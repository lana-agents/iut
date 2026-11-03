/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ValCompat
import Iut.Reconstruction.Thm19.UCompat

/-!
# [AbsTopIII] Thm 1.9: functoriality along `Φ` (MR9 item 4, step 5)

[AbsTopIII] Thm 1.9 (`Topics in Absolute Anabelian Geometry III.txt` l.2109–2199) reconstructs the
NF-portion of the function field functorially in the isomorphisms of the fundamental groups. For
an isomorphism `Φ : Π_U ≅ Π_{U'}` of the arithmetic fundamental groups of two hyperbolic curves
over number fields, the isomorphism `h1LimCycloEquiv` of the colimits `lim→_V H¹(Π_V, Ẑ(1))`
restricts to `φ : K^×_{Z_NF} ≅ K'^×_{Z'_NF}` on the Kummer classes (`kummerNFRangeEquiv`), and:

* `Uchida.ValEvalData.Iso.mem_U_iff_of_forward` (generic): `φ` respects `U_x` for partners if it
  and `φ⁻¹` map `U_x` into `U_{x'}`;
* **`mem_U_kummerNFRangeEquiv`**, **`mem_U_kummerNFRangeEquiv_symm`**: `φ` and `φ⁻¹` map `U_x`
  into `U_{x'}` for points with the same valuations (`mem_U_of_matched`);
* **`recTripleIso`**: `recTriple N ≅ recTriple N₂` (`Iso.ofVal`, `φ` with the partners of
  `exists_val_kummerNFRangeEquiv(_symm)`), with `recTripleIso_φ`;
* **`nfRingEquiv`**: the field isomorphism `K_{Z_NF} ≃+* K_{Z'_NF}` (`ringEquivOfIso`), and
  **`kummerNF_nfRingEquiv`**: on the Kummer classes it is `h1LimCycloEquiv`
  (generic: `recEquiv_coe`, `kummerNF_ringEquivOfIso`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction

namespace Uchida.ValEvalData.Iso

variable {D D' : ValEvalData.{u}}

/-- **`U_x` for partners from the two inclusions**: if `φ` maps `U_x` into `U_{x'}` and `φ⁻¹` maps
`U_{x'}` into `U_x` whenever `x, x'` have the same valuations along `φ`, then `φ` respects `U_x`
for partners (the hypothesis `hU` of `Iso.ofVal`). -/
theorem mem_U_iff_of_forward (φ : D.G ≃* D'.G)
    (hfwd : ∀ (x : D.P) (x' : D'.P), (∀ f, D'.val x' (φ f) = D.val x f) →
      ∀ f, f ∈ D.U x → φ f ∈ D'.U x')
    (hbwd : ∀ (x' : D'.P) (x : D.P), (∀ f', D.val x (φ.symm f') = D'.val x' f') →
      ∀ f', f' ∈ D'.U x' → φ.symm f' ∈ D.U x)
    (x : D.P) (x' : D'.P) (h : ∀ f, D'.val x' (φ f) = D.val x f) (f : D.G) :
    φ f ∈ D'.U x' ↔ f ∈ D.U x := by
  refine ⟨fun hf => ?_, hfwd x x' h f⟩
  have h' := hbwd x' x (fun f' => by
    obtain ⟨f₀, rfl⟩ := φ.surjective f'
    rw [MulEquiv.symm_apply_apply, h]) (φ f) hf
  rwa [MulEquiv.symm_apply_apply] at h'

end Uchida.ValEvalData.Iso

namespace Thm19

section Functorial

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : Pi1.Orbifold.GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  [CharZero Ω'] [Fact (D'.H ≤ D'.HL)] [NumberField k'] (N' : NFModel D')
  (hkF' : ∀ x : F D', IsAlgebraic k' x → x ∈ Set.range (algebraMap k' (F D')))

open Classical in
/-- A nonzero NF-rational function goes to its Kummer class in `kummerNFRange ∪ {0}`. -/
lemma recEquiv_coe (f : (fnf N)ˣ) :
    recEquiv N hkF (f : fnf N) =
      WithZero.coe (α := (recTriple N hkF).G) (kummerNFEquiv N hkF f) := by
  rw [recEquiv_apply, WithZero.withZeroUnitsEquiv_symm_apply_coe,
    Uchida.ValEvalData.Iso.mapZ_coe]
  rfl

/-- **The field isomorphism of an isomorphism of triples is the given isomorphism on the Kummer
classes.** -/
theorem kummerNF_ringEquivOfIso (e : (recTriple N hkF).Iso (recTriple N' hkF'))
    (f : (fnf N)ˣ) :
    kummerNF N' hkF' (Units.map (ringEquivOfIso N hkF N' hkF' e).toMonoidHom f) =
      (e.φ (kummerNFEquiv N hkF f)).1 := by
  have h1 : recEquiv N' hkF' (ringEquivOfIso N hkF N' hkF' e (f : fnf N)) =
      WithZero.coe (α := (recTriple N' hkF').G) (e.φ (kummerNFEquiv N hkF f)) := by
    change recEquiv N' hkF' ((recEquiv N' hkF').symm (e.mapZ (recEquiv N hkF (f : fnf N)))) = _
    rw [Equiv.apply_symm_apply, recEquiv_coe, Uchida.ValEvalData.Iso.mapZ_coe]
  have h2 := recEquiv_coe N' hkF' (Units.map (ringEquivOfIso N hkF N' hkF' e).toMonoidHom f)
  rw [Units.coe_map] at h2
  have h3 := WithZero.coe_injective (h2.symm.trans h1)
  rw [← coe_kummerNFEquiv]
  exact congrArg Subtype.val h3

end Functorial

end Thm19

open Thm19

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

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at several stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **`φ` maps `U_x` into `U_{x'}`** for points `x, x'` with the same valuations along `φ`
(`exists_ratCusp_nfPlace`, the matched cusp, `val_eq_of_matched` to identify `x'`,
`mem_U_of_matched`). -/
theorem mem_U_kummerNFRangeEquiv
    (P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N))
    (P₂ : Place (algebraicClosure ℚ (FFClosure C₂.Xbar)) (fnf N₂))
    (h : ∀ ξ : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G,
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val P₂
        (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ) =
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val P ξ)
    (ξ : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G)
    (hξ : ξ ∈ (recTriple N (mem_range_of_isAlgebraic_F K hτ)).U P) :
    kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ ∈
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).U P₂ := by
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
  have hval : ∀ ξ' : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G,
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk'' hW''N)
        (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ') =
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk hW) ξ' := fun ξ' =>
    val_eq_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ)
      (cycloIso_smul hτ hU hτ₂ hU₂ Φ) σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N N₂ hS
      (fun _ L => L.tameCompat_cycloIso)
      (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).toMonoidHom
      (fun g y => h1LimCycloEquiv_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g y) L₀ x hx hk hW
      W'' hW'' hI hk'' hW''N ξ'
      (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ').2
  have hP₂ : P₂ = nfPlace hk'' hW''N :=
    recTriple_valInjective N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂) _ _ fun ξ₂ => by
      obtain ⟨ξ', rfl⟩ :=
        (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).surjective
          ξ₂
      rw [h, hval]
  subst hP₂
  exact mem_U_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ)
    (cycloIso_smul hτ hU hτ₂ hU₂ Φ) σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC N N₂ hS
    (fun _ L => L.tameCompat_cycloIso)
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).toMonoidHom
    (fun g y => h1LimCycloEquiv_ofG hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ g y) L₀ x hx hk hW
    W'' hW'' hI hk'' hW''N ξ
    (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ).2 hξ

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` and the classes at several stages unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` and their actions are found slowly
/-- **`φ⁻¹` maps `U_{x'}` into `U_x`** for points with the same valuations along `φ⁻¹` (lift data
of `Φ.symm`, `(cycloIso Φ).symm`, `tameBridge_cycloIso_symm`). -/
theorem mem_U_kummerNFRangeEquiv_symm
    (P₂ : Place (algebraicClosure ℚ (FFClosure C₂.Xbar)) (fnf N₂))
    (P : Place (algebraicClosure ℚ (FFClosure C.Xbar)) (fnf N))
    (h : ∀ ξ₂ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G,
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val P
        ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
          N₂).symm ξ₂) =
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val P₂ ξ₂)
    (ξ₂ : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G)
    (hξ₂ : ξ₂ ∈ (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).U P₂) :
    (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm ξ₂ ∈
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).U P := by
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
  have hmem : ∀ ξ' : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G,
      (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm ξ'.1 ∈
        kummerNFRange N (mem_range_of_isAlgebraic_F K hτ) := fun ξ' =>
    coe_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ' ▸
      ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm ξ').2
  have hsub : ∀ ξ' : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G,
      (⟨(h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm ξ'.1,
        hmem ξ'⟩ : (recTriple N (mem_range_of_isAlgebraic_F K hτ)).G) =
      (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).symm ξ' :=
    fun ξ' => Subtype.ext
      (coe_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ ξ').symm
  have hval : ∀ ξ' : (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).G,
      (recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk'' hW''N)
        ((kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
          N₂).symm ξ') =
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)).val (nfPlace hk hW) ξ' := fun ξ' =>
    (congrArg ((recTriple N (mem_range_of_isAlgebraic_F K hτ)).val (nfPlace hk'' hW''N))
      (hsub ξ')).symm.trans
      (val_eq_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ).symm
        (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁ N₂ N hS₂
        (fun _ L => L.tameCompat_of_tameBridge _ (tameBridge_cycloIso_symm hτ hU hτ₂ hU₂ Φ))
        (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm.toMonoidHom
        (fun g y => h1LimEquiv_symm_ofG (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ)
          hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y) L₀ x hx hk hW W'' hW'' hI hk'' hW''N ξ'
        (hmem ξ'))
  have hP : P = nfPlace hk'' hW''N :=
    recTriple_valInjective N (mem_range_of_isAlgebraic_F K hτ) _ _ fun ξ => by
      obtain ⟨ξ', rfl⟩ :=
        (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
          N₂).symm.surjective ξ
      rw [h, hval]
  subst hP
  exact hsub ξ₂ ▸ mem_U_of_matched (cycloIso hτ hU hτ₂ hU₂ Φ).symm
    (symm_smul_of_smul _ (cycloIso_smul hτ hU hτ₂ hU₂ Φ)) σ₂ hσ₂ hg₂ σ₀ hσ₀ hg hDGC₁ N₂ N hS₂
    (fun _ L => L.tameCompat_of_tameBridge _ (tameBridge_cycloIso_symm hτ hU hτ₂ hU₂ Φ))
    (h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁).symm.toMonoidHom
    (fun g y => h1LimEquiv_symm_ofG (cycloIso hτ hU hτ₂ hU₂ Φ) (cycloIso_smul hτ hU hτ₂ hU₂ Φ)
      hS σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hS₂ hDGC hDGC₁ g y) L₀ x hx hk hW W'' hW'' hI hk'' hW''N ξ₂
    (hmem ξ₂) hξ₂

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **[AbsTopIII] Thm 1.9, functoriality: the isomorphism of the reconstructed triples**
`recTriple N ≅ recTriple N₂` induced by `Φ`: the Kummer classes correspond by `h1LimCycloEquiv`
(`kummerNFRangeEquiv`), the points by equality of the valuations (`Iso.ofVal`), and `ord_x`, `U_x`
are respected (`exists_val_kummerNFRangeEquiv(_symm)`, `mem_U_kummerNFRangeEquiv(_symm)`). -/
def recTripleIso :
    (recTriple N (mem_range_of_isAlgebraic_F K hτ)).Iso
      (recTriple N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)) :=
  Uchida.ValEvalData.Iso.ofVal
    (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂)
    (recTriple_valInjective N (mem_range_of_isAlgebraic_F K hτ))
    (recTriple_valInjective N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂))
    (exists_val_kummerNFRangeEquiv hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂)
    (fun P₂ => (exists_val_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂
      P₂).elim fun P hP => ⟨P, fun ξ => by
        have e := hP (kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁
          N N₂ ξ)
        rw [MulEquiv.symm_apply_apply] at e
        exact e.symm⟩)
    (Uchida.ValEvalData.Iso.mem_U_iff_of_forward _
      (mem_U_kummerNFRangeEquiv hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂)
      (mem_U_kummerNFRangeEquiv_symm hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂))

lemma recTripleIso_φ :
    (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂).φ =
      kummerNFRangeEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ := rfl

variable (hτ hU hτ₂ hU₂ Φ) in
/-- **[AbsTopIII] Thm 1.9, functoriality: the field isomorphism** `K_{Z_NF} ≃+* K_{Z'_NF}` of the
NF-portions induced by `Φ` (`ringEquivOfIso` of `recTripleIso`). -/
def nfRingEquiv : fnf N ≃+* fnf N₂ :=
  ringEquivOfIso N (mem_range_of_isAlgebraic_F K hτ) N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)
    (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂)

set_option maxHeartbeats 800000 in
-- the triples and the colimits unify slowly
/-- **The field isomorphism is `Φ` on the Kummer classes**: `κ(ψ(f)) = h1LimCycloEquiv (κ(f))` in
`lim→_V H¹(Π_V, Ẑ(1))`. -/
theorem kummerNF_nfRingEquiv (f : (fnf N)ˣ) :
    kummerNF N₂ (mem_range_of_isAlgebraic_F K₂ hτ₂)
        (Units.map (nfRingEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N
          N₂).toMonoidHom f) =
      h1LimCycloEquiv hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁
        (kummerNF N (mem_range_of_isAlgebraic_F K hτ) f) := by
  have e1 := kummerNF_ringEquivOfIso N (mem_range_of_isAlgebraic_F K hτ) N₂
    (mem_range_of_isAlgebraic_F K₂ hτ₂)
    (recTripleIso hτ hU hτ₂ hU₂ Φ hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂) f
  rw [recTripleIso_φ] at e1
  exact e1.trans ((coe_kummerNFRangeEquiv hS hS₂ σ₀ hσ₀ hg σ₂ hσ₂ hg₂ hDGC hDGC₁ N N₂ _).trans
    (congrArg _ (coe_kummerNFEquiv N (mem_range_of_isAlgebraic_F K hτ) f)))

end Lift

end Iut.Reconstruction
