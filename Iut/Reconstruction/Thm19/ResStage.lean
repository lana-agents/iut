/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.LimIso
import Iut.Reconstruction.Thm19.GalInertia
import Iut.Reconstruction.Thm19.InertiaConj
import Iut.Reconstruction.Thm19.ResKer

/-!
# Residues of the stage isomorphisms (MR9 item 4, steps 1 (iii) and 2)

[AbsTopIII] Thm 1.9 (c), (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2178) uses
the residues of Prop 1.6 (iii) (l.2001–2012) at every stage `V_{K₁}`; for the functoriality in
isomorphisms `Π_U ≃ Π_{U'}` they must be carried along the stage isomorphisms `LiftData.S`
(`Thm19/LimIso.lean`). Here:

* `exists_map_inertiaH_bridgeIso_symm`, `IsCor38Lift.exists_map_inertiaH_galLift_symm`: every
  cuspidal inertia group of the target is the image of one of the source (`Φ.symm`);
* **`LiftData.mapsCuspInertia_e`**, **`LiftData.mapsCuspInertia_e_symm`**: the normalised lift
  `e = conj b ∘ galLift φ` and its inverse preserve cuspidal inertia (`GalInertia`,
  `InertiaConj`);
* **`LiftData.exists_res_S`**: every residue at a cusp of the stage `g` is, after the coefficient
  isomorphism, a residue at a cusp of the target stage of the transported class;
* **`LiftData.S_mem_ker_res_iff`**, **`LiftData.S_mem_range_constMapZHat_iff`**: `LiftData.S`
  matches `ker res` and `(K₁^×)^∧` (Prop 1.6 (iii)).
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale PreGaloisCategory
  Belyi Belyi.Anabelian CurvesJacobian.Cusp

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction

open Thm19 Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve AffOrbicurve CurvesJacobian
  CurvesJacobian.Kummer

section Bridge

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K' : Type u} [Field K'] [NumberField K'] {Ω' : Type u} [Field Ω'] [Algebra K' Ω']
  [IsAlgClosed Ω'] [Algebra.IsAlgebraic K' Ω'] [CharZero Ω'] {C' : HypCurve K'}
  [hc' : Fact (C'.U : Set C'.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)
  {τ' : C'.Xbar.functionField} (hτ' : Transcendental K' τ')
  [IsGalois (K₀ K' (coordT τ')) (FFClosure C'.Xbar)] (hU' : C'.U = chartOne K' C'.Xbar τ')
  (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω' C' hc'.out))

lemma bridgeIso_bridgeIso_symm (x : Pi (curveGaloisData K' hτ')) :
    bridgeIso hτ hU hτ' hU' Φ (bridgeIso hτ' hU' hτ hU Φ.symm x) = x := by
  simp [bridgeIso, CuspidalExt.Iso.symm]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Every cuspidal inertia group of `U'` is the image of one of `U`** under `bridgeIso Φ`. -/
theorem exists_map_inertiaH_bridgeIso_symm (W' : ValuationSubring (FFClosure C'.Xbar))
    (hW' : W' ∈ CuspW (k := K') (t := coordT τ')) :
    ∃ W ∈ CuspW (k := K) (t := coordT τ),
      ((inertiaH (curveGaloisData K hτ) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
            (curveGaloisData K hτ).S))).map
          (bridgeIso hτ hU hτ' hU' Φ).toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K' hτ') W').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K' hτ').H
            (curveGaloisData K' hτ').S)) := by
  obtain ⟨W, hW, hEq⟩ := exists_map_inertiaH_bridgeIso hτ' hU' hτ hU Φ.symm W' hW'
  refine ⟨W, hW, ?_⟩
  have hid : (bridgeIso hτ hU hτ' hU' Φ).toMulEquiv.toMonoidHom.comp
      (bridgeIso hτ' hU' hτ hU Φ.symm).toMulEquiv.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => bridgeIso_bridgeIso_symm hτ hU hτ' hU' Φ x
  rw [← hEq, Subgroup.map_map, hid, Subgroup.map_id]

end Bridge

section GalLift

variable {K : Type u} [Field K] [NumberField K] {Ω : Type u} [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]
  {K₂ : Type u} [Field K₂] [NumberField K₂] {Ω₂ : Type u} [Field Ω₂] [Algebra K₂ Ω₂]
  [IsAlgClosed Ω₂] [Algebra.IsAlgebraic K₂ Ω₂] [CharZero Ω₂] {C₂ : HypCurve K₂}
  [hc₂ : Fact (C₂.U : Set C₂.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U algFF isAlgClosure_of_isAlgebraic

variable (Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out))
  {V : C.Xbar.Opens} {hV : V ≤ C.U} {hne : (V : Set C.Xbar).Nonempty}
  [hcV : Fact ((subCurve C V hV hne).U : Set (subCurve C V hV hne).Xbar)ᶜ.Nonempty]
  {V₂ : C₂.Xbar.Opens} {hV₂ : V₂ ≤ C₂.U} {hne₂ : (V₂ : Set C₂.Xbar).Nonempty}
  [hcV₂ : Fact ((subCurve C₂ V₂ hV₂ hne₂).U : Set (subCurve C₂ V₂ hV₂ hne₂).Xbar)ᶜ.Nonempty]
  {τ₀ : C.Xbar.functionField} (hτ₀ : Transcendental K τ₀)
  [IsGalois (K₀ K (coordT τ₀)) (FFClosure C.Xbar)] (hU₀ : V = chartOne K C.Xbar τ₀)
  {υ : C₂.Xbar.functionField} (hυ : Transcendental K₂ υ)
  [IsGalois (K₀ K₂ (coordT υ)) (FFClosure C₂.Xbar)] (hUυ : V₂ = chartOne K₂ C₂.Xbar υ)
  (φ : (arithmeticExt Ω (subCurve C V hV hne) hcV.out).Pi ≃ₜ*
    (arithmeticExt Ω₂ (subCurve C₂ V₂ hV₂ hne₂) hcV₂.out).Pi)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Every cuspidal inertia group of `V₂` is the image under `galLift φ` of one of `V`.** -/
theorem IsCor38Lift.exists_map_inertiaH_galLift_symm
    (h : IsCor38Lift Φ.pi.toMulEquiv hV hne hV₂ hne₂ φ) (W' : ValuationSubring (FFClosure C₂.Xbar))
    (hW' : W' ∈ CuspW (k := K₂) (t := coordT υ)) :
    ∃ W ∈ CuspW (k := K) (t := coordT τ₀),
      ((inertiaH (curveGaloisData K hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ₀).H
            (curveGaloisData K hτ₀).S))).map
          (galLift (Ω := Ω) (Ω₂ := Ω₂) hτ₀ hU₀ hυ hUυ φ).toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K₂ hυ) W').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K₂ hυ).H
            (curveGaloisData K₂ hυ).S)) :=
  exists_map_inertiaH_bridgeIso_symm (C := subCurve C V hV hne) (C' := subCurve C₂ V₂ hV₂ hne₂)
    hτ₀ hU₀ hυ hUυ (h.iso Φ.g Φ.pr_comm) W' hW'

end GalLift

section Stage

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
  {Φ : (arithmeticExt Ω C hc.out).Iso (arithmeticExt Ω₂ C₂ hc₂.out)} {g : GStage K hτ}

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The normalised lift preserves cuspidal inertia** (`galLift φ`: `GalInertia`; conjugation:
`InertiaConj`). -/
theorem LiftData.mapsCuspInertia_e (L : LiftData hτ hU hτ₂ hU₂ Φ g) : MapsCuspInertia ⇑L.e := by
  intro W hW σ hσ
  obtain ⟨W', hW', hEq⟩ := L.hφ.exists_map_inertiaH_galLift Φ g.hτ₀ rfl L.hυ rfl L.φ W hW
  have hx := Subgroup.mem_map_of_mem
    (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).toMulEquiv.toMonoidHom
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K g.hτ₀).H
      (curveGaloisData K g.hτ₀).S)) hσ)
  rw [hEq] at hx
  obtain ⟨σ₁, hσ₁, hσ₁eq⟩ := hx
  obtain ⟨b, hb⟩ := L.hb
  obtain ⟨τb, rfl⟩ := QuotientGroup.mk_surjective b
  have h2 : galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ (σ : Pi (curveGaloisData K g.hτ₀)) =
      (σ₁ : Pi (curveGaloisData K₂ L.hυ)) := hσ₁eq.symm
  refine ⟨transPlace (τb : FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar) W',
    transPlace_mem_CuspW hW' _, τb * σ₁ * τb⁻¹, conj_mem_inertiaH hσ₁ τb, ?_⟩
  refine (hb _).trans ?_
  rw [h2]
  rfl

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **The inverse of the normalised lift preserves cuspidal inertia.** -/
theorem LiftData.mapsCuspInertia_e_symm (L : LiftData hτ hU hτ₂ hU₂ Φ g) :
    MapsCuspInertia ⇑L.e.symm := by
  intro W'' hW'' σ' hσ'
  obtain ⟨b, hb⟩ := L.hb
  obtain ⟨τb, rfl⟩ := QuotientGroup.mk_surjective b
  have hz := hb (L.e.symm (σ' : Pi (curveGaloisData K₂ L.hυ)))
  rw [ContinuousMulEquiv.apply_symm_apply] at hz
  have h1 : galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ
      (L.e.symm (σ' : Pi (curveGaloisData K₂ L.hυ))) =
      ((τb⁻¹ * σ' * τb⁻¹⁻¹ : (curveGaloisData K₂ L.hυ).H) : Pi (curveGaloisData K₂ L.hυ)) := by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, inv_inv]
    conv_rhs => rw [hz]
    group
  have hc := conj_mem_inertiaH hσ' τb⁻¹
  obtain ⟨W, hW, hEq⟩ := L.hφ.exists_map_inertiaH_galLift_symm Φ g.hτ₀ rfl L.hυ rfl L.φ _
    (transPlace_mem_CuspW hW'' _)
  have hm : galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ
      (L.e.symm (σ' : Pi (curveGaloisData K₂ L.hυ))) ∈
      ((inertiaH (curveGaloisData K g.hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K g.hτ₀).H
            (curveGaloisData K g.hτ₀).S))).map
          (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).toMulEquiv.toMonoidHom := by
    rw [hEq, h1]
    exact ⟨_, hc, rfl⟩
  obtain ⟨y, hy, hyeq⟩ := hm
  obtain ⟨σ, hσ, rfl⟩ := hy
  exact ⟨W, hW, σ, hσ, ((galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).injective hyeq).symm⟩

variable (χU : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
    ZHatOne (F (curveGaloisData K₂ hτ₂)) (FFClosure C₂.Xbar))
  (hχU : CycloEquivariant (bridgeIso hτ hU hτ₂ hU₂ Φ) χU)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Residues of the stage isomorphism**: every residue at a cusp of the stage `g` is, after the
coefficient isomorphism, a residue at a cusp of the target stage of the transported class. -/
theorem LiftData.exists_res_S (L : LiftData hτ hU hτ₂ hU₂ Φ g) (p : InertiaIndex g.data)
    (hp : coordT g.τ₀ ∉ p.1.1) :
    ∃ p' : InertiaIndex L.tgt.data, coordT L.υ ∉ p'.1.1 ∧ ∀ x : H1G g,
      res L.tgt.data (L.S χU hχU x) p' =
        constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K (res g.data x p) :=
  exists_res_h1Congr
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
    (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K)
    (mapsCuspInertia_constIso _ _ _ _ g.K L.mapsCuspInertia_e) p hp

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`LiftData.S` matches `ker res`** ([AbsTopIII] Prop 1.6 (iii)). -/
theorem LiftData.S_mem_ker_res_iff (L : LiftData hτ hU hτ₂ hU₂ Φ g) (x : H1G g) :
    L.S χU hχU x ∈ (res L.tgt.data).ker ↔ x ∈ (res g.data).ker :=
  h1Congr_mem_ker_res_iff
    (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀) g.K)
    (constCyclo (gkIso hτ hU hτ₂ hU₂ Φ) (cycloVχ χU g.hτ₀ L.hυ) g.K)
    (constCyclo_smul L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
      (cycloVχ χU g.hτ₀ L.hυ) (cycloVχ_smul χU _ hχU g.hτ₀ L.hυ L.he) g.K)
    g.data_H_le L.tgt.data_H_le
    (mapsCuspInertia_constIso _ _ _ _ g.K L.mapsCuspInertia_e)
    (mapsCuspInertia_constIso_symm _ _ _ _ g.K L.mapsCuspInertia_e_symm) x

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **`LiftData.S` matches `(K₁^×)^∧`** ([AbsTopIII] Prop 1.6 (iii), `ker_res` at both stages). -/
theorem LiftData.S_mem_range_constMapZHat_iff (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (hJ : IsKummerFaithfulJac g.data)
    (hk : ∀ x : F g.data, IsAlgebraic g.K x → x ∈ Set.range (algebraMap g.K (F g.data)))
    (hJ' : IsKummerFaithfulJac L.tgt.data)
    (hk' : ∀ x : F L.tgt.data, IsAlgebraic L.tgt.K x →
      x ∈ Set.range (algebraMap L.tgt.K (F L.tgt.data)))
    (x : H1G g) :
    L.S χU hχU x ∈ (constMapZHat L.tgt.data).range ↔ x ∈ (constMapZHat g.data).range :=
  (SetLike.ext_iff.1 (ker_res hJ' hk') (L.S χU hχU x)).symm.trans
    ((L.S_mem_ker_res_iff χU hχU x).trans (SetLike.ext_iff.1 (ker_res hJ hk) x))

end Stage

end Iut.Reconstruction
