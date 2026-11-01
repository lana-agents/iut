/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CycloBridge
import Iut.Reconstruction.Thm19.ResTransport

/-!
# Cuspidal inertia and residues along isomorphisms of `arithmeticExt` (MR9 item 4, step 1)

[AbsTopIII] Thm 1.9 (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2153–2157) builds
`P_U` from the residues at the cusps (Prop 1.6 (iii), l.2001–2012); for its functoriality the
residues must be carried along isomorphisms `Π_U ≃ Π_{U'}`. An isomorphism `Φ` of the
`arithmeticExt` of two affine hyperbolic curves over number fields carries cuspidal subgroups onto
cuspidal subgroups (`CuspidalExt.Iso.cusps_map`). In the Galois models:

* **`exists_map_inertiaH_bridgeIso`**: for a cusp place `W` (`W ⊇ K`, `τ ∉ W`) there is a cusp place
  `W'` of `U'` with `bridgeIso Φ (I_W ∩ H) = I_{W'} ∩ H'` in `Π_{U'}` (`mem_cusps_iff_piBridge`,
  `isCuspPlace_comap_iff`);
* **`exists_res_h1Congr_bridgeIso`**: for every inertia index `p = (W, σ)` at a cusp place there is
  an inertia index `p'` of `U'` with `res_{p'}(h1Congr η) = χ(res_p η)` for all classes `η`, for any
  `bridgeIso Φ`-equivariant identification `χ` of the cyclotomes (e.g. `cycloIso Φ`).
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp Belyi Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Iso

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

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Cuspidal inertia groups correspond under `bridgeIso Φ`.** -/
theorem exists_map_inertiaH_bridgeIso (W : ValuationSubring (FFClosure C.Xbar))
    (hW : W ∈ CuspW (k := K) (t := coordT τ)) :
    ∃ W' ∈ CuspW (k := K') (t := coordT τ'),
      ((inertiaH (curveGaloisData K hτ) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
            (curveGaloisData K hτ).S))).map
          (bridgeIso hτ hU hτ' hU' Φ).toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K' hτ') W').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K' hτ').H
            (curveGaloisData K' hτ').S)) := by
  have hI := (mem_cusps_iff_piBridge (Ω := Ω) hτ hU _).2
    ⟨W, (isCuspPlace_comap_iff (Ω := Ω) hτ hU W).2 hW, rfl⟩
  obtain ⟨W', hW', hEq⟩ := (mem_cusps_iff_piBridge (Ω := Ω') hτ' hU' _).1 ((Φ.cusps_map _).1 hI)
  refine ⟨W', (isCuspPlace_comap_iff (Ω := Ω') hτ' hU' W').1 hW', ?_⟩
  have hB : (bridgeIso hτ hU hτ' hU' Φ).toMulEquiv.toMonoidHom =
      (piBridge (Ω := Ω') hτ' hU').symm.toMulEquiv.toMonoidHom.comp
        (Φ.pi.toMulEquiv.toMonoidHom.comp (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom) :=
    MonoidHom.ext fun _ => rfl
  have hid : (piBridge (Ω := Ω') hτ' hU').symm.toMulEquiv.toMonoidHom.comp
      (piBridge (Ω := Ω') hτ' hU').toMulEquiv.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun x => (piBridge (Ω := Ω') hτ' hU').symm_apply_apply x
  rw [hB, ← Subgroup.map_map, ← Subgroup.map_map, hEq, Subgroup.map_map, hid, Subgroup.map_id]

lemma evalTriv_congr_elem {P M : Type*} [Group P] [TopologicalSpace P] [CommGroup M]
    [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction P M] {g₁ g₂ : P} (h : g₁ = g₂)
    (h₁ : ∀ m : M, g₁ • m = m) (h₂ : ∀ m : M, g₂ • m = m) (x : ContH1 P M) :
    ContH1.evalTriv g₁ h₁ x = ContH1.evalTriv g₂ h₂ x := by
  subst h
  rfl

set_option maxHeartbeats 800000 in
-- the quotients `Π_U` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_U` on `Ẑ(1)` is found slowly
/-- **Residues along `bridgeIso Φ`**: every residue at a cusp of `U` is, after `χ`, a residue at a
cusp of `U'` of the transported class. -/
theorem exists_res_h1Congr_bridgeIso
    (χ : ZHatOne (F (curveGaloisData K hτ)) (FFClosure C.Xbar) ≃ₜ*
      ZHatOne (F (curveGaloisData K' hτ')) (FFClosure C'.Xbar))
    (hχ : ∀ p z, χ (p • z) = bridgeIso hτ hU hτ' hU' Φ p • χ z)
    (p : InertiaIndex (curveGaloisData K hτ)) (hp : coordT τ ∉ p.1.1) :
    ∃ p' : InertiaIndex (curveGaloisData K' hτ'), coordT τ' ∉ p'.1.1 ∧ ∀ η,
      res (curveGaloisData K' hτ') (h1Congr (bridgeIso hτ hU hτ' hU' Φ) χ hχ η) p' =
        χ (res (curveGaloisData K hτ) η p) := by
  obtain ⟨W', hW', hEq⟩ := exists_map_inertiaH_bridgeIso hτ hU hτ' hU' Φ p.1.1 ⟨p.2.1, hp⟩
  have hmem := Subgroup.mem_map_of_mem (bridgeIso hτ hU hτ' hU' Φ).toMulEquiv.toMonoidHom
    (Subgroup.mem_map_of_mem (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
      (curveGaloisData K hτ).S)) (show p.1.2 ∈ inertiaH (curveGaloisData K hτ) p.1.1 from p.2.2))
  rw [hEq] at hmem
  obtain ⟨σ', hσ', hσ'eq⟩ := hmem
  refine ⟨⟨(W', σ'), hW'.1, hσ'⟩, hW'.2, fun η => ?_⟩
  exact (res_apply _ _ _).trans ((evalTriv_congr_elem hσ'eq
    (pi_inertia_smul_zHatOne hW'.1 hσ' _)
    (smul_eq_self_of_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _)) _).trans
    ((evalTriv_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _) η).trans
      (congrArg χ (res_apply _ η p).symm)))

end Iso

end Iut.Reconstruction.Thm19
