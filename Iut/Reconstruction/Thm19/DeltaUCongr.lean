/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.DeltaUEquiv
import Iut.Reconstruction.Thm19.CycloIso

/-!
# `π₁ᵉᵗ(U_{k̄}) ≃ π₁ᵉᵗ(U'_{k̄})` from an isomorphism of the Galois models (MR9 item 4 (b-i), Ξ2)

For the functoriality of the synchronizations of [AbsTopIII] Prop 1.4 (ii)
(`Topics in Absolute Anabelian Geometry III.txt` l.1771–1803) along an isomorphism
`Φ : Π_U ≃ₜ* Π_{U'}` over `ψ : G_k ≃ G_{k'}`, the geometric groups must be matched:

* `deltaUCongr`: `Δ_U ≃ₜ* Δ_{U'}` (the restriction of `Φ` to the kernels of `Π_U ↠ G_k`);
* **`deltaBarUCongr`**: `π₁ᵉᵗ(U_{k̄}) ≃ₜ* π₁ᵉᵗ(U'_{k̄})` through `deltaUEquivBar`;
* `piUToPiX_deltaUEquivBar_symm`, **`deltaBarCongr_fill`**: compatible with the fillings
  `π₁ᵉᵗ(U_{k̄}) ↠ π₁ᵉᵗ(X_{k̄})` and `deltaBarCongr` (`Thm19/CycloIso.lean`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω} {D : GaloisData k t}
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'} {D' : GaloisData k' t'}
  [IsGalois (K₀ k t) Ω] [IsGalois (K₀ k' t') Ω'] [CharZero k] [IsAlgClosed Ω] [CharZero k']
  [IsAlgClosed Ω']
  (Φ : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (hψ : ∀ x, piToGk D' (Φ x) = ψ (piToGk D x))

include hψ in
lemma mem_deltaU_iff (x : Pi D) : Φ x ∈ DeltaU D' ↔ x ∈ DeltaU D := by
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψ, MulEquiv.map_eq_one_iff]

/-- **`Δ_U ≃ₜ* Δ_{U'}`**: the restriction of `Φ` to the geometric subgroups. -/
def deltaUCongr : DeltaU D ≃ₜ* DeltaU D' where
  toFun δ := ⟨Φ (δ : Pi D), (mem_deltaU_iff Φ ψ hψ _).2 δ.2⟩
  invFun δ := ⟨Φ.symm (δ : Pi D'), (mem_deltaU_iff Φ ψ hψ _).1 (by
    rw [ContinuousMulEquiv.apply_symm_apply]; exact δ.2)⟩
  left_inv δ := Subtype.ext (Φ.symm_apply_apply (δ : Pi D))
  right_inv δ := Subtype.ext (Φ.apply_symm_apply (δ : Pi D'))
  map_mul' a b := Subtype.ext (map_mul Φ (a : Pi D) b)
  continuous_toFun := (Φ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Φ.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] lemma coe_deltaUCongr (δ : DeltaU D) :
    (deltaUCongr Φ ψ hψ δ : Pi D') = Φ (δ : Pi D) := rfl

end Generic

attribute [local instance] mulOneClass_piX one_piX mul_piX divisionMonoid_piX inv_piX

section Curve

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
/-- **The filling `π₁ᵉᵗ(U_{k̄}) ↠ π₁ᵉᵗ(X_{k̄})` in the Galois model**: it is `Π_U ↠ Π_X` on
`Δ_U` (`deltaUEquivBar`, `deltaXEquivBar`). -/
theorem deltaXEquivBar_fill (γ : DeltaBar k hτ (chartBar k τ)) :
    (deltaXEquivBar hτ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) : PiX (curveGaloisData k hτ)) =
      piUToPiX (curveGaloisData k hτ)
        ((deltaUEquivBar k hτ).symm γ : Pi (curveGaloisData k hτ)) := by
  obtain ⟨σ, rfl⟩ := (rhoBarU_spec k hτ).2 γ
  rw [deltaUEquivBar_symm_rhoBarU, fundamentalGroupMap_genericL]
  change (deltaXEquivBar hτ (rhoBar hτ σ) : PiX (curveGaloisData k hτ)) = _
  rw [deltaXEquivBar_rhoBar, coe_bcToDeltaX, coe_bcToDeltaU]
  rfl

variable (Φ : Pi (curveGaloisData k hτ) ≃ₜ* Pi (curveGaloisData k' hτ'))
  (hfill : ∀ x, piUToPiX (curveGaloisData k' hτ') (Φ x) = 1 ↔
    piUToPiX (curveGaloisData k hτ) x = 1)
  (ψ : Gk k (FFClosure X) ≃* Gk k' (FFClosure X'))
  (hψ : ∀ x, piToGk (curveGaloisData k' hτ') (Φ x) = ψ (piToGk (curveGaloisData k hτ) x))

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
/-- **`π₁ᵉᵗ(U_{k̄}) ≃ₜ* π₁ᵉᵗ(U'_{k̄})`** induced by `Φ`. -/
def deltaBarUCongr : DeltaBar k hτ (chartBar k τ) ≃ₜ* DeltaBar k' hτ' (chartBar k' τ') :=
  ((deltaUEquivBar k hτ).symm.trans (deltaUCongr Φ ψ hψ)).trans (deltaUEquivBar k' hτ')

lemma deltaUEquivBar_symm_deltaBarUCongr (γ : DeltaBar k hτ (chartBar k τ)) :
    ((deltaUEquivBar k' hτ').symm (deltaBarUCongr Φ ψ hψ γ) : Pi (curveGaloisData k' hτ')) =
      Φ ((deltaUEquivBar k hτ).symm γ : Pi (curveGaloisData k hτ)) := by
  rw [deltaBarUCongr, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_X` are slow for unification
/-- **`deltaBarUCongr` is compatible with the fillings and `deltaBarCongr`.** -/
theorem deltaBarCongr_fill (γ : DeltaBar k hτ (chartBar k τ)) :
    deltaBarCongr Φ hfill ψ hψ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) =
      fundamentalGroupMap ((baseChangeKbar k' X').homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ')
          le_top) (deltaBarUCongr Φ ψ hψ γ) := by
  apply (deltaXEquivBar hτ').injective
  apply Subtype.ext
  rw [deltaXEquivBar_deltaBarCongr, coe_deltaXCongr, deltaXEquivBar_fill, deltaXEquivBar_fill,
    piXCongr_piUToPiX, deltaUEquivBar_symm_deltaBarUCongr]

end Curve

end Iut.Reconstruction.Thm19
