/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.DeltaUCongr

/-!
# `π₁ᵉᵗ(U_x) ≃ π₁ᵉᵗ(U'_{x'})` from an isomorphism of the Galois models (MR9 item 4 (b-i), Ξ2)

The synchronization of [AbsTopIII] Prop 1.4 (ii) (`Topics in Absolute Anabelian Geometry III.txt`
l.1771–1803) lives on `Δ_{U_x}`, `U_x = X_{k̄} ∖ {x}` for a cusp `x`. An isomorphism
`Φ : Π_U ≃ₜ* Π_{U'}` gives `π₁ᵉᵗ(U_{k̄}) ≃ₜ* π₁ᵉᵗ(U'_{k̄})` (`deltaBarUCongr`); it descends to
`π₁ᵉᵗ(U_x) ≃ₜ* π₁ᵉᵗ(U'_{x'})` once it matches the kernels of the fillings
`π₁ᵉᵗ(U_{k̄}) ↠ π₁ᵉᵗ(U_x)`, i.e. the inertia at the cusps other than `x`. The kernel condition is
taken in the Galois form `hK` (on `H_{k̄}`, kernels `⟨⟨S_{U_x}⟩⟩`, curves-jacobian
`genericL_spec`):

* `fillUx`, `fillUx_rhoBarU`, `fillUx_surjective`, `fillUx_rhoBarU_eq_one_iff`;
* **`deltaBarUxCongr`** (`descendCongr`), `deltaBarUxCongr_fillUx`;
* **`deltaBarCongr_fillTop`**: compatible with the fillings to `π₁ᵉᵗ(X_{k̄})` and
  `deltaBarCongr`;
* **`deltaBarUxCongr_chartHom`**, **`map_cuspInertia_deltaBarUxCongr`**: matching inertia
  elements on `H_{k̄}` give matching elements and cuspidal inertia groups of `π₁ᵉᵗ(U_x)`.

These are the hypotheses `hfill`, `hI`, `hσ` of `mxHatCongr_syncEquivBar`
(`Thm19/SyncGroupTheoretic.lean`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

attribute [local instance] mulOneClass_piX one_piX mul_piX divisionMonoid_piX inv_piX

section Fill

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} (hτ : Transcendental k τ)
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {V : (baseChangeKbar k X).Opens} [Nonempty V] (hV : (V : Set (baseChangeKbar k X))ᶜ.Finite)
  (hle : chartBar k τ ≤ V)

/-- The filling `π₁ᵉᵗ(U_{k̄}) ↠ π₁ᵉᵗ(V)` for an open `V ⊇ U_{k̄}`. -/
abbrev fillUx : DeltaBar k hτ (chartBar k τ) →ₜ* DeltaBar k hτ V :=
  fundamentalGroupMap ((baseChangeKbar k X).homOfLE hle)
    (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) hle)

lemma fillUx_rhoBarU (σ : (barData k hτ).H) :
    fillUx k hτ hle (rhoBarU k hτ σ) =
      (barData k hτ).chartHom (barData_H_le k hτ)
        (genericL (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V) σ :=
  fundamentalGroupMap_genericL (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barData_H_le k hτ) hle σ

include hV in
lemma fillUx_surjective : Function.Surjective (fillUx k hτ hle) := by
  intro γ
  obtain ⟨σ, rfl⟩ := (genericL_spec (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barEquivL_algebraMap k hτ) (barData_H_le k hτ) (barEquivL_tau k hτ) V hV).2 γ
  exact ⟨rhoBarU k hτ σ, fillUx_rhoBarU k hτ hle σ⟩

include hV in
lemma fillUx_rhoBarU_eq_one_iff (σ : (barData k hτ).H) :
    fillUx k hτ hle (rhoBarU k hτ σ) = 1 ↔
      σ ∈ GaloisPi1.kernel (barData k hτ).H
        (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V) := by
  rw [fillUx_rhoBarU, ← MonoidHom.mem_ker, (genericL_spec (barData k hτ) (baseChangeKbar k X)
    (barEquivL k hτ) (barEquivL_algebraMap k hτ) (barData_H_le k hτ) (barEquivL_tau k hτ) V hV).1]

end Fill

section Congr

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]
  (Φ : Pi (curveGaloisData k hτ) ≃ₜ* Pi (curveGaloisData k' hτ'))
  (hfill : ∀ x, piUToPiX (curveGaloisData k' hτ') (Φ x) = 1 ↔
    piUToPiX (curveGaloisData k hτ) x = 1)
  (ψ : Gk k (FFClosure X) ≃* Gk k' (FFClosure X'))
  (hψ : ∀ x, piToGk (curveGaloisData k' hτ') (Φ x) = ψ (piToGk (curveGaloisData k hτ) x))
  {V : (baseChangeKbar k X).Opens} [Nonempty V] (hV : (V : Set (baseChangeKbar k X))ᶜ.Finite)
  (hle : chartBar k τ ≤ V)
  {V' : (baseChangeKbar k' X').Opens} [Nonempty V']
  (hV' : (V' : Set (baseChangeKbar k' X'))ᶜ.Finite) (hle' : chartBar k' τ' ≤ V')
  (hK : ∀ (σ : (barData k hτ).H) (σ' : (barData k' hτ').H),
    deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' →
      (σ' ∈ GaloisPi1.kernel (barData k' hτ').H
          (SU (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V') ↔
        σ ∈ GaloisPi1.kernel (barData k hτ).H
          (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V)))

include hV hV' hK in
lemma fillUx_deltaBarUCongr_eq_one_iff (a : DeltaBar k hτ (chartBar k τ)) :
    fillUx k' hτ' hle' (deltaBarUCongr Φ ψ hψ a) = 1 ↔ fillUx k hτ hle a = 1 := by
  obtain ⟨σ, rfl⟩ := (rhoBarU_spec k hτ).2 a
  obtain ⟨σ', hσ'⟩ := (rhoBarU_spec k' hτ').2 (deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ))
  rw [← hσ', fillUx_rhoBarU_eq_one_iff k' hτ' hV' hle', fillUx_rhoBarU_eq_one_iff k hτ hV hle]
  exact hK σ σ' hσ'.symm

/-- **`π₁ᵉᵗ(V) ≃ₜ* π₁ᵉᵗ(V')`** (e.g. `V = U_x`): `deltaBarUCongr` descended along the fillings. -/
def deltaBarUxCongr : DeltaBar k hτ V ≃ₜ* DeltaBar k' hτ' V' :=
  descendCongr (fillUx k hτ hle).toMonoidHom (fillUx k' hτ' hle').toMonoidHom
    (fillUx k hτ hle).continuous (fillUx k' hτ' hle').continuous (fillUx_surjective k hτ hV hle)
    (fillUx_surjective k' hτ' hV' hle') (deltaBarUCongr Φ ψ hψ)
    (fillUx_deltaBarUCongr_eq_one_iff Φ ψ hψ hV hle hV' hle' hK)

lemma deltaBarUxCongr_fillUx (a : DeltaBar k hτ (chartBar k τ)) :
    deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK (fillUx k hτ hle a) =
      fillUx k' hτ' hle' (deltaBarUCongr Φ ψ hψ a) :=
  descendCongr_apply _ _ _ _ _ _ _ _ a

lemma fillTop_fillUx (a : DeltaBar k hτ (chartBar k τ)) :
    fundamentalGroupMap ((baseChangeKbar k X).homOfLE (le_top : V ≤ ⊤))
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
        (fillUx k hτ hle a) =
      fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
        a := by
  obtain ⟨σ, rfl⟩ := (rhoBarU_spec k hτ).2 a
  rw [fillUx_rhoBarU, fundamentalGroupMap_genericL, rhoBarU, fundamentalGroupMap_genericL]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
set_option maxHeartbeats 1600000 in
-- the quotients `Π_U`, `Π_X` are slow for unification
/-- **The descended isomorphism is compatible with the fillings to `π₁ᵉᵗ(X_{k̄})` and
`deltaBarCongr`** (the hypothesis `hfill` of `mxHatCongr_syncEquivBar`). -/
theorem deltaBarCongr_fillTop (γ : DeltaBar k hτ V) :
    deltaBarCongr Φ hfill ψ hψ (fundamentalGroupMap ((baseChangeKbar k X).homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) le_top)
          γ) =
      fundamentalGroupMap ((baseChangeKbar k' X').homOfLE le_top)
        (specPoint_genericL_homOfLE (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ')
          le_top) (deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK γ) := by
  obtain ⟨a, rfl⟩ := fillUx_surjective k hτ hV hle γ
  rw [deltaBarUxCongr_fillUx, fillTop_fillUx, fillTop_fillUx, deltaBarCongr_fill]

/-- **Matching elements of `H_{k̄}` have matching images in `π₁ᵉᵗ(V)`.** -/
lemma deltaBarUxCongr_chartHom (σ : (barData k hτ).H) (σ' : (barData k' hτ').H)
    (h : deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ') :
    deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK
        ((barData k hτ).chartHom (barData_H_le k hτ)
          (genericL (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V) σ) =
      (barData k' hτ').chartHom (barData_H_le k' hτ')
        (genericL (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V') σ' := by
  rw [← fillUx_rhoBarU k hτ hle, deltaBarUxCongr_fillUx, h, fillUx_rhoBarU]

set_option maxHeartbeats 800000 in
-- the étale fundamental groups unify slowly
/-- **Cuspidal inertia groups along the descended isomorphism**: if `deltaBarUCongr` matches the
inertia elements of `W₀` and `W₀'` on `H_{k̄}` (both ways), the cuspidal inertia groups of `V`
at `W₀` and of `V'` at `W₀'` correspond (the hypothesis `hI` of `mxHatCongr_syncEquivBar`). -/
theorem map_cuspInertia_deltaBarUxCongr (W₀ : ValuationSubring (FFClosure X))
    (W₀' : ValuationSubring (FFClosure X'))
    (h₁ : ∀ σ ∈ inertiaH (barData k hτ) W₀, ∃ σ' ∈ inertiaH (barData k' hτ') W₀',
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ')
    (h₂ : ∀ σ' ∈ inertiaH (barData k' hτ') W₀', ∃ σ ∈ inertiaH (barData k hτ) W₀,
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ') :
    (cuspInertia (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) (barData_H_le k hτ) V
        W₀).map (deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK).toMulEquiv.toMonoidHom =
      cuspInertia (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ')
        (barData_H_le k' hτ') V' W₀' := by
  rw [CuspCentral.cuspInertia_eq_map (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) V W₀,
    CuspCentral.cuspInertia_eq_map (barData k' hτ') (barEquivL k' hτ') (barData_H_le k' hτ') V'
      W₀',
    Subgroup.map_map]
  ext y
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨σ', hσ', h⟩ := h₁ σ hσ
    exact ⟨σ', hσ', (deltaBarUxCongr_chartHom Φ ψ hψ hV hle hV' hle' hK σ σ' h).symm⟩
  · rintro ⟨σ', hσ', rfl⟩
    obtain ⟨σ, hσ, h⟩ := h₂ σ' hσ'
    refine ⟨σ, hσ, ?_⟩
    rw [MonoidHom.comp_apply]
    exact deltaBarUxCongr_chartHom Φ ψ hψ hV hle hV' hle' hK σ σ' h

end Congr

end Iut.Reconstruction.Thm19
