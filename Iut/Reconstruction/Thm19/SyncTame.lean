/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.DeltaUxCongr
import Iut.Reconstruction.Thm19.SyncGroupTheoretic
import Iut.Reconstruction.Thm19.CuspSync

/-!
# Tame generators along isomorphisms of Galois models (MR9 item 4 (b-i))

[AbsTopIII] Thm 1.9 (b), (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2144–2157) read the
tame generators of the cusps through the synchronizations `I_x ≅ M_X` of Prop 1.4 (ii)
(l.1771–1803). The synchronization is group-theoretic (`Thm19/SyncGroupTheoretic.lean`), so it is
carried along the isomorphisms `π₁ᵉᵗ(U_x) ≃ π₁ᵉᵗ(U'_{x'})` induced by `Φ : Π_U ≃ Π_{U'}`
(`Thm19/DeltaUxCongr.lean`); with `syncEquivBar_inertiaToCusp` (`Thm19/CuspSync.lean`) this gives

* `mxHatCongr_mxReindex`;
* **`cycloCongr_tameGen`**: `cycloCongr Φ (θ_p) = θ_{p'}` for matching cusps `p`, `p'`, given the
  matching of the cusps by `Φ` on `H_{k̄}` (hypotheses `hK`, `h₁`, `h₂`, `hp`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

attribute [local instance] mulOneClass_piX one_piX mul_piX divisionMonoid_piX inv_piX

/-! ### Tame generators along `Φ` (Thm 1.9 (b), (c) along isomorphisms) -/

section Tame

open CurvesJacobian.TopClass CurvesJacobian.CuspCentral

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]
  {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]
  [CharZero (FFClosure X)] [CharZero (FFClosure X')]
  [hgf : Fact (0 < (curveGenus k X).toNat)] [hgf' : Fact (0 < (curveGenus k' X').toNat)]
  (Φ : Pi (curveGaloisData k hτ) ≃ₜ* Pi (curveGaloisData k' hτ'))
  (hfill : ∀ x, piUToPiX (curveGaloisData k' hτ') (Φ x) = 1 ↔
    piUToPiX (curveGaloisData k hτ) x = 1)
  (ψ : Gk k (FFClosure X) ≃* Gk k' (FFClosure X'))
  (hψ : ∀ x, piToGk (curveGaloisData k' hτ') (Φ x) = ψ (piToGk (curveGaloisData k hτ) x))

lemma mxHatCongr_mxReindex {G G' : Type*} [Group G] [TopologicalSpace G] [Group G']
    [TopologicalSpace G'] (K₁ K₂ K₁' K₂' : Type*) [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [CharZero K₁] [CharZero K₂] [CharZero K₁'] [CharZero K₂'] (e : G ≃ₜ* G')
    (φ : MXHat G K₁) :
    mxHatCongr K₂ K₂' e (mxReindex K₁ K₂ φ) = mxReindex K₁' K₂' (mxHatCongr K₁ K₁' e φ) :=
  Subtype.ext (funext fun _ => rfl)

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
set_option maxHeartbeats 3200000 in
-- the étale fundamental groups and the modules `M_X`, `Ẑ(1)` unify slowly
/-- **The cyclotome `cycloCongr Φ` carries tame generators to tame generators**
([AbsTopIII] Thm 1.9 (b), Prop 1.4 (ii), T3 l.1771–1803, along `Φ`): for inertia indices
`p = (W₀, σ)`, `p' = (W₀', σ')` over rational points `x`, `x'`, with the data of the
synchronizations at `U_x = X_{k̄} ∖ {x}` and `U'_{x'}`, if `Φ` (through `deltaBarUCongr`) matches
the kernels of the fillings to `U_x`, `U'_{x'}` (`hK`), the inertia elements at `W₀`, `W₀'`
(`h₁`, `h₂`) and `σ` with `σ'` (`hp`), then `cycloCongr Φ (θ_p) = θ_{p'}`. -/
theorem cycloCongr_tameGen
    (p : InertiaIndex (curveGaloisData k hτ)) (x : RatPoint (curveGaloisData k hτ))
    (hpx : ∀ y : F (curveGaloisData k hτ), (y : FFClosure X) ∈ p.1.1 ↔ (y : FFClosure X) ∈ x.A)
    (p' : InertiaIndex (curveGaloisData k' hτ')) (x' : RatPoint (curveGaloisData k' hτ'))
    (hpx' : ∀ y : F (curveGaloisData k' hτ'),
      (y : FFClosure X') ∈ p'.1.1 ↔ (y : FFClosure X') ∈ x'.A)
    {V : (baseChangeKbar k X).Opens} [Nonempty V] (hV : (V : Set (baseChangeKbar k X))ᶜ.Finite)
    (hle : chartBar k τ ≤ V) {xb : baseChangeKbar k X}
    (hUx : (V : Set (baseChangeKbar k X))ᶜ = {xb})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V p.1.1)
    {π : (F (barData k hτ))ˣ}
    (hπW : p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X))
    {V' : (baseChangeKbar k' X').Opens} [Nonempty V']
    (hV' : (V' : Set (baseChangeKbar k' X'))ᶜ.Finite) (hle' : chartBar k' τ' ≤ V')
    {xb' : baseChangeKbar k' X'} (hUx' : (V' : Set (baseChangeKbar k' X'))ᶜ = {xb'})
    (hW₀' : IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') ⊤ p'.1.1)
    (hW₀U' : ¬ IsCentredOn (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V' p'.1.1)
    {π' : (F (barData k' hτ'))ˣ}
    (hπW' : p'.1.1.valuation ((π' : F (barData k' hτ')) : FFClosure X') < 1)
    (hπ' : ∀ f ∈ F (barData k' hτ'), p'.1.1.valuation f < 1 →
      p'.1.1.valuation f ≤ p'.1.1.valuation ((π' : F (barData k' hτ')) : FFClosure X'))
    (hK : ∀ (σ : (barData k hτ).H) (σ' : (barData k' hτ').H),
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ' →
        (σ' ∈ GaloisPi1.kernel (barData k' hτ').H
            (SU (barData k' hτ') (baseChangeKbar k' X') (barEquivL k' hτ') V') ↔
          σ ∈ GaloisPi1.kernel (barData k hτ).H
            (SU (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) V)))
    (h₁ : ∀ σ ∈ inertiaH (barData k hτ) p.1.1, ∃ σ' ∈ inertiaH (barData k' hτ') p'.1.1,
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ')
    (h₂ : ∀ σ' ∈ inertiaH (barData k' hτ') p'.1.1, ∃ σ ∈ inertiaH (barData k hτ) p.1.1,
      deltaBarUCongr Φ ψ hψ (rhoBarU k hτ σ) = rhoBarU k' hτ' σ')
    (hp : deltaBarUCongr Φ ψ hψ (rhoBarU k hτ (inertiaBar p : (barData k hτ).H)) =
      rhoBarU k' hτ' (inertiaBar p' : (barData k' hτ').H)) :
    cycloCongr Φ hfill ψ hψ (tameGen p) = tameGen p' := by
  have hg := hgf.out
  have hg' := hgf'.out
  set Ξ := deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK
  have hI := map_cuspInertia_deltaBarUxCongr Φ ψ hψ hV hle hV' hle' hK p.1.1 p'.1.1 h₁ h₂
  set σ := inertiaToCusp (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) V p.1.1
    (inertiaBar p)
  have hΞσ : Ξ (σ : DeltaBar k hτ V) =
      (inertiaToCusp (barData k' hτ') (barEquivL k' hτ') (barData_H_le k' hτ') V' p'.1.1
        (inertiaBar p') : DeltaBar k' hτ' V') :=
    deltaBarUxCongr_chartHom Φ ψ hψ hV hle hV' hle' hK _ _ hp
  have hσ : Ξ (σ : DeltaBar k hτ V) ∈ cuspInertia (barData k' hτ') (baseChangeKbar k' X')
      (barEquivL k' hτ') (barData_H_le k' hτ') V' p'.1.1 := by
    rw [hΞσ]
    exact SetLike.coe_mem _
  have T := mxHatCongr_syncEquivBar hg hUx hW₀ hW₀U hπW hπ hg' hUx' hW₀' hW₀U' hπW' hπ' Ξ
    (deltaBarCongr Φ hfill ψ hψ) (deltaBarCongr_fillTop Φ hfill ψ hψ hV hle hV' hle' hK) hI σ hσ
  have hσ' : (⟨_, hσ⟩ : cuspInertia (barData k' hτ') (baseChangeKbar k' X')
      (barEquivL k' hτ') (barData_H_le k' hτ') V' p'.1.1) =
      inertiaToCusp (barData k' hτ') (barEquivL k' hτ') (barData_H_le k' hτ') V' p'.1.1
        (inertiaBar p') := Subtype.ext hΞσ
  rw [hσ'] at T
  have A := syncEquivBar_inertiaToCusp hg p x hpx hUx hW₀ hW₀U hπW hπ
  have A' := syncEquivBar_inertiaToCusp hg' p' x' hpx' hUx' hW₀' hW₀U' hπW' hπ'
  have key : MX.equiv hτ' (F (curveGaloisData k' hτ'))
      (mxCongr Φ hfill ψ hψ (F (curveGaloisData k hτ)) (F (curveGaloisData k' hτ'))
        ((natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm (tameGen p))) =
      MX.equiv hτ' (F (curveGaloisData k' hτ'))
        ((natIsoHatK hτ' (F (curveGaloisData k' hτ')) hg').symm (tameGen p')) :=
    calc _ = mxHatCongr (F (curveGaloisData k hτ)) (F (curveGaloisData k' hτ'))
          (deltaBarCongr Φ hfill ψ hψ) (MX.equiv hτ (F (curveGaloisData k hτ))
            ((natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm (tameGen p))) :=
          ContinuousMulEquiv.apply_symm_apply _ _
      _ = mxHatCongr (F (curveGaloisData k hτ)) (F (curveGaloisData k' hτ'))
          (deltaBarCongr Φ hfill ψ hψ) (mxReindex _ _ (syncEquivBar hg hUx hW₀ hW₀U hπW hπ σ)) :=
          congrArg _ A.symm
      _ = mxReindex _ _ (mxHatCongr (F (barData k hτ)) (F (barData k' hτ'))
          (deltaBarCongr Φ hfill ψ hψ) (syncEquivBar hg hUx hW₀ hW₀U hπW hπ σ)) :=
          mxHatCongr_mxReindex _ _ _ _ _ _
      _ = _ := (congrArg _ T).trans A'
  calc cycloCongr Φ hfill ψ hψ (tameGen p) =
        natIsoHatK hτ' (F (curveGaloisData k' hτ')) hg'
          (mxCongr Φ hfill ψ hψ (F (curveGaloisData k hτ)) (F (curveGaloisData k' hτ'))
            ((natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm (tameGen p))) := rfl
    _ = natIsoHatK hτ' (F (curveGaloisData k' hτ')) hg'
          ((natIsoHatK hτ' (F (curveGaloisData k' hτ')) hg').symm (tameGen p')) :=
        congrArg _ ((MX.equiv hτ' (F (curveGaloisData k' hτ'))).injective key)
    _ = tameGen p' := ContinuousMulEquiv.apply_symm_apply _ _

end Tame

end Iut.Reconstruction.Thm19
