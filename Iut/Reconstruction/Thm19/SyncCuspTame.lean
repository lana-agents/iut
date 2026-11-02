/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.SyncCusp
import Iut.Reconstruction.Thm19.Unramified

/-!
# Tame generators along `Φ` from the matching of the cusps (MR9 item 4 (b-i))

[AbsTopIII] Thm 1.9 (b) (`Topics in Absolute Anabelian Geometry III.txt` l.2144–2152) reads the
tame generators of the cusps through the synchronizations of Prop 1.4 (ii) (l.1771–1803). Here
`cycloCongr_tameGen` (`Thm19/SyncTame.lean`) is freed from rational points (the extension of the
field of constants is unramified everywhere, `Thm19/Unramified.lean`) and from the hypotheses on
`H_{k̄}` (`Thm19/SyncCusp.lean`):

* `syncEquivBar_inertiaToCusp'`, `cycloCongr_tameGen'`: at every cusp, rational or not;
* `exists_syncData'`: the synchronization data at a cusp, with `U_{k̄} ⊆ U_x`;
* `coe_bcToDeltaU_inertiaBar`;
* **`cycloCongr_tameGen_of_cusps`**: if `Φ` carries cuspidal inertia groups of `Π_U` onto
  cuspidal inertia groups (both ways) and the cusps are separated by inertia on both sides
  (`CuspSep`), then `cycloCongr Φ (θ_p) = θ_{p'}` for cusps `p`, `p'` with `Φ(I_p) = I_{p'}` and
  `Φ[σ_p] = [σ_{p'}]`.
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

attribute [local instance] mulOneClass_piX one_piX mul_piX divisionMonoid_piX inv_piX

section Sync

open CurvesJacobian.TopClass CurvesJacobian.CuspCentral

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] CurvesJacobian.isFunctionField_F

set_option maxHeartbeats 800000 in
-- unfolding `syncEquivBar` to `natIsoHatBar` is slow
/-- **[AbsTopIII] Thm 1.9 (b) at any cusp** (`syncEquivBar_inertiaToCusp` without a rational
point below `p`). -/
theorem syncEquivBar_inertiaToCusp' (hg : 0 < (curveGenus k X).toNat)
    (p : InertiaIndex (curveGaloisData k hτ)) (hne : idxVal p ≠ ⊤)
    {U : (baseChangeKbar k X).Opens} [Nonempty U] {x' : baseChangeKbar k X}
    (hUx : (U : Set (baseChangeKbar k X))ᶜ = {x'})
    (hW₀ : IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1)
    (hW₀U : ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U p.1.1)
    {π : (F (barData k hτ))ˣ}
    (hπW : p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1)
    (hπ : ∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
      p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X)) :
    mxReindex _ _ (syncEquivBar hg hUx hW₀ hW₀U hπW hπ
        (inertiaToCusp (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) U p.1.1
          (inertiaBar p))) =
      MX.equiv hτ _ ((natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm (tameGen p)) := by
  have h1 : syncEquivBar hg hUx hW₀ hW₀U hπW hπ (inertiaToCusp (barData k hτ) (barEquivL k hτ)
      (barData_H_le k hτ) U p.1.1 (inertiaBar p)) =
      (natIsoHatBar hτ hg).symm (tameChar (kbar_mem_idx p) π (inertiaBar p)) := by
    rw [← cuspInertiaZHatEquiv_inertiaToCusp (barEquivL_algebraMap k hτ) (barEquivL_tau k hτ)
      (genus_bar_pos hg) U hUx hW₀ hW₀U hπW hπ]
    rfl
  apply Subtype.ext
  funext i
  rw [h1]
  exact congrArg (natIsoBar hτ i.n hg).symm (proj_tameChar_inertiaBar' p hne hπW hπ i.n)

/-- **The data of the synchronization at a cusp** `p` (`t ∉ W`): `U_x = X_{k̄} ∖ {x}` with
`U_{k̄} ⊆ U_x`, `W` centred on `x`, and a uniformiser of `W ∩ F k̄`. -/
theorem exists_syncData' (p : InertiaIndex (curveGaloisData k hτ)) (hp : coordT τ ∉ p.1.1)
    {R : Prop}
    (hR : ∀ (x' : baseChangeKbar k X) (U : (baseChangeKbar k X).Opens) [Nonempty U]
      (π : (F (barData k hτ))ˣ), (U : Set (baseChangeKbar k X))ᶜ = {x'} → chartBar k τ ≤ U →
      IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) ⊤ p.1.1 →
      ¬ IsCentredOn (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ) U p.1.1 →
      p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X) < 1 →
      (∀ f ∈ F (barData k hτ), p.1.1.valuation f < 1 →
        p.1.1.valuation f ≤ p.1.1.valuation ((π : F (barData k hτ)) : FFClosure X)) → R) : R := by
  have hne := idxVal_ne_top_of_cusp p hp
  refine pointData_of_liesOver (barEquivL_algebraMap k hτ)
    (placeBarOf p.2.1 (unif p).ne_zero (unif_valuation_lt_one p hne)) p.1.1
    (fun _ ↦ Iff.rfl) ?_
  intro x U _ π hUx hW₀ hW₀U hπW hπ
  refine hR x U π hUx (fun z hz => ?_) hW₀ hW₀U hπW hπ
  by_contra hzU
  have hzx : z = x := by
    have : z ∈ (U : Set (baseChangeKbar k X))ᶜ := hzU
    rw [hUx] at this
    exact this
  obtain ⟨y, hyU, hy⟩ := exists_notMem_of_not_isCentredOn (barData k hτ) (baseChangeKbar k X)
    (barEquivL k hτ) (barEquivL_algebraMap k hτ) U (kbar_mem_idx p) hW₀U
  have hyx : y = x := by
    have : y ∈ (U : Set (baseChangeKbar k X))ᶜ := hyU
    rw [hUx] at this
    exact this
  rw [hyx, ← hzx] at hy
  have hc := isCentredOn_of_stalkVS_eq (barData k hτ) (baseChangeKbar k X) (barEquivL k hτ)
    (barEquivL_algebraMap k hτ) (chartBar k τ) (kbar_mem_idx p) hz hy
  exact hp ((isCentredOn_chartBar_iff (kbar_mem_idx p)).1 hc)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
lemma coe_bcToDeltaU_inertiaBar (p : InertiaIndex (curveGaloisData k hτ)) :
    (bcToDeltaU (curveGaloisData k hτ) (inertiaBar p : (barData k hτ).H) :
        Pi (curveGaloisData k hτ)) =
      ((p.1.2 : (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) := by
  rw [coe_bcToDeltaU]
  exact congrArg _ (Subtype.ext (AlgEquiv.ext fun y => inertiaBar_apply p y))

end Sync

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

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
set_option maxHeartbeats 3200000 in
-- the étale fundamental groups and the modules `M_X`, `Ẑ(1)` unify slowly
/-- **`cycloCongr_tameGen` at any cusps** (no rational points below `p`, `p'`). -/
theorem cycloCongr_tameGen'
    (p : InertiaIndex (curveGaloisData k hτ)) (hne : idxVal p ≠ ⊤)
    (p' : InertiaIndex (curveGaloisData k' hτ')) (hne' : idxVal p' ≠ ⊤)
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
  have A := syncEquivBar_inertiaToCusp' hg p hne hUx hW₀ hW₀U hπW hπ
  have A' := syncEquivBar_inertiaToCusp' hg' p' hne' hUx' hW₀' hW₀U' hπW' hπ'
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

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U`, `Π_X` are found slowly
set_option maxHeartbeats 3200000 in
-- the étale fundamental groups and the modules `M_X`, `Ẑ(1)` unify slowly
/-- **The cyclotome `cycloCongr Φ` carries tame generators to tame generators**
([AbsTopIII] Thm 1.9 (b), (c), Prop 1.4 (ii), T3 l.1771–1803 and l.2144–2157, along `Φ`): if `Φ`
carries the cuspidal inertia groups of `Π_U` onto cuspidal inertia groups of `Π_{U'}` and
conversely (`hcusp`, `hcusp'`), and the cusps are separated by inertia on both sides
(`CuspSep`), then `cycloCongr Φ (θ_p) = θ_{p'}` for cusps `p = (W, σ)`, `p' = (W', σ')` with
`Φ(I_W) = I_{W'}` and `Φ[σ] = [σ']`. -/
theorem cycloCongr_tameGen_of_cusps
    (hcusp : ∀ W ∈ CuspW (k := k) (t := coordT τ), ∃ W' ∈ CuspW (k := k') (t := coordT τ'),
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
        inertiaPi (curveGaloisData k' hτ') W')
    (hcusp' : ∀ W' ∈ CuspW (k := k') (t := coordT τ'), ∃ W ∈ CuspW (k := k) (t := coordT τ),
      (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
        inertiaPi (curveGaloisData k' hτ') W')
    (hsep : CuspSep (curveGaloisData k hτ)) (hsep' : CuspSep (curveGaloisData k' hτ'))
    (p : InertiaIndex (curveGaloisData k hτ)) (p' : InertiaIndex (curveGaloisData k' hτ'))
    (hp : coordT τ ∉ p.1.1) (hp' : coordT τ' ∉ p'.1.1)
    (hW : (inertiaPi (curveGaloisData k hτ) p.1.1).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') p'.1.1)
    (hσ : Φ ((p.1.2 : (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) =
      ((p'.1.2 : (curveGaloisData k' hτ').H) : Pi (curveGaloisData k' hτ'))) :
    cycloCongr Φ hfill ψ hψ (tameGen p) = tameGen p' := by
  refine exists_syncData' p hp ?_
  intro xb V _ π hUx hle hW₀ hW₀U hπW hπ
  refine exists_syncData' p' hp' ?_
  intro xb' V' _ π' hUx' hle' hW₀' hW₀U' hπW' hπ'
  refine cycloCongr_tameGen' Φ hfill ψ hψ p (idxVal_ne_top_of_cusp p hp) p'
    (idxVal_ne_top_of_cusp p' hp') (hUx ▸ Set.finite_singleton xb) hle hUx hW₀ hW₀U hπW hπ
    (hUx' ▸ Set.finite_singleton xb') hle' hUx' hW₀' hW₀U' hπW' hπ'
    (hK_of_cusps Φ ψ hψ hcusp hcusp' hsep hsep' ⟨p.2.1, hp⟩ ⟨p'.2.1, hp'⟩ hW hUx hW₀U hle hUx'
      hW₀U' hle')
    (fun σ hσ => exists_rhoBarU_of_map Φ ψ hψ p'.2.1 hW σ hσ)
    (fun σ' hσ' => exists_rhoBarU_of_map_symm Φ ψ hψ p.2.1 hW σ' hσ') ?_
  rw [deltaBarUCongr_rhoBarU_iff, coe_bcToDeltaU_inertiaBar, coe_bcToDeltaU_inertiaBar]
  exact hσ

end Tame

end Iut.Reconstruction.Thm19
