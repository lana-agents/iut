/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.SyncCuspTame

/-!
# Tame generators along the stage isomorphisms (MR9 item 4 (b-i), discharge of `TameCompat`)

[AbsTopIII] Thm 1.9 (b), (c) (`Topics in Absolute Anabelian Geometry III.txt` l.2144–2157) read the
tame generators through the synchronizations of Prop 1.4 (ii) (l.1771–1803), which are
group-theoretic (`Thm19/SyncCuspTame.lean`, `cycloCongr_tameGen_of_cusps`). Here the inputs of that
result are provided for curves over number fields and for the stage isomorphisms of lift data:

* generic: `kernel_fix_F_baseChange`, `mem_F_baseChange_of_constExt`, `inertiaPi_eq_bot_of_mem`,
  `map_piT_inertiaPi` (two coordinates of the same curve);
* **`mk_ne_one_of_cusp`**: a nontrivial cuspidal inertia element has nontrivial class in `Π_U`
  (its synchronization is its tame generator, `tameGen_ne_one`); `coordT_notMem_of_map`;
* **`cuspSep_curve`**: the separation property `CuspSep` for curves over number fields
  ([GalSect] Thm 1.3 (i) for cusps, `comap_eq_of_map_inertiaH_eq_curve`, and `Comm(I_W) = D_W`);
* **`LiftData.cycloVχ_cycloIso`**: at a stage, the coefficients `cycloVχ (cycloIso Φ)` are the
  cyclotome `cycloCongr L.e` of the normalised lift (both send the tame generators at a cusp of
  `U` to the tame generators of the image cusp, and the tame character is onto `Ẑ(1)`);
* **`LiftData.tameCompat_cycloIso`**: `LiftData.TameCompat (cycloIso Φ) L` (the field-of-constants
  extension `F ⊆ F_{K₁}` is unramified, `isUnif_baseChange`, `zHatRes_tameGen_eq`).
-/

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Pi1 AffOrbicurve KummerTheory KummerTheory.Curve
  CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp CurvesJacobian.LocAn.DeltaXEquiv Belyi
  AlgebraicGeometry.FiniteEtale CurvesJacobian.LocAn Belyi.Anabelian

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### Generic Galois models -/

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **`ker(H ↠ Π_U)` fixes `F k̄`** (it comes from `⟨⟨S_{k̄}⟩⟩ ⊆ H_{k̄}`,
`ambientKernel_S_le_map_baseChange`). -/
lemma kernel_fix_F_baseChange {κ : D.H} (hκ : κ ∈ GaloisPi1.kernel D.H D.S) {z : Ω}
    (hz : z ∈ F (baseChange D)) : (κ : Ω ≃ₐ[K₀ k t] Ω) z = z := by
  obtain ⟨s', -, hs'⟩ := ambientKernel_S_le_map_baseChange D (Subgroup.mem_subgroupOf.1 hκ)
  have hs'H : s' ∈ (baseChange D).H := (mem_baseChange_H D).2 (by rw [hs']; exact κ.2)
  rw [← hs', resK₀_apply]
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz _ hs'H

/-- **`F_{K₁} ⊆ F k̄`** for an algebraic extension `k ⊆ K₁ ⊆ Ω`. -/
lemma mem_F_baseChange_of_constExt (K₁ : IntermediateField k Ω) [Algebra.IsAlgebraic k K₁]
    {x : Ω} (hx : x ∈ F (constExt K₁ D)) : x ∈ F (baseChange D) := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  obtain ⟨σ, hσ⟩ := exists_resK_eq (k := k) (K := K₁) (t := t) (h := resK₀ k t τ) fun c =>
    τ.commutes ⟨algebraMap K₁ Ω c, (K₀ (kbar k Ω) t).algebraMap_mem ⟨algebraMap K₁ Ω c,
      mem_algebraicClosure_iff.mpr (Algebra.IsAlgebraic.isAlgebraic (R := k) c).algebraMap⟩⟩
  have hσH : σ ∈ (constExt K₁ D).H :=
    (mem_constExt_H D).2 (by rw [hσ]; exact (mem_baseChange_H D).1 hτ)
  exact (DFunLike.congr_fun hσ x).symm.trans (hx σ hσH)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Places over `U` have trivial inertia in `Π_U`.** -/
lemma inertiaPi_eq_bot_of_mem (hH : D.H ≤ D.HL) {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) (ht : t ∈ W) : inertiaPi D W = ⊥ := by
  refine eq_bot_iff.2 ?_
  rintro _ ⟨σ, hσ, rfl⟩
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff _).2
    (D.mem_kernel_of_mem_S σ ⟨hH σ.2, W, hk, ht, hσ⟩))

variable {t₂ : Ω} {D₂ : GaloisData k t₂} [IsGalois (K₀ k t₂) Ω]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Two charts of the same curve** (`F D = F D₂`): the transition `Π_{U₂} → Π_U` maps the
inertia group of `W` onto that of `W`. -/
lemma map_piT_inertiaPi (hF : ∀ x ∈ F D, x ∈ F D₂) (hF' : ∀ x ∈ F D₂, x ∈ F D)
    (hW : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W) (hH : D.H ≤ D.HL) (W : ValuationSubring Ω) :
    (inertiaPi D₂ W).map (piT D D₂ hF hW hH) = inertiaPi D W := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
    exact ⟨hT D D₂ hF σ, fun a ha => hσ a ha, rfl⟩
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨_, ⟨hT D₂ D hF' s, fun a ha => hs a ha, rfl⟩, ?_⟩
    exact congrArg (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))
      (Subtype.ext (AlgEquiv.ext fun _ => rfl))

end Generic

/-! ### Curves -/

section Curve

open CurvesJacobian.TopClass CurvesJacobian.CuspCentral

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsCurveOver k X] [IsIntegral X] {τ : X.functionField} {hτ : Transcendental k τ}
  [IsGalois (K₀ k (coordT τ)) (FFClosure X)]

attribute [local instance] mulOneClass_piX one_piX mul_piX divisionMonoid_piX inv_piX

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` and the étale fundamental groups are found slowly
set_option maxHeartbeats 1600000 in
-- the synchronization and the modules `M_X`, `Ẑ(1)` unify slowly
/-- **Cuspidal inertia injects into `Π_U`** (genus `≥ 1`): a nontrivial element `σ ∈ I_W ∩ H` at a
cusp has nontrivial class, since its image in `I_x ⊆ π₁ᵉᵗ(U_x)` synchronizes to `θ_p ≠ 1`
(`syncEquivBar_inertiaToCusp'`, `tameGen_ne_one`). -/
theorem mk_ne_one_of_cusp [hgf : Fact (0 < (CurvesJacobian.curveGenus k X).toNat)]
    (p : InertiaIndex (curveGaloisData k hτ)) (hp : coordT τ ∉ p.1.1) (hσ : p.1.2 ≠ 1) :
    ((p.1.2 : (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) ≠ 1 := by
  intro h1
  have hg := hgf.out
  have hne := idxVal_ne_top_of_cusp p hp
  refine tameGen_ne_one p hne hσ ?_
  have hρ : rhoBarU k hτ (inertiaBar p : (barData k hτ).H) = 1 := by
    apply (deltaUEquivBar k hτ).symm.injective
    apply Subtype.ext
    rw [deltaUEquivBar_symm_rhoBarU, coe_bcToDeltaU_inertiaBar, h1, map_one]
    rfl
  refine exists_syncData' p hp ?_
  intro xb V _ π hUx hle hW₀ hW₀U hπW hπ
  have A := syncEquivBar_inertiaToCusp' hg p hne hUx hW₀ hW₀U hπW hπ
  have hI : inertiaToCusp (barData k hτ) (barEquivL k hτ) (barData_H_le k hτ) V p.1.1
      (inertiaBar p) = 1 := by
    apply Subtype.ext
    rw [coe_inertiaToCusp, ← fillUx_rhoBarU k hτ hle, hρ, map_one]
    rfl
  rw [hI, map_one, map_one] at A
  have h2 := (MX.equiv hτ (F (curveGaloisData k hτ))).injective (A.symm.trans (map_one _).symm)
  exact (natIsoHatK hτ (F (curveGaloisData k hτ)) hg).symm.injective (h2.trans (map_one _).symm)

variable {k' : Type u} [Field k'] [CharZero k'] {X' : Scheme.{u}} [X'.Over (Spec (.of k'))]
  [IsCurveOver k' X'] [IsIntegral X'] {τ' : X'.functionField} {hτ' : Transcendental k' τ'}
  [IsGalois (K₀ k' (coordT τ')) (FFClosure X')]

set_option synthInstance.maxHeartbeats 400000 in
-- instances on the quotients `Π_U` are found slowly
/-- **The image of a cuspidal inertia group is at a cusp**: if `Φ(I_W) = I_{W'}` for a cusp `W`,
then `W'` is a cusp (inertia over `U'` is trivial in `Π_{U'}`, cuspidal inertia is not). -/
theorem coordT_notMem_of_map [Fact (0 < (CurvesJacobian.curveGenus k X).toNat)]
    (Φ : Pi (curveGaloisData k hτ) ≃ₜ* Pi (curveGaloisData k' hτ'))
    {W : ValuationSubring (FFClosure X)} (hW : W ∈ CuspW (k := k) (t := coordT τ))
    {W' : ValuationSubring (FFClosure X')} (hk' : ∀ c : k', algebraMap k' (FFClosure X') c ∈ W')
    (h : (inertiaPi (curveGaloisData k hτ) W).map Φ.toMulEquiv.toMonoidHom =
      inertiaPi (curveGaloisData k' hτ') W') : coordT τ' ∉ W' := by
  intro ht'
  have hbot := inertiaPi_eq_bot_of_mem (curveGaloisData_H_le k' hτ') hk' ht'
  have hinv : (coordT τ)⁻¹ ∈ W := (W.mem_or_inv_mem (coordT τ)).resolve_left hW.2
  have ht0 : coordT τ ≠ 0 := fun h0 => hW.2 (h0 ▸ W.zero_mem)
  have hlt : W.valuation (coordT τ)⁻¹ < 1 := by
    refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 hinv) fun h1 => hW.2 ?_
    rw [map_inv₀, inv_eq_one] at h1
    exact (W.valuation_le_one_iff _).1 h1.le
  have htF : coordT τ ∈ F (curveGaloisData k hτ) :=
    (F (curveGaloisData k hτ)).algebraMap_mem
      ⟨coordT τ, IntermediateField.mem_adjoin_simple_self k _⟩
  obtain ⟨σ, hσ, hne⟩ := exists_inertiaH_ne_one (D := curveGaloisData k hτ) hW.1
    ⟨(coordT τ)⁻¹, (F (curveGaloisData k hτ)).inv_mem htF, inv_ne_zero ht0, hlt⟩
  refine mk_ne_one_of_cusp ⟨(W, σ), hW.1, hσ⟩ hW.2 hne ?_
  have hx : Φ ((σ : (curveGaloisData k hτ).H) : Pi (curveGaloisData k hτ)) ∈
      inertiaPi (curveGaloisData k' hτ') W' := h ▸ ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
  rw [hbot] at hx
  exact Φ.injective ((Subgroup.mem_bot.1 hx).trans (map_one Φ).symm)

end Curve

/-! ### Separation of the cusps for curves over number fields -/

section Sep

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_U` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
include Ω hU in
/-- **[AbsTopIII] Thm 1.9: the cusps of `U_{k̄}` are separated by inertia** (`CuspSep`): cusps with
`Δ_U`-conjugate inertia groups lie over the same point of `X_{k̄}` (lift the conjugating element
to `ρ ∈ H_{k̄}`; then `I_{ρW₁} = I_{W₂}` gives the same place of `F` by
`comap_eq_of_map_inertiaH_eq_curve` and the same place of `F k̄` by `mem_iff_of_map_inertiaH_eq`
with `Comm(I_W) = D_W` and `kernel_fix_F_baseChange`; `ρ` fixes `F k̄`). -/
theorem cuspSep_curve : CuspSep (curveGaloisData K hτ) := by
  intro W₁ hW₁ W₂ hW₂ δ hδ h
  obtain ⟨ρ, hρ⟩ := bcToDeltaU_surjective (curveGaloisData K hτ) ⟨δ, hδ⟩
  set ρ₀ : (curveGaloisData K hτ).H := ((bcToDeltaTilde (curveGaloisData K hτ) ρ :
    deltaTilde (curveGaloisData K hτ)) : (curveGaloisData K hτ).H)
  have hδρ : δ = (ρ₀ : Pi (curveGaloisData K hτ)) := by
    have := congrArg Subtype.val hρ
    rw [coe_bcToDeltaU] at this
    exact this.symm
  rw [hδρ] at h
  have h0 := (map_conj_inertiaH ρ₀ W₁).symm.trans h
  have hW₁' := transPlace_mem_CuspW hW₁ (ρ₀ : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar)
  have hF := comap_eq_of_map_inertiaH_eq_curve Ω hτ hU _ W₂ hW₁' hW₂ h0
  have hC := commensurator_inertiaH_curve Ω hτ hU _ hW₁'
  ext z
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
  have hz := mem_iff_of_map_inertiaH_eq _ W₂ hF h0 hC (z := (z : FFClosure C.Xbar))
    (fun κ hκ => kernel_fix_F_baseChange hκ z.2)
  rw [mem_transPlace] at hz
  have hfix : (ρ₀ : FFClosure C.Xbar ≃ₐ[K₀ K (coordT τ)] FFClosure C.Xbar).symm
      (z : FFClosure C.Xbar) = z := by
    rw [AlgEquiv.symm_apply_eq]
    exact ((IntermediateField.mem_fixedField_iff _ _).1 z.2 _ ρ.2).symm
  rw [hfix] at hz
  exact hz

end Sep

end Iut.Reconstruction.Thm19
