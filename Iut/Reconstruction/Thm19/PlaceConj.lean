/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.CuspDecomp

/-!
# Places of `F` and conjugacy of inertia groups; `divAt` of divisors on rational points

Two ingredients of the transport of `P_V` ([AbsTopIII] Thm 1.9 (c), `Topics in Absolute Anabelian
Geometry III.txt` l.2153–2157) along the stage isomorphisms (MR9 item 4, step 3 (b), (c)):

* **`exists_conj_inertiaH_of_comap_eq`**: places `W`, `W'` of `Ω` over the same place of
  `F = Ω^H` have `Π_U`-conjugate inertia groups (`W' = σ W` for some `σ ∈ Gal(Ω/F) = H`,
  curves-jacobian `exists_algEquiv_comap_eq`; `map_conj_inertiaH`);
* `mapDomain_apply_eq_of_iff`, **`ratDivF_apply_eq_of_iff`**: the multiplicity of a divisor
  `∑ nᵢ xᵢ` on rational points at a place is the sum of the `nᵢ` over the points at that place,
  so two divisors `f`, `β_* f` have the same multiplicity at `P`, `P'` as soon as `β` matches
  "lying at `P`" with "lying at `P'`" on the support of `f`; **`divAt_ratDivF_eq_of_iff`**: the
  same for `divAt` at inertia indices (the form used by `HasResidues`);
* `exists_transPlace_eq_of_comap_eq`, `mem_iff_of_map_inertiaH_eq` (equal inertia groups over
  the same place of `F` and `Comm(I_W) = D_W` give the same place of `Ω_U`),
  `kernel_fix_F_constExt`;
* `comap_eq_of_map_inertiaH_eq_curve` (cusps of a curve with equal inertia groups lie over the
  same place of `K(X)`, curves-jacobian `comap_ffEmb_eq_of_arithInertia_conj` along `piBridge`)
  and **`GStage.comap_eq_of_conj_inertiaH`**: cusps of a geometric stage with conjugate inertia
  groups lie over the same place of `F_{K₁}` (the converse of `exists_conj_inertiaH_of_comap_eq`);
* **`LiftData.comap_eq_iff`**: the stage isomorphism matches "same place of `F_{K₁}`" for cusps
  with "same place of `F_{ψ(K₁)}`" for their image cusps;
* `LiftData.exists_map_inertiaH_e_symm`, `LiftData.map_inertiaH_constIso_of_e`,
  **`LiftData.exists_map_inertiaH_constIso_symm`**: every cuspidal inertia group of the target
  stage is the image of one of the source stage.
-/

open CategoryTheory AlgebraicGeometry Pi1 Pi1.Orbifold KummerTheory KummerTheory.Curve
  AffOrbicurve WeilCurves.FunctionField CurvesJacobian CurvesJacobian.Kummer CurvesJacobian.Cusp
  CurvesJacobian.LocAn Belyi Belyi.Anabelian

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section Conj

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **Places over the same place of `F = Ω^H` are `H`-translates** (curves-jacobian
`exists_algEquiv_comap_eq`; `Gal(Ω/F) = H` for the closed subgroup `H`). -/
theorem exists_transPlace_eq_of_comap_eq (W W' : ValuationSubring Ω)
    (h : W.comap (algebraMap (F D) Ω) = W'.comap (algebraMap (F D) Ω)) :
    ∃ ρ : D.H, W' = transPlace (ρ : Ω ≃ₐ[K₀ k t] Ω) W := by
  haveI : IsGalois (F D) Ω := IsGalois.tower_top_of_isGalois (K₀ k t) (F D) Ω
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comap_eq W W' h
  set σ' : Ω ≃ₐ[K₀ k t] Ω := σ.restrictScalars (K₀ k t)
  have hσH : σ' ∈ D.H := by
    have hcl : IsClosed (D.H : Set (Ω ≃ₐ[K₀ k t] Ω)) := D.isClosed_H
    have h := InfiniteGalois.fixingSubgroup_fixedField (⟨D.H, hcl⟩ : ClosedSubgroup _)
    change σ' ∈ (⟨D.H, hcl⟩ : ClosedSubgroup _).toSubgroup
    rw [← h, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact σ.commutes ⟨x, hx⟩
  exact ⟨⟨σ', hσH⟩, hσ⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Places over the same place of `F` have conjugate inertia groups** in `Π_U`. -/
theorem exists_conj_inertiaH_of_comap_eq (W W' : ValuationSubring Ω)
    (h : W.comap (algebraMap (F D) Ω) = W'.comap (algebraMap (F D) Ω)) :
    ∃ γ : Pi D, ((inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))).map
        (MulAut.conj γ).toMonoidHom =
      (inertiaH D W').map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  obtain ⟨ρ, rfl⟩ := exists_transPlace_eq_of_comap_eq W W' h
  exact ⟨(ρ : Pi D), map_conj_inertiaH ρ W⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Equal inertia groups over the same place of `F` give the same place of `Ω_U`**: if `W`,
`W'` lie over the same place of `F`, have the same inertia group in `Π_U`, and `Comm(I_W) = D_W`,
then `W` and `W'` agree on every element fixed by `ker(H ↠ Π_U)` (`W' = ρ W` with `[ρ]` in the
normaliser, hence in `D_W`). -/
theorem mem_iff_of_map_inertiaH_eq (W₁ W₂ : ValuationSubring Ω)
    (hF : W₁.comap (algebraMap (F D) Ω) = W₂.comap (algebraMap (F D) Ω))
    (hI : (inertiaH D W₁).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) =
      (inertiaH D W₂).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)))
    (hC : Subgroup.Commensurable.commensurator
        ((inertiaH D W₁).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) =
      (decompH D W₁).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)))
    {z : Ω} (hz : ∀ κ ∈ GaloisPi1.kernel D.H D.S, (κ : Ω ≃ₐ[K₀ k t] Ω) z = z) :
    z ∈ W₁ ↔ z ∈ W₂ := by
  obtain ⟨ρ, rfl⟩ := exists_transPlace_eq_of_comap_eq W₁ W₂ hF
  have hN : (ρ : Pi D) ∈ Subgroup.Commensurable.commensurator
      ((inertiaH D W₁).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) := by
    rw [Subgroup.Commensurable.commensurator_mem_iff, conjAct_smul_eq_map, map_conj_inertiaH,
      ← hI]
  rw [hC] at hN
  obtain ⟨δ, hδ, hδρ⟩ := hN
  have hκ : δ / ρ ∈ GaloisPi1.kernel D.H D.S :=
    (QuotientGroup.eq_iff_div_mem).1 hδρ
  have h2 := hz _ hκ
  rw [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply,
    AlgEquiv.aut_inv] at h2
  have e1 : (ρ : Ω ≃ₐ[K₀ k t] Ω).symm z = (δ : Ω ≃ₐ[K₀ k t] Ω).symm z :=
    ((congrArg (δ : Ω ≃ₐ[K₀ k t] Ω).symm h2.symm).trans
      (AlgEquiv.symm_apply_apply _ _)).symm
  rw [mem_transPlace, e1]
  have h3 : (δ : Ω ≃ₐ[K₀ k t] Ω) ((δ : Ω ≃ₐ[K₀ k t] Ω).symm z) ∈ W₁ ↔
      (δ : Ω ≃ₐ[K₀ k t] Ω).symm z ∈ W₁ := hδ _
  rw [AlgEquiv.apply_symm_apply] at h3
  exact h3

/-- **`ker(H ↠ Π_U)` fixes `F_{K₁}`** (it comes from the kernel of the extension of the field of
constants,
`ambientKernel_le_map_constExt`, whose elements fix `F_{K₁} = Ω^{H_{K₁}}`). -/
lemma kernel_fix_F_constExt (K₁ : IntermediateField k Ω) [FiniteDimensional k K₁] {κ : D.H}
    (hκ : κ ∈ GaloisPi1.kernel D.H D.S) {z : Ω} (hz : z ∈ F (constExt K₁ D)) :
    (κ : Ω ≃ₐ[K₀ k t] Ω) z = z := by
  have h1 : (κ : Ω ≃ₐ[K₀ k t] Ω) ∈ GaloisPi1.ambientKernel D.H D.S := hκ
  obtain ⟨s', -, hs'⟩ := ambientKernel_le_map_constExt (K := K₁) D h1
  have hs'H : s' ∈ (constExt K₁ D).H := (mem_constExt_H D).2 (by rw [hs']; exact κ.2)
  rw [← hs', resK_apply]
  exact (IntermediateField.mem_fixedField_iff _ _).1 hz _ hs'H

end Conj

section Div

/-- Two images of a finitely supported function agree at `b₁`, `b₂` if the two maps match
"`↦ b₁`" with "`↦ b₂`" on the support. -/
lemma mapDomain_apply_eq_of_iff {α β γ M : Type*} [AddCommMonoid M] (f : α →₀ M)
    (h₁ : α → β) (h₂ : α → γ) (b₁ : β) (b₂ : γ) (H : ∀ a ∈ f.support, h₁ a = b₁ ↔ h₂ a = b₂) :
    f.mapDomain h₁ b₁ = f.mapDomain h₂ b₂ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun a ha => ?_
  change Finsupp.single (h₁ a) (f a) b₁ = Finsupp.single (h₂ a) (f a) b₂
  rw [Finsupp.single_apply, Finsupp.single_apply]
  exact if_congr (H a ha) rfl rfl

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']

/-- **Multiplicities of `∑ nᵢ xᵢ` and of `β_* (∑ nᵢ xᵢ)`** at `P`, `P'` agree if `β` matches
the points at `P` with the points at `P'` on the support. -/
theorem ratDivF_apply_eq_of_iff (β : RatPoint D → RatPoint D') (f : RatPoint D →₀ ℤ)
    (P : Place k (F D)) (P' : Place k' (F D'))
    (H : ∀ x ∈ f.support, placeOfF (β x) = P' ↔ placeOfF x = P) :
    ratDivF (f.mapDomain β) P' = ratDivF f P := by
  rw [ratDivF, ratDivF, ← Finsupp.mapDomain_comp]
  exact mapDomain_apply_eq_of_iff f _ _ P' P H

/-- **`divAt` of `∑ nᵢ xᵢ` and of `β_* (∑ nᵢ xᵢ)`** at inertia indices `p`, `p'` whose places
are proper (`W ∩ F ≠ F`) agree if `β` matches the points below `p` with those below `p'` on the
support. -/
theorem divAt_ratDivF_eq_of_iff (β : RatPoint D → RatPoint D') (f : RatPoint D →₀ ℤ)
    (p : InertiaIndex D) (p' : InertiaIndex D') (hp : idxVal p ≠ ⊤) (hp' : idxVal p' ≠ ⊤)
    (H : ∀ x ∈ f.support, placeOfF (β x) = idxPlace p' hp' ↔ placeOfF x = idxPlace p hp) :
    divAt (ratDivF (f.mapDomain β)) p' = divAt (ratDivF f) p := by
  rw [divAt, divAt, dif_pos hp, dif_pos hp']
  exact ratDivF_apply_eq_of_iff β f _ _ H

end Div

/-! ### Equal inertia groups at cusps of a curve and of a geometric stage -/

section Curve

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  [IsGalois (K₀ K (coordT τ)) (FFClosure C.Xbar)] (hU : C.U = chartOne K C.Xbar τ)

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
include Ω hU in
/-- **Cusps with equal inertia groups lie over the same place of `F = K(X)`** (curves-jacobian
`comap_ffEmb_eq_of_arithInertia_conj`, [GalSect] Thm 1.3 (i) for cusps, along `piBridge`). -/
theorem comap_eq_of_map_inertiaH_eq_curve (W₁ W₂ : ValuationSubring (FFClosure C.Xbar))
    (hW₁ : W₁ ∈ CuspW (k := K) (t := coordT τ)) (hW₂ : W₂ ∈ CuspW (k := K) (t := coordT τ))
    (h : (inertiaH (curveGaloisData K hτ) W₁).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S)) =
      (inertiaH (curveGaloisData K hτ) W₂).map
        (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K hτ).H
          (curveGaloisData K hτ).S))) :
    W₁.comap (algebraMap (F (curveGaloisData K hτ)) (FFClosure C.Xbar)) =
      W₂.comap (algebraMap (F (curveGaloisData K hτ)) (FFClosure C.Xbar)) := by
  have h' := congrArg (fun S => S.map (piBridge (Ω := Ω) hτ hU).toMulEquiv.toMonoidHom) h
  rw [map_inertiaH_piBridge hτ hU, map_inertiaH_piBridge hτ hU] at h'
  have hcm := comap_ffEmb_eq_of_arithInertia_conj Ω C hc.out
    ((isCuspPlace_comap_iff (Ω := Ω) hτ hU W₁).2 hW₁)
    ((isCuspPlace_comap_iff (Ω := Ω) hτ hU W₂).2 hW₂) 1 (by
      rw [h']
      ext y
      simp)
  ext x
  set e := (curveEquivL K hτ).symm ⟨x, x.2⟩
  have he : algebraMap C.Xbar.functionField (FFClosure C.Xbar) e = x := by
    rw [← curveEquivL_apply K hτ, RingEquiv.apply_symm_apply]
  have hσ : (σc (Ω := Ω) (C := C)).symm (ffEmb Ω C hc.out e) =
      algebraMap C.Xbar.functionField (FFClosure C.Xbar) e := by
    rw [RingEquiv.symm_apply_eq]
    exact (σc_algebraMap (Ω := Ω) (C := C) e).symm
  have h4 := SetLike.ext_iff.1 hcm e
  simp only [ValuationSubring.mem_comap, RingHom.coe_coe, hσ, he] at h4
  exact h4

end Curve

section GStageConj

variable {K : Type u} [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω] [CharZero Ω] {C : HypCurve K}
  [hc : Fact (C.U : Set C.Xbar)ᶜ.Nonempty]

attribute [local instance] isIntegral_Xbar nonempty_U

variable {τ : C.Xbar.functionField} (hτ : Transcendental K τ)
  (hU : C.U = chartOne K C.Xbar τ)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
include Ω hU in
/-- **Cusps of a geometric stage with conjugate inertia groups lie over the same place of
`F_{K₁}`** (reduce to equal inertia groups by the translation `W ↦ ρW`, `ρ ∈ H_{K₁}`; pass to
`Π_V` by `piRes`; `comap_eq_of_map_inertiaH_eq_curve`, `mem_iff_of_map_inertiaH_eq` with
`Comm(I_W) = D_W`, and `kernel_fix_F_constExt`). -/
theorem GStage.comap_eq_of_conj_inertiaH (g' : GStage K hτ)
    (W₁ W₂ : ValuationSubring (FFClosure C.Xbar))
    (hW₁ : W₁ ∈ CuspW (k := g'.K) (t := coordT g'.τ₀))
    (hW₂ : W₂ ∈ CuspW (k := g'.K) (t := coordT g'.τ₀)) (γ : Pi g'.data)
    (h : ((inertiaH g'.data W₁).map
        (QuotientGroup.mk' (GaloisPi1.kernel g'.data.H g'.data.S))).map
        (MulAut.conj γ).toMonoidHom =
      (inertiaH g'.data W₂).map (QuotientGroup.mk' (GaloisPi1.kernel g'.data.H g'.data.S))) :
    W₁.comap (algebraMap (F g'.data) (FFClosure C.Xbar)) =
      W₂.comap (algebraMap (F g'.data) (FFClosure C.Xbar)) := by
  obtain ⟨ρ, rfl⟩ := QuotientGroup.mk_surjective γ
  have h0 := (map_conj_inertiaH ρ W₁).symm.trans h
  have hW₁' : transPlace (ρ : FFClosure C.Xbar ≃ₐ[K₀ g'.K (coordT g'.τ₀)] FFClosure C.Xbar) W₁ ∈
      CuspW (k := g'.K) (t := coordT g'.τ₀) := transPlace_mem_CuspW hW₁ _
  have e1 : W₁.comap (algebraMap (F g'.data) (FFClosure C.Xbar)) =
      (transPlace (ρ : FFClosure C.Xbar ≃ₐ[K₀ g'.K (coordT g'.τ₀)] FFClosure C.Xbar) W₁).comap
        (algebraMap (F g'.data) (FFClosure C.Xbar)) := by
    ext x
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, mem_transPlace]
    have hx : (ρ : FFClosure C.Xbar ≃ₐ[K₀ g'.K (coordT g'.τ₀)] FFClosure C.Xbar).symm
        (x : FFClosure C.Xbar) = x := by
      rw [AlgEquiv.symm_apply_eq]
      exact ((IntermediateField.mem_fixedField_iff _ _).1 x.2 _ ρ.2).symm
    exact (congrArg (· ∈ W₁) hx).symm.to_iff
  have hb := congrArg (fun S => S.map (piRes g'.K (curveGaloisData K g'.hτ₀))) h0
  rw [map_piRes_inertiaH g'.K (mem_CuspW_of_constExt g'.K hW₁').1,
    map_piRes_inertiaH g'.K (mem_CuspW_of_constExt g'.K hW₂).1] at hb
  have hFb := comap_eq_of_map_inertiaH_eq_curve Ω (C := subCurve C (chartOne K C.Xbar g'.τ₀)
    (chartOne_le_U hτ hU g'.hτ₀ g'.htV) (chartOne_ne g'.τ₀)) g'.hτ₀ rfl _ W₂
    (mem_CuspW_of_constExt g'.K hW₁') (mem_CuspW_of_constExt g'.K hW₂) hb
  have hC := commensurator_inertiaH_curve Ω (C := subCurve C (chartOne K C.Xbar g'.τ₀)
    (chartOne_le_U hτ hU g'.hτ₀ g'.htV) (chartOne_ne g'.τ₀)) g'.hτ₀ rfl _
    (mem_CuspW_of_constExt g'.K hW₁')
  rw [e1]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap]
  exact mem_iff_of_map_inertiaH_eq _ W₂ hFb hb hC
    (fun κ hκ => kernel_fix_F_constExt g'.K hκ x.2)

end GStageConj

section Group

lemma map_symm_eq_of_map_eq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {S : Subgroup G}
    {T : Subgroup G'} (h : S.map e.toMonoidHom = T) : T.map e.symm.toMonoidHom = S := by
  rw [← h, Subgroup.map_map]
  have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  rw [this, Subgroup.map_id]

lemma map_conj_of_map_eq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {S₁ S₂ : Subgroup G} {T₁ T₂ : Subgroup G'} (h₁ : S₁.map e.toMonoidHom = T₁)
    (h₂ : S₂.map e.toMonoidHom = T₂) {γ : G} (h : S₁.map (MulAut.conj γ).toMonoidHom = S₂) :
    T₁.map (MulAut.conj (e γ)).toMonoidHom = T₂ := by
  rw [← h₁, ← h₂, ← h, map_conj_map]
  rfl

end Group

end Iut.Reconstruction.Thm19

/-! ### Along lift data -/

namespace Iut.Reconstruction

open Thm19

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
/-- **The stage isomorphism matches the places of `F_{K₁}` below cusps**: for cusps `W₁`, `W₂`
of the stage with image cusps `W₁''`, `W₂''` (`E(I_{Wᵢ}) = I_{Wᵢ''}`), `W₁`, `W₂` lie over the
same place of `F_{K₁}` iff `W₁''`, `W₂''` lie over the same place of `F_{ψ(K₁)}`. -/
theorem LiftData.comap_eq_iff (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W₁ W₂ : ValuationSubring (FFClosure C.Xbar))
    (hW₁ : W₁ ∈ CuspW (k := g.K) (t := coordT g.τ₀))
    (hW₂ : W₂ ∈ CuspW (k := g.K) (t := coordT g.τ₀))
    (W₁'' W₂'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW₁'' : W₁'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (hW₂'' : W₂'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ))
    (h₁ : ((inertiaH g.data W₁).map
        (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data W₁'').map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)))
    (h₂ : ((inertiaH g.data W₂).map
        (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data W₂'').map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S))) :
    W₁.comap (algebraMap (F g.data) (FFClosure C.Xbar)) =
        W₂.comap (algebraMap (F g.data) (FFClosure C.Xbar)) ↔
      W₁''.comap (algebraMap (F L.tgt.data) (FFClosure C₂.Xbar)) =
        W₂''.comap (algebraMap (F L.tgt.data) (FFClosure C₂.Xbar)) := by
  constructor
  · intro hF
    obtain ⟨γ, hγ⟩ := exists_conj_inertiaH_of_comap_eq W₁ W₂ hF
    exact GStage.comap_eq_of_conj_inertiaH Ω₂ hτ₂ hU₂ L.tgt W₁'' W₂'' hW₁'' hW₂'' _
      (map_conj_of_map_eq _ h₁ h₂ hγ)
  · intro hF
    obtain ⟨γ, hγ⟩ := exists_conj_inertiaH_of_comap_eq W₁'' W₂'' hF
    exact GStage.comap_eq_of_conj_inertiaH Ω hτ hU g W₁ W₂ hW₁ hW₂ _
      (map_conj_of_map_eq _ (map_symm_eq_of_map_eq _ h₁) (map_symm_eq_of_map_eq _ h₂) hγ)

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Every cuspidal inertia group of the target is the image under the normalised lift of one of
the source** (`IsCor38Lift.exists_map_inertiaH_galLift_symm`, `map_conj_inertiaH`). -/
theorem LiftData.exists_map_inertiaH_e_symm (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W'' : ValuationSubring (FFClosure C₂.Xbar)) (hW'' : W'' ∈ CuspW (k := K₂) (t := coordT L.υ)) :
    ∃ W ∈ CuspW (k := K) (t := coordT g.τ₀),
      ((inertiaH (curveGaloisData K g.hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K g.hτ₀).H
            (curveGaloisData K g.hτ₀).S))).map L.e.toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K₂ L.hυ) W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K₂ L.hυ).H
            (curveGaloisData K₂ L.hυ).S)) := by
  obtain ⟨b, hb⟩ := L.hb
  obtain ⟨τb, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨W, hW, hEq⟩ := L.hφ.exists_map_inertiaH_galLift_symm Φ g.hτ₀ rfl L.hυ rfl L.φ
    (transPlace ((τb⁻¹ : (curveGaloisData K₂ L.hυ).H) :
      FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar) W'')
    (transPlace_mem_CuspW hW'' _)
  refine ⟨W, hW, ?_⟩
  have hcomp : L.e.toMulEquiv.toMonoidHom =
      (MulAut.conj ((τb : (curveGaloisData K₂ L.hυ).H) :
        Pi (curveGaloisData K₂ L.hυ))).toMonoidHom.comp
        (galLift (Ω := Ω) (Ω₂ := Ω₂) g.hτ₀ rfl L.hυ rfl L.φ).toMulEquiv.toMonoidHom :=
    MonoidHom.ext fun x => hb x
  have e : transPlace ((τb : (curveGaloisData K₂ L.hυ).H) :
      FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar)
      (transPlace ((τb⁻¹ : (curveGaloisData K₂ L.hυ).H) :
        FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar) W'') = W'' := by
    have h := transPlace_inv_transPlace ((τb⁻¹ : (curveGaloisData K₂ L.hυ).H) :
      FFClosure C₂.Xbar ≃ₐ[K₀ K₂ (coordT L.υ)] FFClosure C₂.Xbar) W''
    rwa [Subgroup.coe_inv, inv_inv] at h
  rw [hcomp, ← Subgroup.map_map, hEq, map_conj_inertiaH τb, e]

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **From the normalised lift to the stage isomorphism**: if `e(I_W) = I_{W''}` in `Π_V`, then
`constIso e (I_W) = I_{W''}` at the stages (`piRes_constIso`, `map_piRes_inertiaH`). -/
theorem LiftData.map_inertiaH_constIso_of_e (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W : ValuationSubring (FFClosure C.Xbar)) (hW : W ∈ CuspW (k := K) (t := coordT g.τ₀))
    (W'' : ValuationSubring (FFClosure C₂.Xbar)) (hW'' : W'' ∈ CuspW (k := K₂) (t := coordT L.υ))
    (hEq : ((inertiaH (curveGaloisData K g.hτ₀) W).map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K g.hτ₀).H
            (curveGaloisData K g.hτ₀).S))).map L.e.toMulEquiv.toMonoidHom =
        (inertiaH (curveGaloisData K₂ L.hυ) W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel (curveGaloisData K₂ L.hυ).H
            (curveGaloisData K₂ L.hυ).S))) :
    ((inertiaH g.data W).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
        (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
          g.K).toMulEquiv.toMonoidHom =
      (inertiaH L.tgt.data W'').map
        (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) := by
  apply Subgroup.map_injective (piRes_injective (K := L.tgt.K) (curveGaloisData K₂ L.hυ))
  refine (map_map_eq_of_comm _ _ _ (piRes g.K (curveGaloisData K g.hτ₀))
    L.e.toMulEquiv.toMonoidHom fun p => piRes_constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk
      (piToGk_surjective_curve g.hτ₀) g.K p).trans ?_
  refine (congrArg (fun S => S.map L.e.toMulEquiv.toMonoidHom)
    (map_piRes_inertiaH g.K hW.1)).trans ?_
  exact hEq.trans (map_piRes_inertiaH L.tgt.K hW''.1).symm

set_option maxHeartbeats 1600000 in
-- the quotients `Π_V` unify slowly
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_V` are found slowly
/-- **Every cuspidal inertia group of the target stage is the image of one of the source stage**
under the stage isomorphism. -/
theorem LiftData.exists_map_inertiaH_constIso_symm (L : LiftData hτ hU hτ₂ hU₂ Φ g)
    (W'' : ValuationSubring (FFClosure C₂.Xbar))
    (hW'' : W'' ∈ CuspW (k := L.tgt.K) (t := coordT L.υ)) :
    ∃ W ∈ CuspW (k := g.K) (t := coordT g.τ₀),
      ((inertiaH g.data W).map (QuotientGroup.mk' (GaloisPi1.kernel g.data.H g.data.S))).map
          (constIso L.e (gkIso hτ hU hτ₂ hU₂ Φ) L.he_gk (piToGk_surjective_curve g.hτ₀)
            g.K).toMulEquiv.toMonoidHom =
        (inertiaH L.tgt.data W'').map
          (QuotientGroup.mk' (GaloisPi1.kernel L.tgt.data.H L.tgt.data.S)) := by
  have hW₀ := mem_CuspW_of_constExt L.tgt.K hW''
  obtain ⟨W, hW, hEq⟩ := L.exists_map_inertiaH_e_symm W'' hW₀
  exact ⟨W, mem_CuspW_constExt _ hW, L.map_inertiaH_constIso_of_e W hW W'' hW₀ hEq⟩

end Stage

end Iut.Reconstruction
