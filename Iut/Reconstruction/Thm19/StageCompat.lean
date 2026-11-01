/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageIso
import Iut.Reconstruction.Thm19.GeomLim

/-!
# Stage isomorphisms and transition maps (MR9 item 3, step 6): the generic part

For the functoriality of [AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt`
l.2158–2178) in `Π_U ≃ Π_{U'}`, the stage isomorphisms `H¹(Π_V, Ẑ(1)) ≃* H¹(Π_{V'}, Ẑ(1))`
(`h1Congr`, `constH1Iso`) must commute with the transition maps `resT` of the colimit. The
lifts of [AbsTopII] Cor 3.8 are only compatible with the transitions up to an inner automorphism
by an element `m` acting trivially on `Ẑ(1)`. Here, in the Galois models:

* **`h1Congr_resT_conj`**: if `piT' ∘ E₂ = conj m ∘ E₁ ∘ piT`, `m` acts trivially on `Ẑ(1)` and
  the coefficients commute with `zT`, then `h1Congr E₂ ∘ resT = resT' ∘ h1Congr E₁`
  (`ContH1.map_conj_eq_self`);
* `h1Congr_h1Congr` (composition), **`h1Congr_eq_resT`** (an isomorphism inverse to a transition
  map on `Π` induces the transition map on `H¹`);
* for extensions of the field of constants: `piRes_piT` (`piRes` commutes with the transition maps),
  `gkFix_anti`, `constField_mono`, `le_constField_symm` (`K ⊆ ψ⁻¹(ψ(K))`), and
  `smul_eq_self_of_piToGk` (an element of `Π_{U_K}` over `1 ∈ G_k` acts trivially on `Ẑ(1)`).
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer Pi1.Orbifold

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

/-! ### `h1Congr` and the transition maps -/

section Generic

variable {k₁ k₂ Ω : Type u} [Field k₁] [Field k₂] [Field Ω] [Algebra k₁ Ω] [Algebra k₂ Ω]
  {t₁ t₂ : Ω} {D₁ : GaloisData k₁ t₁} {D₂ : GaloisData k₂ t₂}
  [IsGalois (K₀ k₁ t₁) Ω] [IsGalois (K₀ k₂ t₂) Ω] [CharZero k₁] [CharZero k₂]
  {k₁' k₂' Ω' : Type u} [Field k₁'] [Field k₂'] [Field Ω'] [Algebra k₁' Ω'] [Algebra k₂' Ω']
  {t₁' t₂' : Ω'} {D₁' : GaloisData k₁' t₁'} {D₂' : GaloisData k₂' t₂'}
  [IsGalois (K₀ k₁' t₁') Ω'] [IsGalois (K₀ k₂' t₂') Ω'] [CharZero k₁'] [CharZero k₂']
  {hF : ∀ x ∈ F D₁, x ∈ F D₂}
  {hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
    (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W} {hH : D₁.H ≤ D₁.HL}
  {hF' : ∀ x ∈ F D₁', x ∈ F D₂'}
  {hW' : ∀ W : ValuationSubring Ω', (∀ c : k₂', algebraMap k₂' Ω' c ∈ W) → t₂' ∈ W →
    (∀ c : k₁', algebraMap k₁' Ω' c ∈ W) ∧ t₁' ∈ W} {hH' : D₁'.H ≤ D₁'.HL}

set_option maxHeartbeats 3200000 in
-- the cocycle computation unfolds several quotient maps
set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **Stage isomorphisms commute with the transition maps** when the group isomorphisms do so up
to conjugation by an element acting trivially on the coefficients. -/
theorem h1Congr_resT_conj (E₁ : Pi D₁ ≃ₜ* Pi D₁') (E₂ : Pi D₂ ≃ₜ* Pi D₂')
    (χ₁ : ZHatOne (F D₁) Ω ≃ₜ* ZHatOne (F D₁') Ω') (χ₂ : ZHatOne (F D₂) Ω ≃ₜ* ZHatOne (F D₂') Ω')
    (hχ₁ : ∀ p z, χ₁ (p • z) = E₁ p • χ₁ z) (hχ₂ : ∀ p z, χ₂ (p • z) = E₂ p • χ₂ z)
    (m : Pi D₁')
    (hE : ∀ y, piT D₁' D₂' hF' hW' hH' (E₂ y) = m * E₁ (piT D₁ D₂ hF hW hH y) * m⁻¹)
    (hm : ∀ z : ZHatOne (F D₁') Ω', m • z = z)
    (hχ : ∀ z, χ₂ (zT D₁ D₂ z) = zT D₁' D₂' (χ₁ z))
    (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    h1Congr E₂ χ₂ hχ₂ (resT D₁ D₂ hF hW hH x) =
      resT D₁' D₂' hF' hW' hH' (h1Congr E₁ χ₁ hχ₁ x) := by
  have hm' : ∀ z : ZHatOne (F D₁') Ω', m⁻¹ • z = z := fun z => by
    conv_lhs => rw [← hm (m⁻¹ • z)]
    rw [smul_smul, mul_inv_cancel, one_smul]
  have hid : (MulDistribMulAction.toMonoidHom (ZHatOne (F D₁') Ω') m⁻¹⁻¹ :
      ZHatOne (F D₁') Ω' → ZHatOne (F D₁') Ω') = id := funext fun z => by
    rw [MulDistribMulAction.toMonoidHom_apply, inv_inv, hm]
    rfl
  have hc : Continuous (MulDistribMulAction.toMonoidHom (ZHatOne (F D₁') Ω') m⁻¹⁻¹) := by
    rw [hid]
    exact continuous_id
  have hconj : ((MulAut.conj m⁻¹).toMonoidHom : Pi D₁' → Pi D₁') = fun h => m⁻¹ * h * m⁻¹⁻¹ :=
    funext fun h => MulAut.conj_apply _ _
  have hcφ : Continuous (MulAut.conj m⁻¹).toMonoidHom := by
    rw [hconj]
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hcomp : ∀ h z, MulDistribMulAction.toMonoidHom (ZHatOne (F D₁') Ω') m⁻¹⁻¹
      ((MulAut.conj m⁻¹).toMonoidHom h • z) =
      h • MulDistribMulAction.toMonoidHom (ZHatOne (F D₁') Ω') m⁻¹⁻¹ z := by
    intro h z
    rw [hid, hconj]
    change (m⁻¹ * h * m⁻¹⁻¹) • z = h • z
    rw [inv_inv, mul_smul, mul_smul, hm, hm']
  rw [← ContH1.map_conj_eq_self m⁻¹ hcφ hc hcomp (h1Congr E₁ χ₁ hχ₁ x)]
  induction x using ContH1.induction_on with
  | h c =>
    simp only [h1Congr_apply, resT, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply]
    have e1 : piT D₁ D₂ hF hW hH (E₂.symm σ) = E₁.symm (m⁻¹ * piT D₁' D₂' hF' hW' hH' σ * m) := by
      rw [ContinuousMulEquiv.eq_symm_apply]
      have := hE (E₂.symm σ)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      rw [this]
      group
    change χ₂ (zT D₁ D₂ (c (piT D₁ D₂ hF hW hH (E₂.symm σ)))) =
      zT D₁' D₂' (MulDistribMulAction.toMonoidHom (ZHatOne (F D₁') Ω') m⁻¹⁻¹
        (χ₁ (c (E₁.symm (m⁻¹ * piT D₁' D₂' hF' hW' hH' σ * m⁻¹⁻¹)))))
    rw [MulDistribMulAction.toMonoidHom_apply, inv_inv, hm, e1, hχ]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **An isomorphism inverse to a transition map on `Π` induces the transition map on `H¹`.** -/
theorem h1Congr_eq_resT {D₂ : GaloisData k₂ t₂}
    {hF : ∀ x ∈ F D₁, x ∈ F D₂}
    {hW : ∀ W : ValuationSubring Ω, (∀ c : k₂, algebraMap k₂ Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k₁, algebraMap k₁ Ω c ∈ W) ∧ t₁ ∈ W}
    (E : Pi D₁ ≃ₜ* Pi D₂) (χ : ZHatOne (F D₁) Ω ≃ₜ* ZHatOne (F D₂) Ω)
    (hχ : ∀ p z, χ (p • z) = E p • χ z) (hE : ∀ y, piT D₁ D₂ hF hW hH (E y) = y)
    (hc : ∀ z, χ z = zT D₁ D₂ z) (x : ContH1 (Pi D₁) (ZHatOne (F D₁) Ω)) :
    h1Congr E χ hχ x = resT D₁ D₂ hF hW hH x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [h1Congr_apply, resT, ContH1.map_mk]
    congr 1
    apply Subtype.ext
    funext σ
    simp only [ContH1.cocyclesMap_apply]
    have e1 : E.symm σ = piT D₁ D₂ hF hW hH σ := by
      have := hE (E.symm σ)
      rw [ContinuousMulEquiv.apply_symm_apply] at this
      exact this.symm
    change χ (c (E.symm σ)) = zT D₁ D₂ (c (piT D₁ D₂ hF hW hH σ))
    rw [e1, hc]

end Generic

section Comp

variable {P P' P'' M M' M'' : Type*} [Group P] [TopologicalSpace P] [CommGroup M]
  [TopologicalSpace M] [IsTopologicalGroup M] [MulDistribMulAction P M]
  [Group P'] [TopologicalSpace P'] [CommGroup M'] [TopologicalSpace M']
  [IsTopologicalGroup M'] [MulDistribMulAction P' M']
  [Group P''] [TopologicalSpace P''] [CommGroup M''] [TopologicalSpace M'']
  [IsTopologicalGroup M''] [MulDistribMulAction P'' M'']

omit [IsTopologicalGroup M] [IsTopologicalGroup M''] in
lemma h1Congr_trans_comm (E : P ≃ₜ* P') (E' : P' ≃ₜ* P'') (χ : M ≃ₜ* M') (χ' : M' ≃ₜ* M'')
    (hχ : ∀ p m, χ (p • m) = E p • χ m) (hχ' : ∀ p m, χ' (p • m) = E' p • χ' m) (p : P) (m : M) :
    (χ.trans χ') (p • m) = (E.trans E') p • (χ.trans χ') m := by
  simp only [ContinuousMulEquiv.trans_apply, hχ, hχ']

/-- **`h1Congr` composes.** -/
lemma h1Congr_h1Congr (E : P ≃ₜ* P') (E' : P' ≃ₜ* P'') (χ : M ≃ₜ* M') (χ' : M' ≃ₜ* M'')
    (hχ : ∀ p m, χ (p • m) = E p • χ m) (hχ' : ∀ p m, χ' (p • m) = E' p • χ' m)
    (x : ContH1 P M) :
    h1Congr E' χ' hχ' (h1Congr E χ hχ x) =
      h1Congr (E.trans E') (χ.trans χ') (h1Congr_trans_comm E E' χ χ' hχ hχ') x := by
  induction x using ContH1.induction_on with
  | h c =>
    simp only [h1Congr_apply, ContH1.map_mk]
    rfl

end Comp

/-! ### Extensions of the field of constants -/

section Const

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]

lemma gkFix_anti {K K' : IntermediateField k Ω} (h : K ≤ K') : gkFix K' ≤ gkFix K := fun _ hg =>
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x (h hx)

variable {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] [CharZero k'] [IsAlgClosed Ω']

/-- `K ↦ K'` (`G_{K'} = ψ(G_K)`) is monotone. -/
lemma constField_mono (ψ : Gk k Ω ≃* Gk k' Ω') {K K' : IntermediateField k Ω} (h : K ≤ K') :
    constField ψ K ≤ constField ψ K' := by
  rintro _ ⟨y, hy, rfl⟩
  have hy' := (IntermediateField.mem_fixedField_iff _ _).1 hy
  refine ⟨y, (IntermediateField.mem_fixedField_iff _ _).2 ?_, rfl⟩
  rintro _ ⟨g, hg, rfl⟩
  exact hy' _ ⟨g, gkFix_anti h hg, rfl⟩

variable {t : Ω} {D : GaloisData k t} [IsGalois (K₀ k t) Ω]
  {t' : Ω'} {D' : GaloisData k' t'} [IsGalois (K₀ k' t') Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))

include e he hs in
/-- **`K ⊆ ψ⁻¹(ψ(K))`** for the fields of constants (`gkFix_constField`). -/
lemma le_constField_symm (K : IntermediateField k Ω) [FiniteDimensional k K] :
    K ≤ constField ψ.symm (constField ψ K) := by
  intro x hx
  have hxk : x ∈ kbar k Ω := algebraMap_mem_kbar (⟨x, hx⟩ : K)
  refine ⟨⟨x, hxk⟩, (IntermediateField.mem_fixedField_iff _ _).2 ?_, rfl⟩
  rintro _ ⟨g, hg, rfl⟩
  rw [gkFix_constField e ψ he hs K] at hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have h1 : ψ.symm.toMonoidHom (ψ.toMonoidHom g₀) = g₀ := ψ.symm_apply_apply g₀
  rw [h1]
  exact (mem_gkFix_iff K g₀).1 hg₀ ⟨x, hx⟩

end Const

section ConstPi

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]
  {t₁ t₂ : Ω} {D₁ : GaloisData k t₁} {D₂ : GaloisData k t₂}
  [IsGalois (K₀ k t₁) Ω] [IsGalois (K₀ k t₂) Ω]
  {K₁ K₂ : IntermediateField k Ω} [FiniteDimensional k K₁] [FiniteDimensional k K₂]

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`piRes` commutes with the transition maps.** -/
lemma piRes_piT (hF : ∀ x ∈ F (constExt K₁ D₁), x ∈ F (constExt K₂ D₂))
    (hW : ∀ W : ValuationSubring Ω, (∀ c : K₂, algebraMap K₂ Ω c ∈ W) → t₂ ∈ W →
      (∀ c : K₁, algebraMap K₁ Ω c ∈ W) ∧ t₁ ∈ W) (hH : (constExt K₁ D₁).H ≤ (constExt K₁ D₁).HL)
    (hF' : ∀ x ∈ F D₁, x ∈ F D₂)
    (hW' : ∀ W : ValuationSubring Ω, (∀ c : k, algebraMap k Ω c ∈ W) → t₂ ∈ W →
      (∀ c : k, algebraMap k Ω c ∈ W) ∧ t₁ ∈ W) (hH' : D₁.H ≤ D₁.HL)
    (y : Pi (constExt K₂ D₂)) :
    piRes K₁ D₁ (piT (constExt K₁ D₁) (constExt K₂ D₂) hF hW hH y) =
      piT D₁ D₂ hF' hW' hH' (piRes K₂ D₂ y) := by
  induction y using QuotientGroup.induction_on with
  | H σ => exact congrArg (fun h : D₁.H => (h : Pi D₁)) (Subtype.ext (AlgEquiv.ext fun _ => rfl))

set_option synthInstance.maxHeartbeats 400000 in
-- the action of `Π_{U_K}` on `Ẑ(1)` is found slowly
omit [IsGalois (K₀ k t₂) Ω] in
/-- **An element of `Π_{U_K}` over `1 ∈ G_k` acts trivially on `Ẑ(1)`.** -/
lemma smul_eq_self_of_piToGk (q : Pi (constExt K₁ D₁)) (hq : piToGk D₁ (piRes K₁ D₁ q) = 1)
    (z : ZHatOne (F (constExt K₁ D₁)) Ω) : q • z = z := by
  obtain ⟨w, rfl⟩ := (zKEquiv D₁ K₁).surjective z
  change q • zK K₁ D₁ w = zK K₁ D₁ w
  rw [← zK_piRes_smul K₁ D₁ q w,
    smul_eq_of_piToGk_eq D₁ (F D₁) (g₁ := piRes K₁ D₁ q) (g₂ := 1) (by rw [hq, map_one]) w,
    one_smul]

end ConstPi

end Iut.Reconstruction.Thm19
