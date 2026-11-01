/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ResIso
import Iut.Reconstruction.Thm19.ConstInertia

/-!
# `ker(res)` and `(k^×)^∧` along isomorphisms preserving cuspidal inertia (MR9 item 4, step 2)

[AbsTopIII] Prop 1.6 (iii) (`Topics in Absolute Anabelian Geometry III.txt` l.2001–2012): the
restriction to the inertia groups of the cusps gives the exact sequence
`1 → (k^×)^∧ → H¹(Π_U, M_X) → ⊕_{x∈S} Ẑ`. curves-jacobian records the residues at all places
`W ⊇ k` (`res`, `ker_res`); at the places over `U` they vanish. For the functoriality of
[AbsTopIII] Thm 1.9 (c), (d) the kernel must be carried along the stage isomorphisms. Generically,
in the Galois models:

* `evalTriv_one`, **`res_eq_one_of_mem`** (residues at places over `U` vanish: their inertia lies in
  the kernel of `H ↠ Π_U`), **`mem_ker_res_iff`** (`η ∈ ker res` iff the residues at the cusps
  vanish);
* `MapsCuspInertia f`: `f : Π_U → Π_{U'}` carries every cuspidal inertia element into a cuspidal
  inertia group;
* **`exists_res_h1Congr`**: then every residue at a cusp is, after `χ`, a residue at a cusp of the
  transported class;
* **`h1Congr_mem_ker_res_iff`**, **`h1Congr_mem_range_constMapZHat_iff`**: if `e` and `e⁻¹`
  preserve cuspidal inertia, `h1Congr e χ` matches `ker res` and `(k^×)^∧`;
* **`mapsCuspInertia_constIso`**, `mapsCuspInertia_constIso_symm`: the restriction `constIso` to
  extensions of the field of constants preserves cuspidal inertia if `e` does (`ConstInertia`).
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer Pi1.Orbifold

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section EvalOne

variable {P M : Type*} [Group P] [TopologicalSpace P] [CommGroup M] [TopologicalSpace M]
  [IsTopologicalGroup M] [MulDistribMulAction P M]

/-- A cocycle is trivial at `1`. -/
lemma evalTriv_one (h : ∀ m : M, (1 : P) • m = m) (x : ContH1 P M) :
    ContH1.evalTriv (1 : P) h x = 1 := by
  have h1 : ContH1.evalTriv (1 : P) h x =
      ContH1.evalTriv (1 : P) h x * ContH1.evalTriv (1 : P) h x :=
    (evalTriv_congr_elem (one_mul (1 : P)).symm h (by rw [one_mul]; exact h) x).trans
      (ContH1.evalTriv_mul h h _ x)
  exact mul_left_cancel (h1.symm.trans (mul_one _).symm)

end EvalOne

section Res

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

/-- **Residues at places over `U` vanish**: the inertia at a place containing `t` lies in the
kernel of `H ↠ Π_U` (for `H ≤ H_L`). -/
lemma res_eq_one_of_mem (hH : D.H ≤ D.HL) (η : ContH1 (Pi D) (ZHatOne (F D) Ω))
    (p : InertiaIndex D) (ht : t ∈ p.1.1) : res D η p = 1 := by
  have h1 : ((p.1.2 : D.H) : Pi D) = 1 :=
    (QuotientGroup.eq_one_iff _).2
      (D.mem_kernel_of_mem_S p.1.2 ⟨hH p.1.2.2, p.1.1, p.2.1, ht, p.2.2⟩)
  exact (res_apply D η p).trans ((evalTriv_congr_elem h1 _ (fun m => one_smul _ m) η).trans
    (evalTriv_one _ η))

/-- **`η ∈ ker res` iff the residues at the cusps vanish.** -/
lemma mem_ker_res_iff (hH : D.H ≤ D.HL) (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    η ∈ (res D).ker ↔ ∀ p : InertiaIndex D, t ∉ p.1.1 → res D η p = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h p _
    exact congrFun h p
  · intro h
    funext p
    by_cases ht : t ∈ p.1.1
    · exact res_eq_one_of_mem hH η p ht
    · exact h p ht

variable {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']

/-- `f : Π_U → Π_{U'}` carries every cuspidal inertia element into a cuspidal inertia group. -/
def MapsCuspInertia (f : Pi D → Pi D') : Prop :=
  ∀ W ∈ CuspW (k := k) (t := t), ∀ σ ∈ inertiaH D W,
    ∃ W' ∈ CuspW (k := k') (t := t'), ∃ σ' ∈ inertiaH D' W', f (σ : Pi D) = (σ' : Pi D')

variable (e : Pi D ≃ₜ* Pi D') (χ : ZHatOne (F D) Ω ≃ₜ* ZHatOne (F D') Ω')
  (hχ : ∀ p z, χ (p • z) = e p • χ z)

/-- **Residues along an isomorphism preserving cuspidal inertia**: every residue at a cusp is,
after `χ`, a residue at a cusp of the transported class. -/
theorem exists_res_h1Congr (hE : MapsCuspInertia ⇑e) (p : InertiaIndex D) (hp : t ∉ p.1.1) :
    ∃ p' : InertiaIndex D', t' ∉ p'.1.1 ∧
      ∀ η, res D' (h1Congr e χ hχ η) p' = χ (res D η p) := by
  obtain ⟨W', hW', σ', hσ', heq⟩ := hE p.1.1 ⟨p.2.1, hp⟩ p.1.2 p.2.2
  refine ⟨⟨(W', σ'), hW'.1, hσ'⟩, hW'.2, fun η => ?_⟩
  exact (res_apply _ _ _).trans ((evalTriv_congr_elem heq.symm
    (pi_inertia_smul_zHatOne hW'.1 hσ' _)
    (smul_eq_self_of_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _)) _).trans
    ((evalTriv_h1Congr _ χ hχ (pi_inertia_smul_zHatOne p.2.1 p.2.2 _) η).trans
      (congrArg χ (res_apply _ η p).symm)))

set_option maxHeartbeats 800000 in
-- the quotients `Π_U` unify slowly
/-- **`ker res` corresponds under `h1Congr e χ`** if `e` and `e⁻¹` preserve cuspidal inertia. -/
theorem h1Congr_mem_ker_res_iff (hH : D.H ≤ D.HL) (hH' : D'.H ≤ D'.HL)
    (hE : MapsCuspInertia ⇑e) (hE' : MapsCuspInertia ⇑e.symm)
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    h1Congr e χ hχ η ∈ (res D').ker ↔ η ∈ (res D).ker := by
  rw [mem_ker_res_iff hH', mem_ker_res_iff hH]
  constructor
  · intro h p hp
    obtain ⟨p', hp', hres⟩ := exists_res_h1Congr e χ hχ hE p hp
    exact (map_eq_one_iff χ χ.injective).1 ((hres η).symm.trans (h p' hp'))
  · intro h p' hp'
    obtain ⟨W, hW, σ, hσ, heq⟩ := hE' p'.1.1 ⟨p'.2.1, hp'⟩ p'.1.2 p'.2.2
    have heq' : ((p'.1.2 : D'.H) : Pi D') = e (σ : Pi D) := by
      rw [← heq, ContinuousMulEquiv.apply_symm_apply]
    have hσ1 := pi_inertia_smul_zHatOne (D := D) hW.1 hσ (F D)
    exact (res_apply _ _ _).trans ((evalTriv_congr_elem heq'
      (pi_inertia_smul_zHatOne p'.2.1 p'.2.2 _) (smul_eq_self_of_h1Congr _ χ hχ hσ1) _).trans
      ((evalTriv_h1Congr _ χ hχ hσ1 η).trans ((congrArg χ ((res_apply D η
        ⟨(W, σ), hW.1, hσ⟩).symm.trans (h _ hW.2))).trans (map_one χ))))

/-- **`(k^×)^∧` corresponds under `h1Congr e χ`** ([AbsTopIII] Prop 1.6 (iii), `ker_res` on both
sides) if `e` and `e⁻¹` preserve cuspidal inertia. -/
theorem h1Congr_mem_range_constMapZHat_iff (hH : D.H ≤ D.HL) (hH' : D'.H ≤ D'.HL)
    (hE : MapsCuspInertia ⇑e) (hE' : MapsCuspInertia ⇑e.symm)
    (hJ : IsKummerFaithfulJac D)
    (hk : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (hJ' : IsKummerFaithfulJac D')
    (hk' : ∀ x : F D', IsAlgebraic k' x → x ∈ Set.range (algebraMap k' (F D')))
    (η : ContH1 (Pi D) (ZHatOne (F D) Ω)) :
    h1Congr e χ hχ η ∈ (constMapZHat D').range ↔ η ∈ (constMapZHat D).range := by
  rw [← ker_res hJ' hk', ← ker_res hJ hk]
  exact h1Congr_mem_ker_res_iff e χ hχ hH hH' hE hE' η

end Res

section Const

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  {k' Ω' : Type u} [Field k'] [Field Ω'] [Algebra k' Ω'] {t' : Ω'}
  {D' : GaloisData k' t'} [CharZero k'] [IsGalois (K₀ k' t') Ω'] [IsAlgClosed Ω']
  (e : Pi D ≃ₜ* Pi D') (ψ : Gk k Ω ≃* Gk k' Ω')
  (he : ∀ p, piToGk D' (e p) = ψ (piToGk D p)) (hs : Function.Surjective (piToGk D))
  (K : IntermediateField k Ω) [FiniteDimensional k K] [FiniteDimensional k' (constField ψ K)]

lemma piRes_constIso_symm (q : Pi (constExt (constField ψ K) D')) :
    piRes K D ((constIso e ψ he hs K).symm q) = e.symm (piRes (constField ψ K) D' q) :=
  piRes_constMulEquiv_symm e ψ he hs K q

omit [FiniteDimensional k K] in
lemma mem_CuspW_of_constExt {W : ValuationSubring Ω} (hW : W ∈ CuspW (k := K) (t := t)) :
    W ∈ CuspW (k := k) (t := t) := by
  refine ⟨fun c => ?_, hW.2⟩
  have h := hW.1 (algebraMap k K c)
  rwa [← IsScalarTower.algebraMap_apply] at h

omit [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω] in
lemma mem_CuspW_constExt (K₁ : IntermediateField k Ω) [Algebra.IsAlgebraic k K₁]
    {W : ValuationSubring Ω} (hW : W ∈ CuspW (k := k) (t := t)) :
    W ∈ CuspW (k := K₁) (t := t) :=
  ⟨fun c => algebraMap_mem_A_constExt hW.1 c, hW.2⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`constIso` preserves cuspidal inertia if `e` does.** -/
theorem mapsCuspInertia_constIso (h : MapsCuspInertia ⇑e) :
    MapsCuspInertia ⇑(constIso e ψ he hs K) := by
  intro W hW σ hσ
  obtain ⟨W', hW', σ₁, hσ₁, heq⟩ := h W (mem_CuspW_of_constExt K hW) (hRes K D σ)
    (hRes_mem_inertiaH hσ)
  obtain ⟨σ', hσ', hσ'eq⟩ := exists_hRes_eq_of_mem_inertiaH (K₁ := constField ψ K) hW'.1 hσ₁
  refine ⟨W', mem_CuspW_constExt (constField ψ K) hW', σ', hσ', piRes_injective D' ?_⟩
  rw [piRes_constIso, piRes_mk, piRes_mk, hσ'eq]
  exact heq

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`constIso⁻¹` preserves cuspidal inertia if `e⁻¹` does.** -/
theorem mapsCuspInertia_constIso_symm (h : MapsCuspInertia ⇑e.symm) :
    MapsCuspInertia ⇑(constIso e ψ he hs K).symm := by
  intro W hW σ hσ
  obtain ⟨W', hW', σ₁, hσ₁, heq⟩ := h W (mem_CuspW_of_constExt (constField ψ K) hW)
    (hRes (constField ψ K) D' σ) (hRes_mem_inertiaH hσ)
  obtain ⟨σ', hσ', hσ'eq⟩ := exists_hRes_eq_of_mem_inertiaH (K₁ := K) hW'.1 hσ₁
  refine ⟨W', mem_CuspW_constExt K hW', σ', hσ', piRes_injective D ?_⟩
  rw [piRes_constIso_symm, piRes_mk, piRes_mk, hσ'eq]
  exact heq

end Const

end Iut.Reconstruction.Thm19
