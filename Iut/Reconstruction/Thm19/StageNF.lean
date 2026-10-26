/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFDirectLimit

/-!
# [AbsTopIII] Thm 1.9 (d): the stages of the colimit as NF-curves

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178) takes the
colimit over the `V` "obtained by removing finite collections of NF-points from `Z ×_{k_Z} k′`".
The stages `StageIdx D` of `Thm19/NFDirectLimit.lean` allow any coordinate `t′`; here are the
ones whose cusps are NF-points, and the NF-model of such a stage:

* `exists_algEquiv_K₀`: a ring automorphism of `Ω` fixing `E` and `t′` is an automorphism over
  `E(t′)`;
* `mem_kbar_stage_iff`: `K̄ = k̄` inside `Ω` (`K / k` algebraic);
* **`mem_F_baseChange_stage_iff`**: the function field `F K̄` of `V_{K̄}` is that of `U_{k̄}`
  (inside `Ω`): a stage is an open of the base change, with the same geometric function field;
* `StageIdx.IsNF N s`: the cusps of the stage `s` (places `W ⊇ K` of `Ω` with `t′ ∉ W`) are
  NF-points;
* **`StageIdx.nfModel N s hs`**: the NF-model `N` of `U` is an NF-model of an NF-stage (same
  `F_NF`);
* `StageIdx.isNF_base`, `StageIdx.IsNF.mono_K`: `U_K` itself (coordinate `t`) is an NF-stage, and
  enlarging the field of constants keeps a coordinate NF;
* **`exists_nfStage_units`**: every `f ∈ K^×_{Z_NF}` is a unit on an NF-stage over every given
  finite extension `K₀ ⊆ K` (the coordinate `t + c₂ (f + c₁ f⁻¹)` of `exists_coordinate_V` has
  its poles at cusps of `U` and at zeros and poles of `f`, which are NF-points).
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

section Aut

variable {Ω : Type u} [Field Ω]

/-- **A ring automorphism of `Ω` fixing `E` and `t′` is an automorphism over `E(t′)`.** -/
lemma exists_algEquiv_K₀ {E : Type u} [Field E] [Algebra E Ω] {t' : Ω} (σ : Ω ≃+* Ω)
    (hE : ∀ c : E, σ (algebraMap E Ω c) = algebraMap E Ω c) (ht : σ t' = t') :
    ∃ σ' : Ω ≃ₐ[K₀ E t'] Ω, ∀ x, σ' x = σ x := by
  let h' : Ω ≃ₐ[E] Ω := AlgEquiv.ofRingEquiv (f := σ) fun c => hE c
  have hle : K₀ E t' ≤ IntermediateField.fixedField (Subgroup.zpowers h') := by
    rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
    intro g hg
    have ht' : h' ∈ MulAction.stabilizer (Ω ≃ₐ[E] Ω) t' := ht
    exact (Subgroup.zpowers_le.2 ht') hg
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => ?_, fun _ => rfl⟩
  exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) h' (Subgroup.mem_zpowers h')

end Aut

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω]

/-- `K̄ = k̄` inside `Ω` for an algebraic extension `K / k`. -/
lemma mem_kbar_stage_iff (K : IntermediateField k Ω) [Algebra.IsAlgebraic k K] {x : Ω} :
    x ∈ kbar K Ω ↔ x ∈ kbar k Ω := by
  constructor
  · intro hx
    have h1 : IsAlgebraic K x := mem_algebraicClosure_iff.1 hx
    haveI : Algebra.IsAlgebraic k K := inferInstance
    exact mem_algebraicClosure_iff.2 (h1.restrictScalars k)
  · intro hx
    exact mem_algebraicClosure_iff.2
      ((mem_algebraicClosure_iff.1 hx).isIntegral.tower_top (A := K)).isAlgebraic

/-- An element of `Gal(Ω / k̄(t))` in `H` fixes the function field `L_K` of `U_K`. -/
lemma fixes_L_constExt_of_mem [hH : Fact (D.H ≤ D.HL)] (K : IntermediateField k Ω)
    [Algebra.IsAlgebraic k K] (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω) (hσ : resK₀ k t σ ∈ D.H) {x : Ω}
    (hx : x ∈ (constExt K D).L) : σ x = x := by
  rw [mem_L_constExt_iff] at hx
  refine hx (resK₀ k t σ) (hH.out hσ) fun c => ?_
  have hc : algebraMap K Ω c ∈ kbar k Ω :=
    (mem_kbar_stage_iff K).1 (mem_algebraicClosure_iff.2 (isAlgebraic_algebraMap c))
  exact σ.commutes ⟨_, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, hc⟩⟩

/-- **The geometric function field of a stage is that of `U`**: `F K̄` of `V ⊆ U_K` equals `F k̄`
of `U` inside `Ω`. -/
theorem mem_F_baseChange_stage_iff [hH : Fact (D.H ≤ D.HL)] (s : StageIdx D) {x : Ω} :
    x ∈ F (baseChange s.data) ↔ x ∈ F (baseChange D) := by
  constructor
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    have hσ' : resK₀ k t σ ∈ D.H := (mem_baseChange_H D).1 hσ
    obtain ⟨σ', hσ'e⟩ := exists_algEquiv_K₀ (E := kbar s.K Ω) (t' := s.t')
      (σ : Ω ≃ₐ[K₀ (kbar k Ω) t] Ω).toRingEquiv (fun c => by
        have hc : (c : Ω) ∈ kbar k Ω := (mem_kbar_stage_iff s.K).1 c.2
        exact σ.commutes ⟨_, (K₀ (kbar k Ω) t).algebraMap_mem ⟨_, hc⟩⟩)
      (fixes_L_constExt_of_mem s.K σ hσ' s.ht')
    have hmem : σ' ∈ (baseChange s.data).H := by
      rw [mem_baseChange_H]
      change resK₀ s.K s.t' σ' ∈ (extendK₀ (constExt s.K D).L s.ht').fixingSubgroup
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      change σ' y = y
      rw [hσ'e]
      exact fixes_L_constExt_of_mem s.K σ hσ' hy
    have := hx σ' hmem
    rw [hσ'e] at this
    exact this
  · intro hx
    rw [IntermediateField.mem_fixedField_iff] at hx ⊢
    intro σ hσ
    have hσ' : resK₀ s.K s.t' σ ∈ (extendK₀ (constExt s.K D).L s.ht').fixingSubgroup :=
      (mem_baseChange_H s.data).1 hσ
    -- `σ` fixes `k̄`, `t` and the function field `L` of `U`
    have hfixL : ∀ y ∈ (constExt s.K D).L, σ y = y := fun y hy =>
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ' y hy
    obtain ⟨σ₀, hσ₀e⟩ := exists_algEquiv_K₀ (E := kbar k Ω) (t' := t)
      (σ : Ω ≃ₐ[K₀ (kbar s.K Ω) s.t'] Ω).toRingEquiv (fun c => by
        have hc : (c : Ω) ∈ kbar s.K Ω := (mem_kbar_stage_iff s.K).2 c.2
        exact σ.commutes ⟨_, (K₀ (kbar s.K Ω) s.t').algebraMap_mem ⟨_, hc⟩⟩)
      (hfixL t (t_mem_L_constExt D s.K))
    have hmem : σ₀ ∈ (baseChange D).H := by
      rw [mem_baseChange_H]
      have hHL : resK₀ k t σ₀ ∈ D.HL := by
        have e : (IntermediateField.fixedField D.HL).fixingSubgroup = D.HL :=
          InfiniteGalois.fixingSubgroup_fixedField ⟨D.HL, D.isClosed_HL⟩
        rw [← e, IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        change σ₀ y = y
        rw [hσ₀e]
        exact hfixL y (le_L_constExt D s.K ((IntermediateField.mem_fixedField_iff _ _).2
          fun τ hτ => (IntermediateField.mem_fixedField_iff _ _).1 hy τ (hH.out hτ)))
      exact D.le hHL
    have := hx σ₀ hmem
    rw [hσ₀e] at this
    exact this

variable (N : NFModel D)

namespace StageIdx

/-- **NF-stages**: the cusps of the stage `V` (the places `W ⊇ K` of `Ω` with `t′ ∉ W`) are
NF-points, i.e. `V` is obtained from `U_K` by removing NF-points ([AbsTopIII] Thm 1.9 (d)). -/
def IsNF (s : StageIdx D) : Prop :=
  ∀ W : ValuationSubring Ω, (∀ c : s.K, algebraMap s.K Ω c ∈ W) → s.t' ∉ W → N.IsNFPoint W

variable {N}

/-- **The NF-model of an NF-stage**: the same `F_NF`. -/
def nfModel [Fact (D.H ≤ D.HL)] (s : StageIdx D) (hs : s.IsNF N) :
    NFModel s.data where
  FNF := N.FNF
  algebraic_mem := N.algebraic_mem
  mem_F x hx := (mem_F_baseChange_stage_iff s).2 (N.mem_F x hx)
  isAlgebraic_of_mem_kbar x hx hxk :=
    N.isAlgebraic_of_mem_kbar x hx ((mem_kbar_stage_iff s.K).1 hxk)
  mem_closure x hx := by
    have h := N.mem_closure x ((mem_F_baseChange_stage_iff s).1 hx)
    have e : ((N.FNF : Set Ω) ∪ kbar k Ω) = ((N.FNF : Set Ω) ∪ kbar s.K Ω) := by
      ext y
      simp only [Set.mem_union, SetLike.mem_coe, mem_kbar_stage_iff s.K]
    rwa [e] at h
  cusp_nf := hs
  linearDisjoint := by
    have e : kbarNF s.K Ω = kbarNF k Ω := by
      ext y
      exact mem_kbar_stage_iff s.K
    rw [e]
    exact N.linearDisjoint

@[simp] lemma nfModel_FNF [Fact (D.H ≤ D.HL)] (s : StageIdx D) (hs : s.IsNF N) :
    (s.nfModel hs).FNF = N.FNF := rfl

lemma nfModel_isNFPoint_iff [Fact (D.H ≤ D.HL)] (s : StageIdx D) (hs : s.IsNF N)
    (W : ValuationSubring Ω) : (s.nfModel hs).IsNFPoint W ↔ N.IsNFPoint W := Iff.rfl

/-- Enlarging the field of constants keeps the cusps NF. -/
lemma IsNF.of_le {s s' : StageIdx D} (hs : s.IsNF N) (hK : s.K ≤ s'.K) (ht : s'.t' = s.t') :
    s'.IsNF N := fun W hW htW =>
  hs W (fun c => hW ⟨c, hK c.2⟩) (ht ▸ htW)

end StageIdx

variable (D) in
/-- `U_K` itself (coordinate `t`) as a stage. -/
def stageOfK (K : IntermediateField k Ω) [FiniteDimensional k K] : StageIdx D where
  K := K
  t' := t
  ht' := t_mem_L_constExt D K
  htr' := transcendental_K D
  htV := self_mem_chartRing K t

/-- **`U_K` is an NF-stage**: its cusps lie over cusps of `U`. -/
lemma isNF_stageOfK (K : IntermediateField k Ω) [FiniteDimensional k K] :
    (stageOfK D K).IsNF N := fun W hW ht =>
  N.cusp_nf W (fun c => hW (algebraMap k K c)) ht

lemma stageOfK_le_iff {K : IntermediateField k Ω} [FiniteDimensional k K] (s : StageIdx D) :
    stageOfK D K ≤ s ↔ K ≤ s.K := ⟨fun h => h.1, fun h => ⟨h, s.htV⟩⟩

/-! ### Cofinality of the NF-stages -/

section Coord

variable {k' : Type u} [Field k'] [Algebra k' Ω] {t₀ : Ω} (D' : Pi1.Orbifold.GaloisData k' t₀)
  [CharZero k'] [IsGalois (K₀ k' t₀) Ω]

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **`exists_coordinate_V` with the poles of the coordinate**: for a unit `f` there is a
coordinate `t′` on whose open `t`, `f`, `f⁻¹` are regular, and which is itself regular wherever
`t`, `f` and `f⁻¹` are (`t′ = t + c₂ (f + c₁ f⁻¹)`): the cusps of the open of `t′` are cusps of
`U` or zeros or poles of `f`. -/
theorem exists_coordinate_V_rev (f : (F D')ˣ) :
    ∃ t' : Ω, t' ∈ D'.L ∧ Transcendental k' t' ∧ t₀ ∈ chartRing k' t' ∧
      ((f : F D') : Ω) ∈ chartRing k' t' ∧ (((f⁻¹ : (F D')ˣ) : F D') : Ω) ∈ chartRing k' t' ∧
      ∀ W : ValuationSubring Ω, (∀ c : k', algebraMap k' Ω c ∈ W) → t₀ ∈ W →
        ((f : F D') : Ω) ∈ W → (((f⁻¹ : (F D')ˣ) : F D') : Ω) ∈ W → t' ∈ W := by
  obtain ⟨c₁, h₁⟩ := exists_smul_add_mem_imp D' (f : F D') ((f⁻¹ : (F D')ˣ) : F D')
  obtain ⟨c₂, h₂⟩ := exists_smul_add_mem_imp D' (tF D')
    ((f : F D') + algebraMap k' (F D') c₁ * ((f⁻¹ : (F D')ˣ) : F D'))
  set z : F D' := tF D' + algebraMap k' (F D') c₂ *
    ((f : F D') + algebraMap k' (F D') c₁ * ((f⁻¹ : (F D')ˣ) : F D')) with hz
  have key : ∀ W : ValuationSubring Ω, (∀ c : k', algebraMap k' Ω c ∈ W) → (z : Ω) ∈ W →
      t₀ ∈ W ∧ ((f : F D') : Ω) ∈ W ∧ (((f⁻¹ : (F D')ˣ) : F D') : Ω) ∈ W := by
    intro W hk hW
    obtain ⟨ht, hz₁⟩ := h₂ W hk hW
    obtain ⟨hf, hf'⟩ := h₁ W hk hz₁
    exact ⟨ht, hf, hf'⟩
  have htr' : Transcendental k' (z : Ω) := by
    intro halg
    apply D'.transcendental
    have hall : ∀ W : ValuationSubring Ω, (∀ c : k', algebraMap k' Ω c ∈ W) → t₀ ∈ W :=
      fun W hk => (key W hk (KummerTheory.Curve.mem_of_isIntegral hk halg.isIntegral)).1
    have hmem : t₀ ∈ (integralClosure k' Ω).toSubring := by
      rw [Subring.eq_iInf_of_isIntegrallyClosedIn (R := (integralClosure k' Ω).toSubring),
        Subring.mem_iInf]
      intro V
      exact hall V.1 fun c => V.2 (Subalgebra.algebraMap_mem _ c)
    exact ((mem_integralClosure_iff k' Ω).1 hmem).isAlgebraic
  refine ⟨z, mem_L_of_mem_F_shrink D' z.2, htr', ?_, ?_, ?_, ?_⟩
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).1
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).2.1
  · exact mem_chartRing_of_forall fun W hk hW => (key W hk hW).2.2
  · intro W hk ht hf hf'
    have hc : ∀ c : k', ((algebraMap k' (F D') c : F D') : Ω) ∈ W := fun c => by
      have e : algebraMap k' Ω c = ((algebraMap k' (F D') c : F D') : Ω) :=
        IsScalarTower.algebraMap_apply k' (F D') Ω c
      rw [← e]
      exact hk c
    exact add_mem ht (mul_mem (hc c₂) (add_mem hf (mul_mem (hc c₁) hf')))

end Coord

/-- Elements of the function field `L` are in `F` (no orbifold points). -/
lemma mem_F_of_mem_L {k' : Type u} [Field k'] [Algebra k' Ω] {t₀ : Ω}
    (E : Pi1.Orbifold.GaloisData k' t₀) (hE : E.H ≤ E.HL) {x : Ω} (hx : x ∈ E.L) : x ∈ F E := by
  rw [IntermediateField.mem_fixedField_iff]
  exact fun σ hσ => (IntermediateField.mem_fixedField_iff _ _).1 hx σ (hE hσ)

variable [hH : Fact (D.H ≤ D.HL)]
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

include hkF in
/-- **Cofinality of the NF-stages**: every nonzero NF-rational function `f` is a unit on an
NF-stage whose field of constants contains a given finite extension `K₀` of `k`. -/
theorem exists_nfStage_units (K₀' : IntermediateField k Ω) [FiniteDimensional k K₀']
    {f : Ω} (hf : f ∈ N.FNF) (hf0 : f ≠ 0) :
    ∃ s : StageIdx D, s.IsNF N ∧ K₀' ≤ s.K ∧
      ∃ v : US D s, (((v : (F s.data)ˣ) : F s.data) : Ω) = f := by
  obtain ⟨K, hK, hfK⟩ := exists_finite_mem_F_constExt D hkF (N.mem_F f hf)
  set K' : IntermediateField k Ω := K ⊔ K₀' with hK'
  have hfK' : f ∈ F (constExt K' D) :=
    mem_F_of_mem_L _ (constExt_H_le D hH.out K')
      (L_constExt_mono D le_sup_left (F_constExt_le_L D K hfK))
  have hne : (⟨f, hfK'⟩ : F (constExt K' D)) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  set fu : (F (constExt K' D))ˣ := Units.mk0 _ hne with hfu
  obtain ⟨t', ht'L, htr', htV, hf1, hf2, hrev⟩ := exists_coordinate_V_rev (constExt K' D) fu
  obtain ⟨v, hv⟩ := exists_units_V ht'L htr' fu hf1 hf2
  refine ⟨⟨K', t', ht'L, htr', htV⟩, ?_, le_sup_right, v, hv⟩
  intro W hW ht'W
  by_contra hNF
  apply ht'W
  have hk : ∀ c : k, algebraMap k Ω c ∈ W := fun c => hW (algebraMap k K' c)
  refine hrev W hW ?_ ?_ ?_
  · by_contra ht
    exact hNF (N.cusp_nf W hk ht)
  · by_contra hfW
    exact hNF ⟨f, hf, hfW⟩
  · by_contra hfW
    refine hNF ⟨f⁻¹, N.FNF.inv_mem hf, ?_⟩
    have e : (((fu⁻¹ : (F (constExt K' D))ˣ) : F (constExt K' D)) : Ω) = f⁻¹ := by
      rw [Units.val_inv_eq_inv_val, hfu, Units.val_mk0]
      rfl
    rwa [e] at hfW

end Iut.Reconstruction.Thm19
