/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.RecFunctionField
import Iut.Reconstruction.Thm19.StageJac
import Iut.Reconstruction.Thm19.NFKummer

/-!
# [AbsTopIII] Thm 1.9 (d): `K^×_{Z_NF}` inside `lim→_V H¹(Π_V, Ẑ(1))` by the tests of Prop 1.8

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178)
constructs `k̄_NF^× ⊆ K^×_{Z_NF} ↪ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` "via the subgroups of (c) and the
characterizations of Kummer classes of nonconstant NF-rational functions and NF-constants given in
Proposition 1.8, (i), (ii)". `Thm19/RecFunctionField.lean` defines `kummerNFRange` as the image of
the Kummer map. Here that image is characterised inside `H1Lim D` by the two tests of Prop 1.8
(`Thm19/NFKummer.lean`) at the NF-stages (`Thm19/StageNF.lean`), i.e. by `P_V`, the restrictions
`s_x^*` to decomposition groups of NF-points, `(K^×)^∧` and the transition maps only:

* `IsNFStageTest N ξ`: `ξ = [V, η]` for an NF-stage `V`, `η ∈ P_V`, and `η` passes the test of
  Prop 1.8 (i) at `V`;
* `IsNFConstTest`, `IsNFStageConstTest N ξ`: `ξ = [V, c]` for `c ∈ (K^×)^∧` passing the test of
  Prop 1.8 (ii) at an NF-stage `V` carrying a nonconstant NF-rational unit;
* **`exists_kummerNF_not_isAlgebraic_iff`**: the classes of the nonconstant NF-rational functions
  are those passing the test (i) at some NF-stage. Here the "positive multiple" of Prop 1.8 (i)
  disappears in the colimit: if `η^M = κ_V(w)`, then after the stage `V′` over `K(b^{1/M})`
  (`exists_resKH1_eq_kummerMapZHat` on the stage, transported to `V′`), `[V, η] = [V′, κ(v)]`
  with `v^M = w`, and `v` is an NF-rational function (`NFModel.unitsDescend`: `l v ∈ F_NF` for a
  scalar `l ∈ k̄`, and `l^M ∈ F_NF ∩ k̄ = k̄_NF`);
* **`exists_kummerNF_isAlgebraic_iff`**: the classes of the NF-constants `k̄_NF^×` are those
  passing the test (ii);
* **`mem_kummerNFRange_iff`**: `ξ ∈ kummerNFRange ↔ IsNFStageTest ξ ∨ IsNFStageConstTest ξ`;
* `mem_kummerNFRange_iff_curve`: the same for the Galois model of a curve with a rational point
  over a number field, with no hypothesis (`isKummerFaithfulJac_stage_curve_numberField`).

The hypothesis `hJ : ∀ s, IsKummerFaithfulJac s.data` of the generic statements is the Jacobian
input of Prop 1.6 (iii) at the stages; it is discharged for curves over number fields.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer IsLocalRing

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

open CurvesJacobian StageIdx

set_option linter.unusedSectionVars false

attribute [local instance] isAlgClosed_algebraicClosure isFunctionField_fnf
  CurvesJacobian.isFunctionField_F

section Generic

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [IsGalois (K₀ k t) Ω] [CharZero k] [CharZero Ω]
  [IsAlgClosed Ω]

/-- **The test of [AbsTopIII] Prop 1.8 (ii)** for `c ∈ (k^×)^∧`: `κ_U(f)|_x = c|_{G_{k_x}}` for
some nonconstant NF-rational unit `f` and some NF-point `x ∈ U(k_x)`, `[k_x : k] < ∞`. -/
def IsNFConstTest (N : NFModel D) (hHL : D.HL = D.H) (c : KummerCompletion k) : Prop :=
  ∃ f : units D, Transcendental k ((f : (F D)ˣ) : F D) ∧
    N.IsNFFunction ((f : (F D)ˣ) : F D) ∧
    ∃ (A : ValuationSubring Ω) (hk : ∀ c : k, algebraMap k Ω c ∈ A) (ht : t ∈ A),
      N.IsNFPoint A ∧
      letI := Decomposition.residueAlgebra A hk
      ∃ (_ : Algebra.IsIntegral k (ResidueField A))
        (_ : FiniteDimensional k (Decomposition.pointField (F D) A hk
          (Decomposition.residue_algebraMap_residueAlgebra A hk))),
        restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (kummerMapZHat D f) =
          restrictClosed D A hk (Decomposition.residue_algebraMap_residueAlgebra A hk) hHL ht
            (constMapZHat D c)

end Generic

section Rec

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  {D : Pi1.Orbifold.GaloisData k t} [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]
  [CharZero Ω] [hH : Fact (D.H ≤ D.HL)] [NumberField k] (N : NFModel D)
  (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))

/-- **The test of Prop 1.8 (i) at an NF-stage**: `ξ = [V, η]` with `V` an NF-stage, `η ∈ P_V`,
and `η` passing the test of [AbsTopIII] Prop 1.8 (i) at `V`. -/
def IsNFStageTest (ξ : H1Lim D) : Prop :=
  ∃ (s : StageIdx D) (hs : s.IsNF N) (η : H1S D s), η ∈ PU s.data ∧ H1Lim.mk s η = ξ ∧
    IsNFKummerTest (s.nfModel hs) rfl η

/-- **The test of Prop 1.8 (ii) at an NF-stage**: `ξ = [V, c]` with `V` an NF-stage carrying a
nonconstant NF-rational unit and `c ∈ (K^×)^∧` passing the test of [AbsTopIII] Prop 1.8 (ii). -/
def IsNFStageConstTest (ξ : H1Lim D) : Prop :=
  ∃ (s : StageIdx D) (hs : s.IsNF N) (c : KummerCompletion s.K),
    H1Lim.mk s (constMapZHat s.data c) = ξ ∧
    (∃ f₀ : US D s, Transcendental s.K ((f₀ : (F s.data)ˣ) : F s.data) ∧
      (s.nfModel hs).IsNFFunction ((f₀ : (F s.data)ˣ) : F s.data)) ∧
    IsNFConstTest (s.nfModel hs) rfl c

variable {N}

include hkF in
/-- **A unit of a stage lies in the field of constants iff it is an algebraic number** (`K` a
number field, algebraically closed in the function field of the stage). -/
lemma mem_range_constUnit_iff (s : StageIdx D) (v : US D s) :
    v ∈ Set.range (constUnit s.data) ↔
      IsAlgebraic ℚ (((v : (F s.data)ˣ) : F s.data) : Ω) := by
  haveI : NumberField s.K := NumberField.of_module_finite k s.K
  constructor
  · rintro ⟨b, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b : s.K)).algebraMap
  · intro h
    haveI : IsScalarTower s.K (F s.data) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hK : IsAlgebraic s.K (((v : (F s.data)ˣ) : F s.data) : Ω) :=
      h.extendScalars (algebraMap ℚ s.K).injective
    have hF : IsAlgebraic s.K ((v : (F s.data)ˣ) : F s.data) :=
      (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom s.K (F s.data) Ω)
        (algebraMap (F s.data) Ω).injective).1 hK
    obtain ⟨c, hc⟩ := mem_range_of_isAlgebraic_stage hH.out hkF _ hF
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact (v : (F s.data)ˣ).ne_zero hc.symm
    exact ⟨Units.mk0 c hc0, Subtype.ext (Units.ext hc)⟩

/-- The class `[V, η]` equals `[V′, η|_{V′}]` for `V ≤ V′`. -/
lemma H1Lim.mk_eq_mk_resS {s s' : StageIdx D} (h : s ≤ s') (η : H1S D s) :
    H1Lim.mk s η = H1Lim.mk s' (resS h η) :=
  (DirectLimit.mk_apply (f := fun _ _ h => resS (D := D) h) s s' η h).symm

/-- The stage `V` over the larger field of constants `K′ ⊇ K` (same coordinate). -/
def StageIdx.extend (s : StageIdx D) (K' : IntermediateField k Ω) [FiniteDimensional k K']
    (hK : s.K ≤ K') : StageIdx D where
  K := K'
  t' := s.t'
  ht' := L_constExt_mono D hK s.ht'
  htr' := fun h => s.htr' (by
    have h' : IsAlgebraic k s.t' := (h.restrictScalars k)
    exact h'.extendScalars (algebraMap k s.K).injective)
  htV := mem_chartRing_trans hK s.htV (self_mem_chartRing _ _)

lemma StageIdx.le_extend (s : StageIdx D) (K' : IntermediateField k Ω) [FiniteDimensional k K']
    (hK : s.K ≤ K') : s ≤ s.extend K' hK :=
  ⟨hK, self_mem_chartRing _ _⟩

section Transfer

variable (s : StageIdx D) (K' : IntermediateField k Ω) [FiniteDimensional k K'] (hK : s.K ≤ K')

/-- `K′` as an extension of the field of constants `K` of the stage. -/
abbrev extK : IntermediateField s.K Ω := IntermediateField.extendScalars hK

instance algebraic_extK : Algebra.IsAlgebraic s.K (extK s K' hK) := by
  refine ⟨fun x => ?_⟩
  have hx : (x : Ω) ∈ K' := x.2
  have h1 : IsIntegral k (x : Ω) := by
    have := (Algebra.IsIntegral.isIntegral (R := k) (⟨(x : Ω), hx⟩ : K'))
    exact this.map K'.val
  have h2 : IsIntegral s.K (x : Ω) := h1.tower_top
  exact (IntermediateField.isIntegral_iff.2 h2).isAlgebraic

/-- Places of `Ω` centred on the stage over `K′` are centred on `V_{K′}` (as a base change of
the stage `V`). -/
lemma hW_extK (W : ValuationSubring Ω)
    (hK' : ∀ c : (s.extend K' hK).K, algebraMap (s.extend K' hK).K Ω c ∈ W)
    (hW : (s.extend K' hK).t' ∈ W) :
    (∀ c : extK s K' hK, algebraMap (extK s K' hK) Ω c ∈ W) ∧ s.t' ∈ W :=
  ⟨fun c => hK' ⟨c, c.2⟩, hW⟩

/-- The function field of `V_{K′}` (base change of the stage `V`) lies in that of the stage over
`K′`. -/
lemma F_extK_le {x : Ω} (hx : x ∈ F (constExt (extK s K' hK) s.data)) :
    x ∈ F (s.extend K' hK).data := by
  haveI : IsGalois (K₀ K' (s.extend K' hK).t') Ω := StageIdx.isGalois (s.extend K' hK)
  refine (mem_F_stage_iff D K' (s.extend K' hK).ht' (s.extend K' hK).htr').2 ?_
  rw [mem_L_constExt_iff]
  intro σ hσ hK'
  have hfixL : ∀ y ∈ (constExt K' D).L, σ y = y := fun y hy =>
    (mem_L_constExt_iff D K').1 hy σ hσ hK'
  obtain ⟨σ', hσ'⟩ := exists_algEquiv_K₀ (E := extK s K' hK) (t' := s.t') σ.toRingEquiv
    (fun c => hK' ⟨c, c.2⟩) (hfixL _ (s.extend K' hK).ht')
  have hmem : σ' ∈ (constExt (extK s K' hK) s.data).H := by
    refine (mem_constExt_H s.data).2 ?_
    change resK s.K (extK s K' hK) s.t' σ' ∈ (extendK₀ (constExt s.K D).L s.ht').fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    change σ' y = y
    rw [hσ']
    exact hfixL y (L_constExt_mono D hK hy)
  have := (IntermediateField.mem_fixedField_iff _ _).1 hx σ' hmem
  exact ((hσ' x).symm.trans this :)

lemma constExt_extK_H_le :
    (constExt (extK s K' hK) s.data).H ≤ (constExt (extK s K' hK) s.data).HL :=
  constExt_H_le s.data le_rfl (extK s K' hK)

set_option maxHeartbeats 4000000 in
-- `ContH1` terms over three Galois models unify slowly
/-- **The transition `V → V_{K′}` followed by `V_{K′} → (stage over K′)` is `resS`.** -/
theorem resS_extend_eq (η : H1S D s) :
    resS (s.le_extend K' hK) η =
      resT (constExt (extK s K' hK) s.data) (s.extend K' hK).data
        (fun _ hx => F_extK_le s K' hK hx) (hW_extK s K' hK) (constExt_extK_H_le s K' hK)
        (resKH1 (extK s K' hK) s.data η) := by
  rw [resKH1_eq_resT s.data le_rfl (extK s K' hK), resT_resT]
  rfl

lemma coe_unitsT_extend (v : units (constExt (extK s K' hK) s.data)) :
    ((((unitsT (constExt (extK s K' hK) s.data) (s.extend K' hK).data
        (fun _ hx => F_extK_le s K' hK hx) (hW_extK s K' hK) v : US D (s.extend K' hK)) :
          (F (s.extend K' hK).data)ˣ) : F (s.extend K' hK).data) : Ω) =
      (((v : (F (constExt (extK s K' hK) s.data))ˣ) : F (constExt (extK s K' hK) s.data)) :
        Ω) :=
  coe_unitsT _ _ _ _ v

end Transfer

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **[AbsTopIII] Prop 1.8 (i) and Thm 1.9 (d) in the colimit**: the Kummer classes of the
nonconstant NF-rational functions in `lim→_V H¹(Π_V, Ẑ(1))` are exactly the classes passing the
test of Prop 1.8 (i) at some NF-stage. (`hJ`: Prop 1.6 (iii) at the stages, i.e.
`⋂_N N · J(K) = 0`; see `isKummerFaithfulJac_stage_curve_numberField`.) -/
theorem exists_kummerNF_not_isAlgebraic_iff (hJ : ∀ s : StageIdx D, IsKummerFaithfulJac s.data)
    (ξ : H1Lim D) :
    (∃ f : (fnf N)ˣ, ¬ IsAlgebraic ℚ ((f : fnf N) : Ω) ∧ kummerNF N hkF f = ξ) ↔
      IsNFStageTest N ξ := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨s, hs, -, v, hv⟩ := exists_nfStage_units N hkF ⊥ (f : fnf N).2
      (fun h => f.ne_zero (Subtype.ext h))
    haveI : NumberField s.K := NumberField.of_module_finite k s.K
    refine ⟨s, hs, kummerMapZHat s.data v, ⟨v, rfl⟩, (kummerNF_eq_mk N hkF f s v hv).symm, ?_⟩
    refine (isNFKummerTest_iff (N := s.nfModel hs) (hHL := rfl)
      (NumberField.isTorallyKummerFaithful s.K) (hJ s)
      (mem_range_of_isAlgebraic_stage hH.out hkF) _ ⟨v, rfl⟩).2
      ⟨1, one_pos, v, pow_one _, ?_, ?_⟩
    · rw [mem_range_constUnit_iff hkF s v, hv]
      exact hf
    · change _ ∈ N.FNF
      rw [hv]
      exact (f : fnf N).2
  · rintro ⟨s, hs, η, hη, rfl, htest⟩
    haveI : NumberField s.K := NumberField.of_module_finite k s.K
    have hkFs := mem_range_of_isAlgebraic_stage (D := D) (K := s.K) (ht' := s.ht')
      (htr' := s.htr') hH.out hkF
    obtain ⟨M, hM, w, hw, hwc, hwNF⟩ := (isNFKummerTest_iff (N := s.nfModel hs) (hHL := rfl)
      (NumberField.isTorallyKummerFaithful s.K) (hJ s) hkFs η hη).1 htest
    obtain ⟨u, b, -, hb⟩ := exists_resKH1_eq_kummerMapZHat (hJ s) hkFs hη hM hw
    -- an `M`-th root `β₀` of `b`, and the stage `V′` over `K′ = K(β₀)`
    obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap s.K Ω b) hM
    have hβint : IsIntegral k β₀ := by
      have h1 : IsIntegral k (algebraMap s.K Ω b) := by
        have := (Algebra.IsIntegral.isIntegral (R := k) (b : s.K))
        exact this.map (IsScalarTower.toAlgHom k s.K Ω)
      exact IsIntegral.of_pow hM (hβ₀ ▸ h1)
    haveI : FiniteDimensional k (IntermediateField.adjoin k {β₀}) :=
      IntermediateField.adjoin.finiteDimensional hβint
    set K' : IntermediateField k Ω := s.K ⊔ IntermediateField.adjoin k {β₀} with hK'
    have hK : s.K ≤ K' := le_sup_left
    have hβK' : β₀ ∈ K' :=
      (show IntermediateField.adjoin k {β₀} ≤ K' from le_sup_right)
        (IntermediateField.mem_adjoin_simple_self k β₀)
    have hβ0 : β₀ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne'] at hβ₀
      exact b.ne_zero ((algebraMap s.K Ω).injective (by rw [← hβ₀, map_zero]))
    let β : (extK s K' hK)ˣ := Units.mk0 ⟨β₀, hβK'⟩ (fun h => hβ0 (congrArg Subtype.val h))
    have hβ : β ^ M = Units.map (algebraMap s.K (extK s K' hK) : s.K →* extK s K' hK) b := by
      apply Units.ext
      apply Subtype.ext
      change β₀ ^ M = algebraMap s.K Ω b
      exact hβ₀
    obtain ⟨v, hv, hvM⟩ := hb (extK s K' hK) β hβ
    set s' := s.extend K' hK with hs'def
    have hs' : s'.IsNF N := hs.of_le hK rfl
    set v' : US D s' := unitsT (constExt (extK s K' hK) s.data) s'.data
      (fun _ hx => F_extK_le s K' hK hx) (hW_extK s K' hK) v with hv'def
    have hcoe : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) =
        (((v : (F (constExt (extK s K' hK) s.data))ˣ) :
          F (constExt (extK s K' hK) s.data)) : Ω) := coe_unitsT_extend s K' hK v
    have hvMΩ : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ^ M =
        (((w : (F s.data)ˣ) : F s.data) : Ω) := by
      rw [hcoe]
      have := congrArg (fun z : units (constExt (extK s K' hK) s.data) =>
        (((z : (F (constExt (extK s K' hK) s.data))ˣ) :
          F (constExt (extK s K' hK) s.data)) : Ω)) hvM
      simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, IntermediateField.coe_pow] at this
      rw [this]
      rfl
    have hw0 : (((w : (F s.data)ˣ) : F s.data) : Ω) ≠ 0 := fun h =>
      (w : (F s.data)ˣ).ne_zero (Subtype.ext h)
    have hv'0 : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ≠ 0 := fun h =>
      (v' : (F s'.data)ˣ).ne_zero (Subtype.ext h)
    -- `v′` is an NF-rational function
    have hv'NF : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ∈ N.FNF := by
      obtain ⟨l, hl0, hlk, hlv⟩ := (s'.nfModel hs').unitsDescend v'
      have hlv' : l * (((v' : (F s'.data)ˣ) : F s'.data) : Ω) ∈ N.FNF := hlv
      have hlM : l ^ M ∈ N.FNF := by
        have e : l ^ M = (l * (((v' : (F s'.data)ˣ) : F s'.data) : Ω)) ^ M /
            (((w : (F s.data)ˣ) : F s.data) : Ω) := by
          rw [mul_pow, hvMΩ, mul_div_assoc, div_self hw0, mul_one]
        rw [e]
        exact div_mem (pow_mem hlv' M) hwNF
      have hlk' : l ^ M ∈ kbar k Ω :=
        pow_mem ((mem_kbar_stage_iff s'.K).1 hlk) M
      have hlalg : IsAlgebraic ℚ l := IsAlgebraic.of_pow hM (N.isAlgebraic_of_mem_kbar _ hlM hlk')
      have hlF := N.algebraic_mem l hlalg
      have e : (((v' : (F s'.data)ˣ) : F s'.data) : Ω) =
          l⁻¹ * (l * (((v' : (F s'.data)ˣ) : F s'.data) : Ω)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hl0, one_mul]
      rw [e]
      exact mul_mem (N.FNF.inv_mem hlF) hlv'
    -- `v′` is not an algebraic number
    have hv'nc : ¬ IsAlgebraic ℚ (((v' : (F s'.data)ˣ) : F s'.data) : Ω) := by
      intro halg
      apply hwc
      rw [mem_range_constUnit_iff hkF s w, ← hvMΩ]
      exact halg.pow M
    let f : (fnf N)ˣ := Units.mk0 ⟨_, hv'NF⟩ (fun h => hv'0 (congrArg Subtype.val h))
    refine ⟨f, hv'nc, ?_⟩
    rw [kummerNF_eq_mk N hkF f s' v' rfl, H1Lim.mk_eq_mk_resS (s.le_extend K' hK) η,
      resS_extend_eq s K' hK η, hv, resT_kummerMapZHat]

set_option maxHeartbeats 4000000 in
-- `ContH1` and unit terms over the stages unify slowly
/-- **[AbsTopIII] Prop 1.8 (ii) and Thm 1.9 (d) in the colimit**: the Kummer classes of the
NF-constants `k̄_NF^×` in `lim→_V H¹(Π_V, Ẑ(1))` are exactly the classes passing the test of
Prop 1.8 (ii) at some NF-stage. -/
theorem exists_kummerNF_isAlgebraic_iff (ξ : H1Lim D) :
    (∃ f : (fnf N)ˣ, IsAlgebraic ℚ ((f : fnf N) : Ω) ∧ kummerNF N hkF f = ξ) ↔
      IsNFStageConstTest N ξ := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨y, hy, hyt⟩ := N.exists_transcendental
    have hfint : IsIntegral k ((f : fnf N) : Ω) :=
      (hf.extendScalars (algebraMap ℚ k).injective).isIntegral
    haveI : FiniteDimensional k (IntermediateField.adjoin k {((f : fnf N) : Ω)}) :=
      IntermediateField.adjoin.finiteDimensional hfint
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyt (isAlgebraic_zero)
    obtain ⟨s, hs, hK₀, v, hv⟩ := exists_nfStage_units N hkF
      (IntermediateField.adjoin k {((f : fnf N) : Ω)}) hy hy0
    haveI : NumberField s.K := NumberField.of_module_finite k s.K
    have hfK : ((f : fnf N) : Ω) ∈ s.K := hK₀ (IntermediateField.mem_adjoin_simple_self k _)
    have hf0 : ((f : fnf N) : Ω) ≠ 0 := fun h => f.ne_zero (Subtype.ext h)
    let b : s.Kˣ := Units.mk0 ⟨_, hfK⟩ (fun h => hf0 (congrArg Subtype.val h))
    have hbv : (((constUnit s.data b : (F s.data)ˣ) : F s.data) : Ω) = ((f : fnf N) : Ω) := rfl
    -- the nonconstant NF-rational unit `v` (the function `y`)
    have hvt : Transcendental s.K ((v : (F s.data)ˣ) : F s.data) := by
      intro halg
      apply hyt
      haveI : IsScalarTower s.K (F s.data) Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
      have h1 : IsAlgebraic s.K y := by
        rw [← hv]
        exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom s.K (F s.data) Ω)
          (algebraMap (F s.data) Ω).injective).2 halg
      have h2 : IsAlgebraic k y := h1.restrictScalars k
      exact isAlgebraic_algebraMap (⟨y, mem_algebraicClosure_iff.2 h2⟩ : kbar k Ω)
    have hvNF : (s.nfModel hs).IsNFFunction ((v : (F s.data)ˣ) : F s.data) := by
      change _ ∈ N.FNF
      rw [hv]
      exact hy
    refine ⟨s, hs, toKummerCompletion s.K b, ?_, ⟨v, hvt, hvNF⟩, ?_⟩
    · rw [constMapZHat_toKummerCompletion]
      exact (kummerNF_eq_mk N hkF f s _ hbv).symm
    · exact (exists_restrictClosed_eq_iff (N := s.nfModel hs) (hHL := rfl)
        (NumberField.isTorallyKummerFaithful s.K) v hvt hvNF _).1 ⟨b, hf, rfl⟩
  · rintro ⟨s, hs, c, rfl, ⟨f₀, hf₀, hNF₀⟩, htest⟩
    haveI : NumberField s.K := NumberField.of_module_finite k s.K
    obtain ⟨b, hbNF, rfl⟩ := (exists_restrictClosed_eq_iff (N := s.nfModel hs) (hHL := rfl)
      (NumberField.isTorallyKummerFaithful s.K) f₀ hf₀ hNF₀ c).2 htest
    have hb0 : algebraMap s.K Ω (b : s.K) ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap s.K Ω).injective).2 b.ne_zero
    let f : (fnf N)ˣ := Units.mk0 ⟨_, N.algebraic_mem _ hbNF⟩
      (fun h => hb0 (congrArg Subtype.val h))
    refine ⟨f, hbNF, ?_⟩
    rw [constMapZHat_toKummerCompletion]
    exact kummerNF_eq_mk N hkF f s _ rfl

include hkF in
/-- **[AbsTopIII] Thm 1.9 (d): `K^×_{Z_NF}` inside `lim→_V H¹(Π_V, Ẑ(1))` by the tests of
Prop 1.8**: a class lies in the image of the NF-rational functions iff it passes the test (i)
or the test (ii) at some NF-stage. -/
theorem mem_kummerNFRange_iff (hJ : ∀ s : StageIdx D, IsKummerFaithfulJac s.data)
    (ξ : H1Lim D) :
    ξ ∈ kummerNFRange N hkF ↔ IsNFStageTest N ξ ∨ IsNFStageConstTest N ξ := by
  rw [← exists_kummerNF_not_isAlgebraic_iff hkF hJ, ← exists_kummerNF_isAlgebraic_iff hkF]
  constructor
  · rintro ⟨f, rfl⟩
    by_cases h : IsAlgebraic ℚ ((f : fnf N) : Ω)
    · exact Or.inr ⟨f, h, rfl⟩
    · exact Or.inl ⟨f, h, rfl⟩
  · rintro (⟨f, -, rfl⟩ | ⟨f, -, rfl⟩) <;> exact ⟨f, rfl⟩

end Rec

/-! ### The curve form over a number field -/

section Curve

open CategoryTheory AlgebraicGeometry Belyi CurvesJacobian.Cusp

variable {k : Type u} [Field k] [CharZero k] [NumberField k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsCurveOver k X] [IsIntegral X] {τ : X.functionField}
  {hτ : Transcendental k τ} [IsGalois (K₀ k (coordT τ)) (FFClosure X)] [CharZero (FFClosure X)]
  [IsAlgClosed (FFClosure X)]

/-- **[AbsTopIII] Thm 1.9 (d) for a curve with a rational point over a number field**:
`K^×_{Z_NF}` inside `lim→_V H¹(Π_V, Ẑ(1))` is the set of classes passing the test of
Prop 1.8 (i) or (ii) at some NF-stage; no hypothesis (`⋂_N N · J(K) = 0` at every stage is
`isKummerFaithfulJac_stage_curve_numberField`). -/
theorem mem_kummerNFRange_iff_curve (N : NFModel (curveGaloisData k hτ))
    (σ : Spec (CommRingCat.of k) ⟶ X)
    (hσ : σ ≫ (X ↘ Spec (CommRingCat.of k)) = 𝟙 (Spec (CommRingCat.of k)))
    (ξ : H1Lim (curveGaloisData k hτ)) :
    ξ ∈ kummerNFRange N (mem_range_of_isAlgebraic_F k hτ) ↔
      IsNFStageTest N ξ ∨ IsNFStageConstTest N ξ :=
  mem_kummerNFRange_iff (mem_range_of_isAlgebraic_F k hτ)
    (isKummerFaithfulJac_stage_curve_numberField k hτ σ hσ) ξ

end Curve

end Iut.Reconstruction.Thm19
