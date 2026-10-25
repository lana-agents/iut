/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.NFTransition
import Iut.Reconstruction.Thm19.NFAdditive

/-!
# [AbsTopIII] Thm 1.9 (d): `K^×_{Z_NF} ↪ lim→_V H¹(Π_V, Ẑ(1))`

[AbsTopIII] Thm 1.9 (d) (`Topics in Absolute Anabelian Geometry III.txt` l.2158–2178): "one
constructs the subgroups `k̄_NF^× ⊆ K^×_{Z_NF} ↪ lim→_V H¹(Π_V, μ_Ẑ(Π_U))` — where `V` ranges over
the open subschemes obtained by removing finite collections of NF-points from `Z ×_{k_Z} k′`, for
`k′` a finite extension of `k_Z`; […] the "`↪`" arises from the Kummer map". The stages
`stage D K t′` of the colimit and its transition maps `resT` are in `Thm19/NFTransition.lean`.
Here:

* **`exists_finite_mem_F_constExt`**: every element of the function field `F k̄` of `U_{k̄}` lies
  in the function field `F K` of `U_K` for a finite extension `K / k` (the stabiliser of the
  element in `H` is open and contains the kernel of `H ↠ G_k`, so its image in `G_k` is an open
  subgroup, which contains `Gal(k̄ / K)` for some finite `K`);
* **`exists_stage_ge_sup`**: two stages `(K₁, t₁)`, `(K₂, t₂)` lie below a stage over `K₁ ⊔ K₂`
  (directedness of the double colimit);
* **`exists_stage_units_of_mem_baseChange`**: every nonzero element of `F k̄` is a unit on some
  stage, and **`exists_stage_units_fnf`**: in particular every `f ∈ K^×_{Z_NF} = F_NF^×`, so the
  Kummer class `κ_V(f)` of every NF-rational function lives in the colimit;
* **`coe_eq_of_resT_eq`** (injectivity of the Kummer map into the colimit, `k` torally
  Kummer-faithful, e.g. a number field or a finite extension of `ℚ_p`):
  units of two stages whose Kummer classes agree at a common later stage are the same function.
-/

open KummerTheory Curve AffOrbicurve WeilCurves.FunctionField CurvesJacobian.Kummer

universe u

namespace Iut.Reconstruction.Thm19

open CurvesJacobian

set_option linter.unusedSectionVars false

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}
  (D : Pi1.Orbifold.GaloisData k t) [CharZero k] [IsGalois (K₀ k t) Ω] [IsAlgClosed Ω]

section Finite

/-- **Every element of `F k̄` lies in `F K` for a finite extension `K / k`** (`k` algebraically
closed in `F`). -/
theorem exists_finite_mem_F_constExt
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {x : Ω} (hx : x ∈ F (baseChange D)) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K), x ∈ F (constExt K D) := by
  haveI : CompactSpace D.H := GaloisPi1.compactSpace_of_isClosed _ D.isClosed_H
  set O : Set D.H := {h | (h : Ω ≃ₐ[K₀ k t] Ω) x = x} with hO
  have hOopen : IsOpen O :=
    (stabilizer_isOpen_of_isIntegral (K := K₀ k t) (L := Ω) x).preimage continuous_subtype_val
  -- `O` is saturated for `H → G_k`: its kernel fixes `F k̄`
  have hsat : ∀ h h' : D.H, hToGk D h = hToGk D h' → h ∈ O → h' ∈ O := by
    intro h h' he hh
    have h1 : hToGk D (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have hfix := fixes_F_baseChange D (h⁻¹ * h').2 ((hToGk_eq_one_iff D _).1 h1) hx
    change (h' : Ω ≃ₐ[K₀ k t] Ω) x = x
    have : (h' : Ω ≃ₐ[K₀ k t] Ω) = (h : Ω ≃ₐ[K₀ k t] Ω) * ((h⁻¹ * h' : D.H) :
        Ω ≃ₐ[K₀ k t] Ω) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [this, AlgEquiv.mul_apply, hfix]
    exact hh
  have hq : Topology.IsQuotientMap (hToGk D) :=
    (continuous_hToGk D).isClosedMap.isQuotientMap (continuous_hToGk D) (hToGk_surjective D hkF)
  have hpre : hToGk D ⁻¹' (hToGk D '' O) = O := by
    ext h
    constructor
    · rintro ⟨h', hh', he⟩
      exact hsat h' h he hh'
    · intro hh
      exact ⟨h, hh, rfl⟩
  have hIopen : IsOpen (hToGk D '' O) := by
    rw [← hq.isCoinducing.isOpen_preimage, hpre]
    exact hOopen
  have h1 : (1 : Gk k Ω) ∈ hToGk D '' O := ⟨1, rfl, map_one _⟩
  obtain ⟨E, hE, hEI⟩ :=
    (krullTopology_mem_nhds_one_iff k (kbar k Ω) _).1 (hIopen.mem_nhds h1)
  set K := E.map (kbar k Ω).val with hK
  haveI hKf : FiniteDimensional k K :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap E (kbar k Ω).val).toLinearEquiv
  refine ⟨K, hKf, ?_⟩
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  let h : D.H := ⟨resK k K t σ, (mem_constExt_H D).1 hσ⟩
  have hhE : hToGk D h ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    apply Subtype.ext
    change algebraMap (kbar k Ω) Ω (hToGk D h y) = algebraMap (kbar k Ω) Ω y
    rw [algebraMap_hToGk_apply]
    exact resK_fix σ ⟨(y : Ω), ⟨y, hy, rfl⟩⟩
  obtain ⟨h', hh'O, he⟩ := hEI hhE
  have hmem := hsat h' h he hh'O
  simp only [hO, Set.mem_setOf_eq] at hmem
  exact hmem

end Finite

section Directed

variable {D}

lemma transcendental_sup {K₁ K₂ : IntermediateField k Ω} [FiniteDimensional k K₁]
    [FiniteDimensional k K₂] {x : Ω} (hx : Transcendental K₁ x) :
    Transcendental (↥(K₁ ⊔ K₂)) x := by
  have hk : Transcendental k x := fun h => hx (h.extendScalars (algebraMap k K₁).injective)
  exact Transcendental.extendScalars (↥(K₁ ⊔ K₂)) hk

variable (D) in
/-- **Directedness across extensions**: stages `(K₁, t₁)` and `(K₂, t₂)` lie below a stage over
`K₁ ⊔ K₂`. -/
theorem exists_stage_ge_sup (hH : D.H ≤ D.HL) {K₁ K₂ : IntermediateField k Ω}
    [FiniteDimensional k K₁] [FiniteDimensional k K₂] {t₁ t₂ : Ω}
    (ht₁ : t₁ ∈ (constExt K₁ D).L) (htr₁ : Transcendental K₁ t₁)
    (ht₂ : t₂ ∈ (constExt K₂ D).L) :
    ∃ t₃ : Ω, t₃ ∈ (constExt (K₁ ⊔ K₂) D).L ∧ Transcendental (↥(K₁ ⊔ K₂)) t₃ ∧
      t₁ ∈ chartRing (↥(K₁ ⊔ K₂)) t₃ ∧ t₂ ∈ chartRing (↥(K₁ ⊔ K₂)) t₃ :=
  exists_stage_ge D (K₁ ⊔ K₂) hH (L_constExt_mono D le_sup_left ht₁) (transcendental_sup htr₁)
    (L_constExt_mono D le_sup_right ht₂)

end Directed

section Units

attribute [local instance] CurvesJacobian.isFunctionField_F

/-- **Every nonzero element of `F k̄` is a unit on some stage** `V ⊆ U_K`, `K / k` finite, with
`t` regular on `V`. -/
theorem exists_stage_units_of_mem_baseChange
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {f : Ω} (hf : f ∈ F (baseChange D)) (hf0 : f ≠ 0) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K) (t' : Ω)
      (ht' : t' ∈ (constExt K D).L) (htr' : Transcendental K t'),
      t ∈ chartRing K t' ∧ ∃ v : units (stage D K ht' htr'),
        (((v : (F (stage D K ht' htr'))ˣ) : F (stage D K ht' htr')) : Ω) = f := by
  obtain ⟨K, hK, hfK⟩ := exists_finite_mem_F_constExt D hkF hf
  have hne : (⟨f, hfK⟩ : F (constExt K D)) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  obtain ⟨t', ht', htr', htV, v, hv⟩ := exists_stage_units D K (Units.mk0 _ hne)
  exact ⟨K, hK, t', ht', htr', htV, v, hv⟩

/-- **[AbsTopIII] Thm 1.9 (d), `K^×_{Z_NF} → lim→_V`**: every `f ∈ K^×_{Z_NF} = F_NF^×` is a unit
on some stage `V ⊆ U_K` (`K / k` finite), so it has a Kummer class `κ_V(f)` in the colimit. -/
theorem exists_stage_units_fnf [CharZero Ω] (N : NFModel D)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    (f : (fnf N)ˣ) :
    ∃ (K : IntermediateField k Ω) (_ : FiniteDimensional k K) (t' : Ω)
      (ht' : t' ∈ (constExt K D).L) (htr' : Transcendental K t'),
      t ∈ chartRing K t' ∧ ∃ v : units (stage D K ht' htr'),
        (((v : (F (stage D K ht' htr'))ˣ) : F (stage D K ht' htr')) : Ω) =
          ((f : fnf N) : Ω) :=
  exists_stage_units_of_mem_baseChange D hkF (N.mem_F _ (f : fnf N).2)
    fun h => f.ne_zero (Subtype.ext h)

end Units

section Injective

variable {D}

set_option maxHeartbeats 1600000 in
-- rewriting with `resT_kummerMapZHat` unifies the `ContH1` instances of two stages
/-- **[AbsTopIII] Thm 1.9 (d), the Kummer map into the colimit is injective** (`k` torally
Kummer-faithful, e.g. a number field or a finite extension of `ℚ_p`): if units `v₁`, `v₂` of
stages `(K₁, t₁)`, `(K₂, t₂)` have the same Kummer class at a common later stage `(K₃, t₃)`, then
they are the same function. -/
theorem coe_eq_of_resT_eq (htf : IsTorallyKummerFaithful k) (hH : D.H ≤ D.HL)
    (hkF : ∀ x : F D, IsAlgebraic k x → x ∈ Set.range (algebraMap k (F D)))
    {K₁ K₂ K₃ : IntermediateField k Ω} [FiniteDimensional k K₁] [FiniteDimensional k K₂]
    [FiniteDimensional k K₃] (h₁₃ : K₁ ≤ K₃) (h₂₃ : K₂ ≤ K₃) {t₁ t₂ t₃ : Ω}
    {ht₁ : t₁ ∈ (constExt K₁ D).L} {htr₁ : Transcendental K₁ t₁}
    {ht₂ : t₂ ∈ (constExt K₂ D).L} {htr₂ : Transcendental K₂ t₂}
    {ht₃ : t₃ ∈ (constExt K₃ D).L} {htr₃ : Transcendental K₃ t₃}
    [IsGalois (K₀ K₁ t₁) Ω] [IsGalois (K₀ K₂ t₂) Ω] [IsGalois (K₀ K₃ t₃) Ω]
    (hc₁ : t₁ ∈ chartRing K₃ t₃) (hc₂ : t₂ ∈ chartRing K₃ t₃)
    (v₁ : units (stage D K₁ ht₁ htr₁)) (v₂ : units (stage D K₂ ht₂ htr₂))
    (h : resT (stage D K₁ ht₁ htr₁) (stage D K₃ ht₃ htr₃)
        (fun _ hx => F_stage_mono D h₁₃ ht₃ htr₃ hx) (hW_stage_mono h₁₃ hc₁)
        (stage_H_le D K₁ ht₁ htr₁) (kummerMapZHat (stage D K₁ ht₁ htr₁) v₁) =
      resT (stage D K₂ ht₂ htr₂) (stage D K₃ ht₃ htr₃)
        (fun _ hx => F_stage_mono D h₂₃ ht₃ htr₃ hx) (hW_stage_mono h₂₃ hc₂)
        (stage_H_le D K₂ ht₂ htr₂) (kummerMapZHat (stage D K₂ ht₂ htr₂) v₂)) :
    (((v₁ : (F (stage D K₁ ht₁ htr₁))ˣ) : F (stage D K₁ ht₁ htr₁)) : Ω) =
      (((v₂ : (F (stage D K₂ ht₂ htr₂))ˣ) : F (stage D K₂ ht₂ htr₂)) : Ω) := by
  rw [resT_kummerMapZHat, resT_kummerMapZHat] at h
  have he := kummerMapZHat_injective (mem_range_of_isAlgebraic_stage hH hkF) (htf K₃) h
  rw [← coe_unitsT (stage D K₁ ht₁ htr₁) (stage D K₃ ht₃ htr₃)
      (fun _ hx => F_stage_mono D h₁₃ ht₃ htr₃ hx) (hW_stage_mono h₁₃ hc₁) v₁,
    ← coe_unitsT (stage D K₂ ht₂ htr₂) (stage D K₃ ht₃ htr₃)
      (fun _ hx => F_stage_mono D h₂₃ ht₃ htr₃ hx) (hW_stage_mono h₂₃ hc₂) v₂, he]

end Injective

end Iut.Reconstruction.Thm19
