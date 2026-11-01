/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.ResIso

/-!
# Inertia groups of translated places (MR9 item 4, step 1 (i))

For an automorphism `τ` of `Ω` and a place `W`, the inertia group of the translated place
`τW = {x | τ⁻¹x ∈ W}` is `τ I_W τ⁻¹`. Here:

* `valuation_comap_lt_one_iff`: `v_{τW}(τ y) < 1 ↔ v_W(y) < 1`;
* **`conj_mem_inertia`**: `σ ∈ I_W → τ σ τ⁻¹ ∈ I_{τW}`;
* **`conj_mem_inertiaH`**: the same in the group `H` of a Galois model;
* `transPlace_mem_CuspW`: translates of cusp places by `τ ∈ Gal(Ω/k(t))` are cusp places;
* **`conj_mem_map_inertiaH`**: in `Π_U`, `b (I_W ∩ H) b⁻¹ ⊆ I_{τW} ∩ H` for `b` the class of
  `τ ∈ H`.
-/

open KummerTheory Curve AffOrbicurve

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

section Conj

variable {P Ω : Type u} [Field P] [Field Ω] [Algebra P Ω]

/-- The translated place `τW = {x | τ⁻¹ x ∈ W}`. -/
abbrev transPlace (τ : Ω ≃ₐ[P] Ω) (W : ValuationSubring Ω) : ValuationSubring Ω :=
  W.comap (τ.symm : Ω ≃ₐ[P] Ω).toAlgHom.toRingHom

lemma mem_transPlace {τ : Ω ≃ₐ[P] Ω} {W : ValuationSubring Ω} {x : Ω} :
    x ∈ transPlace τ W ↔ τ.symm x ∈ W := ValuationSubring.mem_comap

lemma valuation_comap_lt_one_iff (W : ValuationSubring Ω) (τ : Ω ≃ₐ[P] Ω) (y : Ω) :
    (transPlace τ W).valuation (τ y) < 1 ↔ W.valuation y < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_transPlace,
    map_inv₀, AlgEquiv.symm_apply_apply, map_eq_zero_iff _ τ.injective]

/-- **`τ I_W τ⁻¹ ⊆ I_{τW}`.** -/
lemma conj_mem_inertia {W : ValuationSubring Ω} {σ : Ω ≃ₐ[P] Ω}
    (hσ : σ ∈ GaloisPi1.inertia W) (τ : Ω ≃ₐ[P] Ω) :
    τ * σ * τ⁻¹ ∈ GaloisPi1.inertia (transPlace τ W) := by
  intro a ha
  have h1 : (τ * σ * τ⁻¹) a - a = τ (σ (τ.symm a) - τ.symm a) := by
    rw [map_sub, AlgEquiv.apply_symm_apply]
    rfl
  rw [h1, valuation_comap_lt_one_iff]
  exact hσ _ (mem_transPlace.1 ha)

end Conj

section GaloisModel

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] {t : Ω}
  [IsGalois (K₀ k t) Ω] {D : Pi1.Orbifold.GaloisData k t}

omit [CharZero k] in
/-- **`τ (I_W ∩ H) τ⁻¹ ⊆ I_{τW} ∩ H`** for `τ ∈ H`. -/
lemma conj_mem_inertiaH {W : ValuationSubring Ω} {σ : D.H} (hσ : σ ∈ inertiaH D W) (τ : D.H) :
    τ * σ * τ⁻¹ ∈ inertiaH D (transPlace (τ : Ω ≃ₐ[K₀ k t] Ω) W) :=
  mem_inertiaH.2 (conj_mem_inertia (mem_inertiaH.1 hσ) (τ : Ω ≃ₐ[K₀ k t] Ω))

omit [CharZero k] [IsGalois (K₀ k t) Ω] in
lemma symm_fix_K₀ (τ : Ω ≃ₐ[K₀ k t] Ω) {x : Ω} (hx : x ∈ K₀ k t) : τ.symm x = x :=
  τ.symm.commutes ⟨x, hx⟩

omit [CharZero k] [IsGalois (K₀ k t) Ω] in
/-- Translates of cusp places are cusp places. -/
lemma transPlace_mem_CuspW {W : ValuationSubring Ω} (hW : W ∈ CuspW (k := k) (t := t))
    (τ : Ω ≃ₐ[K₀ k t] Ω) : transPlace τ W ∈ CuspW (k := k) (t := t) := by
  refine ⟨fun c => ?_, fun h => hW.2 ?_⟩
  · rw [mem_transPlace, symm_fix_K₀ τ (IntermediateField.algebraMap_mem _ c)]
    exact hW.1 c
  · rw [mem_transPlace, symm_fix_K₀ τ (IntermediateField.subset_adjoin k {t} rfl)] at h
    exact h

omit [CharZero k] in
/-- **Conjugation in `Π_U` moves cuspidal inertia to the inertia of the translated place.** -/
lemma conj_mem_map_inertiaH {W : ValuationSubring Ω} (τ : D.H) {x : Pi D}
    (hx : x ∈ (inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) :
    (τ : Pi D) * x * (τ : Pi D)⁻¹ ∈ (inertiaH D (transPlace (τ : Ω ≃ₐ[K₀ k t] Ω) W)).map
      (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  refine ⟨τ * σ * τ⁻¹, conj_mem_inertiaH hσ τ, ?_⟩
  rw [map_mul, map_mul, map_inv]
  rfl

end GaloisModel

end Iut.Reconstruction.Thm19
