/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Thm19.StageCompat

/-!
# Cuspidal inertia under the extension of the field of constants (MR9 item 4, step 1 (ii))

For a finite extension `K₁ / k` the Galois model of `U_{K₁}` is `constExt K₁ D` with
`H' = H ∩ Gal(Ω/K₁(t))` and `piRes : Π_{U_{K₁}} ↪ Π_U` (curves-jacobian `LocAn/ThmCConstExt`).
The inertia group of a place `W` in `H'` is contained in that of `W` in `H`:

* `hRes_mem_inertiaH`: `σ ∈ I_W ∩ H' → hRes σ ∈ I_W ∩ H`;
* **`piRes_mem_map_inertiaH`**: `piRes` maps the image of `I_W ∩ H'` in `Π_{U_{K₁}}` into the image
  of `I_W ∩ H` in `Π_U`;
* conversely (`W ⊇ k`) `exists_hRes_eq_of_mem_inertiaH`, **`exists_piRes_eq_of_mem_map_inertiaH`**:
  every element of `I_W ∩ H` comes from `I_W ∩ H'` (inertia fixes the algebraic elements,
  continuous-kummer-theory `inertia_fix_algebraic`).
-/

open KummerTheory Curve AffOrbicurve CurvesJacobian CurvesJacobian.Kummer Pi1.Orbifold

universe u

noncomputable section

namespace Iut.Reconstruction.Thm19

set_option linter.unusedSectionVars false

section ConstInertia

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [CharZero k] [IsAlgClosed Ω]
  {t : Ω} {D : GaloisData k t} [IsGalois (K₀ k t) Ω]
  {K₁ : IntermediateField k Ω} [FiniteDimensional k K₁]

/-- The inertia group in `H' = H ∩ Gal(Ω/K₁(t))` lies in that of `H`. -/
lemma hRes_mem_inertiaH {W : ValuationSubring Ω} {σ : (constExt K₁ D).H}
    (hσ : σ ∈ inertiaH (constExt K₁ D) W) : hRes K₁ D σ ∈ inertiaH D W :=
  fun a ha => hσ a ha

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **`piRes` maps cuspidal inertia of `U_{K₁}` into cuspidal inertia of `U`.** -/
lemma piRes_mem_map_inertiaH {W : ValuationSubring Ω} {x : Pi (constExt K₁ D)}
    (hx : x ∈ (inertiaH (constExt K₁ D) W).map
      (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S))) :
    piRes K₁ D x ∈ (inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S)) := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  exact ⟨hRes K₁ D σ, hRes_mem_inertiaH hσ, rfl⟩

/-- **Inertia of `U` lifts to `U_{K₁}`**: an element of `I_W ∩ H` (`W ⊇ k`) fixes the algebraic
elements (`inertia_fix_algebraic`, residue characteristic `0`), hence `K₁`, so it comes from
`I_W ∩ H'`. -/
lemma exists_hRes_eq_of_mem_inertiaH {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {σ : D.H} (hσ : σ ∈ inertiaH D W) :
    ∃ σ' : (constExt K₁ D).H, σ' ∈ inertiaH (constExt K₁ D) W ∧ hRes K₁ D σ' = σ := by
  obtain ⟨τ, hτ⟩ := exists_resK_eq (k := k) (K := K₁) (t := t) (h := (σ : Ω ≃ₐ[K₀ k t] Ω))
    (fun c => inertia_fix_algebraic hk hσ (Algebra.IsAlgebraic.isAlgebraic (R := k) c).algebraMap)
  have hτH : τ ∈ (constExt K₁ D).H := (mem_constExt_H D).2 (by rw [hτ]; exact σ.2)
  refine ⟨⟨τ, hτH⟩, fun a ha => ?_, Subtype.ext hτ⟩
  have e : τ a = (σ : Ω ≃ₐ[K₀ k t] Ω) a := by rw [← hτ]; rfl
  change W.valuation (τ a - a) < 1
  rw [e]
  exact hσ a ha

set_option synthInstance.maxHeartbeats 400000 in
-- the group structures on the quotients `Π_U` are found slowly
/-- **The cusp inertia of `U` is the `piRes`-image of that of `U_{K₁}`** (at a place `W ⊇ k`). -/
lemma exists_piRes_eq_of_mem_map_inertiaH {W : ValuationSubring Ω}
    (hk : ∀ c : k, algebraMap k Ω c ∈ W) {x : Pi D}
    (hx : x ∈ (inertiaH D W).map (QuotientGroup.mk' (GaloisPi1.kernel D.H D.S))) :
    ∃ y ∈ (inertiaH (constExt K₁ D) W).map
      (QuotientGroup.mk' (GaloisPi1.kernel (constExt K₁ D).H (constExt K₁ D).S)),
      piRes K₁ D y = x := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  obtain ⟨σ', hσ', rfl⟩ := exists_hRes_eq_of_mem_inertiaH (K₁ := K₁) hk hσ
  exact ⟨_, ⟨σ', hσ', rfl⟩, rfl⟩

end ConstInertia

end Iut.Reconstruction.Thm19
