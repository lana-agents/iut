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
  of `I_W ∩ H` in `Π_U`.
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

end ConstInertia

end Iut.Reconstruction.Thm19
