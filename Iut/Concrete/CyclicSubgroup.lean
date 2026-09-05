/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.Existence

/-!
# Galois-stable cyclic subgroups of an elliptic curve

`Iut.EllipticCurveData.HasCyclicSubgroup C ℓ` says that `E(F̄)` contains a subgroup of order
`ℓ` stable under `Gal(F̄/F)`: an `ℓ`-cyclic subgroup scheme of `E/F` (the condition on
the points of IUT IV, Corollary 2.2 excluded by the lower bound on the height). Such a
subgroup consists of `ℓ`-torsion points (`HasCyclicSubgroup.nsmul_eq_zero`,
`HasCyclicSubgroup.le_torsionBy`).
-/

namespace Iut.EllipticCurveData

open WeierstrassCurve NumberField
open scoped Classical

variable (C : EllipticCurveData.{u})

/-- `E/F` has an **`ℓ`-cyclic subgroup scheme**: a `Gal(F̄/F)`-stable subgroup of `E(F̄)` of
order `ℓ`. -/
def HasCyclicSubgroup (ℓ : ℕ) : Prop :=
  ∃ H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)),
    Nat.card H = ℓ ∧ ∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H

variable {C}

/-- An element of a subgroup of order `ℓ` is killed by `ℓ`. -/
lemma nsmul_eq_zero_of_mem_of_card_eq {ℓ : ℕ}
    {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))} (hH : Nat.card H = ℓ)
    {P : Affine.Point (Affine.baseChange C.E C.Fbar)} (hP : P ∈ H) : ℓ • P = 0 := by
  have h := card_nsmul_eq_zero' (x := (⟨P, hP⟩ : H))
  rw [hH] at h
  exact congrArg Subtype.val h

/-- A subgroup of order `ℓ` lies in the `ℓ`-torsion. -/
lemma le_torsionBy_of_card_eq {ℓ : ℕ}
    {H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar))} (hH : Nat.card H = ℓ) :
    H ≤ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ := fun _ hP =>
  AddSubgroup.torsionBy.nsmul_iff.mpr (nsmul_eq_zero_of_mem_of_card_eq hH hP)

/-- The subgroup witnessing `HasCyclicSubgroup C ℓ` consists of `ℓ`-torsion points. -/
lemma HasCyclicSubgroup.exists_le_torsionBy {ℓ : ℕ} (h : C.HasCyclicSubgroup ℓ) :
    ∃ H : AddSubgroup (Affine.Point (Affine.baseChange C.E C.Fbar)),
      Nat.card H = ℓ ∧
      (∀ σ : C.Fbar ≃ₐ[C.F] C.Fbar, ∀ P ∈ H, galPointMap C.F C.E C.Fbar σ P ∈ H) ∧
      H ≤ AddSubgroup.torsionBy (Affine.Point (Affine.baseChange C.E C.Fbar)) ℓ := by
  obtain ⟨H, hH, hgal⟩ := h
  exact ⟨H, hH, hgal, le_torsionBy_of_card_eq hH⟩

end Iut.EllipticCurveData
