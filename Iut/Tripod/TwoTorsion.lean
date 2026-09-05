/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveOf

/-!
# The rational 2-torsion of the Legendre curve

`E_λ : y² = x(x−1)(x−λ)` has exactly four 2-torsion points over any field of characteristic
`≠ 2` containing `λ`: `O`, `(0,0)`, `(1,0)`, `(λ,0)`. This is the input `TwoTorsionRational`
of the construction of the theta local data (`Iut.thetaLocalData`).
-/

namespace Iut.Tripod

open WeierstrassCurve
open scoped Classical

/-- The 2-torsion subgroup of `E_λ` has exactly four elements. -/
theorem card_torsionBy_two {K : Type*} [Field K] [NeZero (2 : K)] (l : K)
    [(legendre l).IsElliptic] (h0 : l ≠ 0) (h1 : l ≠ 1) :
    Nat.card ↥(AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) = 4 := by
  set P₁ : (legendre l).toAffine.Point := .some 0 0 (legendre_nonsingular_zero l) with hP₁
  set P₂ : (legendre l).toAffine.Point := .some 1 0 (legendre_nonsingular_one l) with hP₂
  set P₃ : (legendre l).toAffine.Point := .some l 0 (legendre_nonsingular_self l) with hP₃
  have hset : ((AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) :
      Set (legendre l).toAffine.Point) = {0, P₁, P₂, P₃} := by
    ext P
    rw [SetLike.mem_coe, AddSubgroup.torsionBy.nsmul_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hP
      rcases legendre_two_torsion l hP with rfl | ⟨x, h, rfl, hx | hx | hx⟩
      · exact Or.inl rfl
      · subst hx
        exact Or.inr (Or.inl rfl)
      · subst hx
        exact Or.inr (Or.inr (Or.inl rfl))
      · subst hx
        exact Or.inr (Or.inr (Or.inr rfl))
    · rintro (rfl | rfl | rfl | rfl)
      · simp
      · exact two_nsmul_some_zero l _
      · exact two_nsmul_some_zero l _
      · exact two_nsmul_some_zero l _
  have h01 : P₁ ≠ P₂ := by
    intro h
    rw [hP₁, hP₂, Affine.Point.some.injEq] at h
    exact zero_ne_one h.1
  have h02 : P₁ ≠ P₃ := by
    intro h
    rw [hP₁, hP₃, Affine.Point.some.injEq] at h
    exact h0 h.1.symm
  have h12 : P₂ ≠ P₃ := by
    intro h
    rw [hP₂, hP₃, Affine.Point.some.injEq] at h
    exact h1 h.1.symm
  have hcard : Nat.card ↥(AddSubgroup.torsionBy (legendre l).toAffine.Point ((2 : ℕ) : ℤ)) =
      Set.ncard ({0, P₁, P₂, P₃} : Set (legendre l).toAffine.Point) := by
    rw [← hset]
    exact Nat.card_coe_set_eq _
  rw [hcard, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_singleton]
  · exact fun h => h12 (Set.mem_singleton_iff.mp h)
  · rintro (h | h)
    · exact h01 h
    · exact h02 (Set.mem_singleton_iff.mp h)
  · rintro (h | h | h)
    · exact Affine.Point.some_ne_zero _ h.symm
    · exact Affine.Point.some_ne_zero _ h.symm
    · exact Affine.Point.some_ne_zero _ (Set.mem_singleton_iff.mp h).symm

/-- The curve of a point has four rational 2-torsion points. -/
theorem two_torsion_curveOf (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5) :
    2 * 2 ≤ Nat.card ↥(AddSubgroup.torsionBy (curveOf x h3 h5).E.toAffine.Point ((2 : ℕ) : ℤ)) := by
  haveI := legendre_gen'_isElliptic x
  exact (card_torsionBy_two (gen' x.1) (gen'_ne_zero x.2.1) (gen'_ne_one x.2.2)).ge

end Iut.Tripod
