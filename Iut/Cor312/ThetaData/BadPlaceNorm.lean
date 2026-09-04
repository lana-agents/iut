/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.ReductionNorm
import Iut.Cor312.ThetaData.TateFamily

/-!
# The residue characteristic at the bad places

At a finite place `w` of the torsion field `K` over `V_mod^bad` (residue characteristic `≠ 2`),
the completion `K_w` satisfies the standing hypothesis `TameResidueChar` of the Tate
uniformization: `‖2‖ = 1` (`2` is not in the maximal ideal) and `12 ≠ 0` (characteristic `0`).
-/

namespace Iut

open NumberField IsDedekindDomain.HeightOneSpectrum

universe u

section Two

variable {k : Type*} [Field k] [NumberField k]

/-- `2` lies in a finite place iff its residue characteristic is `2`. -/
lemma two_mem_maximalIdeal_iff (v : FinitePlace k) :
    (2 : 𝓞 k) ∈ v.maximalIdeal.asIdeal ↔ residueChar v = 2 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h2 : (Ideal.Quotient.mk v.maximalIdeal.asIdeal (2 : 𝓞 k)) =
      ((2 : ℕ) : 𝓞 k ⧸ v.maximalIdeal.asIdeal) := by
    rw [map_ofNat, Nat.cast_ofNat]
  rw [h2, CharP.cast_eq_zero_iff (𝓞 k ⧸ v.maximalIdeal.asIdeal) (ringChar _)]
  exact Nat.prime_dvd_prime_iff_eq (residueChar_prime v) Nat.prime_two

/-- `‖2‖ = 1` on the completion at a place not containing `2`. -/
lemma norm_two_eq_one_of_notMem {w : FinitePlace k} (h2 : (2 : 𝓞 k) ∉ w.maximalIdeal.asIdeal) :
    ‖(2 : localCompletion w)‖ = 1 := by
  rw [norm_eq_one_iff_valued]
  have : (2 : localCompletion w) =
      FinitePlace.embedding w.maximalIdeal (algebraMap (𝓞 k) k 2) := by
    rw [map_ofNat, map_ofNat]
  rw [this, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    valuation_eq_one_iff_notMem]
  exact h2

/-- `12 ≠ 0` on the completion (characteristic zero). -/
lemma twelve_ne_zero (w : FinitePlace k) : (12 : localCompletion w) ≠ 0 := by
  have : (12 : localCompletion w) = FinitePlace.embedding w.maximalIdeal 12 := by
    rw [map_ofNat]
  rw [this]
  exact (map_ne_zero (FinitePlace.embedding w.maximalIdeal)).mpr (by norm_num)

end Two

section BadPlace

open WeierstrassCurve

variable {F : Type u} [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable (K : IntermediateField F Fbar) [NumberField ↥K]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- `2` is not in a bad place of `K` (the places of `V_mod^bad` have odd residue
characteristic). -/
lemma two_notMem_of_isBadPlace (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2) {w : FinitePlace ↥K}
    (hw : IsBadPlace E K VBad w) : (2 : 𝓞 ↥K) ∉ w.maximalIdeal.asIdeal := by
  obtain ⟨v, hv, hwv⟩ := hw
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  intro h
  apply hVBad v hv
  rw [← two_mem_maximalIdeal_iff, Ideal.mem_of_liesOver (P := w.maximalIdeal.asIdeal),
    map_ofNat]
  exact h

/-- The completion at a bad place satisfies `TameResidueChar`. -/
lemma tameResidueChar_of_isBadPlace (hVBad : ∀ v ∈ VBad, residueChar v ≠ 2) {w : FinitePlace ↥K}
    (hw : IsBadPlace E K VBad w) : TateCurvesTheta.TameResidueChar (localCompletion w) :=
  ⟨norm_two_eq_one_of_notMem (two_notMem_of_isBadPlace E K hVBad hw), twelve_ne_zero w⟩

end BadPlace

end Iut
