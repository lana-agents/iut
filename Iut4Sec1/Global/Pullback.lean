/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Iut4Sec1.Global.ArithmeticDivisor
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Pullback of arithmetic divisors

This file implements both finite- and infinite-place pullback for a finite
extension of number fields. At a finite place the coefficient is multiplied by
the ramification index. At an infinite place it is multiplied by the local
completion degree (one or two). The ramification--inertia sum formulas prove
invariance of normalized degree.
-/

open NumberField
open scoped NumberField

namespace Iut4Sec1

section Extension

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

private noncomputable def heightOneSpectrumOfPrimeOver
    (v : NumberField.FinitePlace K)
    (q : v.maximalIdeal.asIdeal.primesOver (𝓞 L)) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
  ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver v.maximalIdeal.ne_bot q.2⟩

private noncomputable def finitePlaceOfPrimeOver
    (v : NumberField.FinitePlace K)
    (q : v.maximalIdeal.asIdeal.primesOver (𝓞 L)) :
    NumberField.FinitePlace L :=
  NumberField.FinitePlace.mk (heightOneSpectrumOfPrimeOver v q)

private noncomputable def finitePlaceSinglePullback
    (v : NumberField.FinitePlace K) (c : ℝ) : ArithmeticDivisor L :=
  ∑ q : v.maximalIdeal.asIdeal.primesOver (𝓞 L),
    Finsupp.single (.inl (finitePlaceOfPrimeOver v q))
      ((q.1.ramificationIdx (𝓞 K) : ℝ) * c)

private noncomputable def infinitePlaceSinglePullback
    (v : NumberField.InfinitePlace K) (c : ℝ) : ArithmeticDivisor L := by
  classical
  exact ∑ w : NumberField.InfinitePlace L,
    if w ∈ v.placesOver L then
      Finsupp.single (.inr w) ((v.inertiaDeg w : ℝ) * c)
    else 0

/-- Pullback of an arithmetic divisor through a finite extension of number fields. -/
noncomputable def arithmeticDivisorPullback (D : ArithmeticDivisor K) : ArithmeticDivisor L :=
  D.sum fun v c => match v with
    | .inl v => finitePlaceSinglePullback v c
    | .inr v => infinitePlaceSinglePullback v c

private lemma ringOfIntegers_finrank_eq :
    Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L := by
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 K) K (𝓞 L) L).symm

private lemma arithmeticDivisorDegree_single
    (v : ArithmeticPlace K) (c : ℝ) :
    arithmeticDivisorDegree (Finsupp.single v c : ArithmeticDivisor K) =
      c * arithmeticPlaceWeight v := by
  classical
  simp [arithmeticDivisorDegree]

private lemma arithmeticDivisorDegree_finsetSum {ι : Type*}
    (s : Finset ι) (D : ι → ArithmeticDivisor K) :
    arithmeticDivisorDegree (∑ i ∈ s, D i) =
      ∑ i ∈ s, arithmeticDivisorDegree (D i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [arithmeticDivisorDegree_add, ih]

private lemma arithmeticDivisorDegree_sum {ι : Type*} [Fintype ι]
    (D : ι → ArithmeticDivisor K) :
    arithmeticDivisorDegree (∑ i, D i) = ∑ i, arithmeticDivisorDegree (D i) := by
  simpa using arithmeticDivisorDegree_finsetSum (K := K) Finset.univ D

private lemma finitePlace_weight_eq_inertia_mul
    (v : NumberField.FinitePlace K)
    (q : v.maximalIdeal.asIdeal.primesOver (𝓞 L)) :
    arithmeticPlaceWeight (.inl (finitePlaceOfPrimeOver v q)) =
      (q.1.inertiaDeg (𝓞 K) : ℝ) * arithmeticPlaceWeight (.inl v) := by
  letI : q.1.LiesOver v.maximalIdeal.asIdeal := q.2.2
  have hnorm := Ideal.absNorm_pow_inertiaDeg v.maximalIdeal.asIdeal q.1
  rw [arithmeticPlaceWeight, arithmeticPlaceWeight]
  unfold finitePlaceOfPrimeOver
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  change Real.log (q.1.absNorm : ℝ) =
    (q.1.inertiaDeg (𝓞 K) : ℝ) * Real.log (v.maximalIdeal.asIdeal.absNorm : ℝ)
  rw [← hnorm, Nat.cast_pow, Real.log_pow]

private lemma finitePlaceSinglePullback_degree
    (v : NumberField.FinitePlace K) (c : ℝ) :
    arithmeticDivisorDegree (finitePlaceSinglePullback (L := L) v c) =
      (Module.finrank K L : ℝ) *
        arithmeticDivisorDegree (Finsupp.single (.inl v) c : ArithmeticDivisor K) := by
  classical
  rw [finitePlaceSinglePullback, arithmeticDivisorDegree_sum]
  simp_rw [arithmeticDivisorDegree_single, finitePlace_weight_eq_inertia_mul]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank
    v.maximalIdeal.asIdeal (𝓞 L)
  rw [ringOfIntegers_finrank_eq (K := K) (L := L)] at hsum
  have hsumR : (∑ q : v.maximalIdeal.asIdeal.primesOver (𝓞 L),
      (q.1.ramificationIdx (𝓞 K) : ℝ) * q.1.inertiaDeg (𝓞 K)) =
      (Module.finrank K L : ℝ) := by exact_mod_cast hsum
  rw [← hsumR, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  ring

private lemma infinitePlaceSinglePullback_degree
    (v : NumberField.InfinitePlace K) (c : ℝ) :
    arithmeticDivisorDegree (infinitePlaceSinglePullback (L := L) v c) =
      (Module.finrank K L : ℝ) *
        arithmeticDivisorDegree (Finsupp.single (.inr v) c : ArithmeticDivisor K) := by
  classical
  rw [infinitePlaceSinglePullback, arithmeticDivisorDegree_sum]
  simp_rw [apply_ite arithmeticDivisorDegree, arithmeticDivisorDegree_zero,
    arithmeticDivisorDegree_single, arithmeticPlaceWeight]
  have hsum := NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank K L v
  have hsumR : (∑ w ∈ (v.placesOver L).toFinset, (v.inertiaDeg w : ℝ)) =
      (Module.finrank K L : ℝ) := by exact_mod_cast hsum
  rw [← hsumR]
  simp only [mul_one]
  rw [Finset.sum_mul]
  calc
    (∑ x : NumberField.InfinitePlace L,
        if x ∈ v.placesOver L then (v.inertiaDeg x : ℝ) * c else 0) =
        ∑ x ∈ Finset.univ.filter (fun w => w ∈ v.placesOver L),
          (v.inertiaDeg x : ℝ) * c :=
      (Finset.sum_filter (fun w : NumberField.InfinitePlace L => w ∈ v.placesOver L)
        (fun w => (v.inertiaDeg w : ℝ) * c)).symm
    _ = ∑ x ∈ (v.placesOver L).toFinset, (v.inertiaDeg x : ℝ) * c := by
      congr 1
      ext w
      simp

/-- Raw degree scales by the field-extension degree under pullback. -/
theorem arithmeticDivisorDegree_pullback (D : ArithmeticDivisor K) :
    arithmeticDivisorDegree (arithmeticDivisorPullback (L := L) D) =
      (Module.finrank K L : ℝ) * arithmeticDivisorDegree D := by
  classical
  rw [← arithmeticDivisorDegreeHom_apply, arithmeticDivisorPullback, map_finsuppSum,
    arithmeticDivisorDegree, Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro v _
  simp only [arithmeticDivisorDegreeHom_apply]
  cases v with
  | inl v =>
      rw [finitePlaceSinglePullback_degree, arithmeticDivisorDegree_single]
  | inr v =>
      rw [infinitePlaceSinglePullback_degree, arithmeticDivisorDegree_single]

/-- The normalized degree of Definition 1.9(i) is invariant under pullback. -/
theorem normalizedArithmeticDivisorDegree_pullback (D : ArithmeticDivisor K) :
    normalizedArithmeticDivisorDegree (arithmeticDivisorPullback (L := L) D) =
      normalizedArithmeticDivisorDegree D := by
  rw [normalizedArithmeticDivisorDegree, normalizedArithmeticDivisorDegree,
    arithmeticDivisorDegree_pullback]
  have htower : (Module.finrank ℚ L : ℝ) =
      (Module.finrank ℚ K : ℝ) * Module.finrank K L := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K L).symm
  have hK : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K).ne'
  have hL : (Module.finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K L).ne'
  rw [htower]
  field_simp

/-! ## Parts and normalized local degree -/

/-- The degree of a completion over the corresponding completion of `ℚ`. -/
noncomputable def arithmeticPlaceLocalDegree : ArithmeticPlace K → ℕ
  | .inl v =>
      v.maximalIdeal.asIdeal.ramificationIdx ℤ *
        v.maximalIdeal.asIdeal.inertiaDeg ℤ
  | .inr v => v.mult

lemma arithmeticPlaceLocalDegree_pos (v : ArithmeticPlace K) :
    0 < arithmeticPlaceLocalDegree v := by
  cases v with
  | inl v =>
      exact Nat.mul_pos (Ideal.ramificationIdx_pos v.maximalIdeal.asIdeal ℤ)
        (Ideal.inertiaDeg_pos v.maximalIdeal.asIdeal ℤ)
  | inr v => exact NumberField.InfinitePlace.mult_pos

/-- The raw degree of the part of `D` supported on `E`, divided by the total
local degree of the places in `E`. -/
noncomputable def normalizedLocalDegree
    (D : ArithmeticDivisor K) (E : Finset (ArithmeticPlace K)) : ℝ :=
  arithmeticDivisorDegree (arithmeticDivisorPart D (· ∈ E)) /
    ∑ v ∈ E, (arithmeticPlaceLocalDegree v : ℝ)

noncomputable def pullbackLocalDegreeSum
    (E : Finset (ArithmeticPlace K)) : ℝ := by
  classical
  exact ∑ v ∈ E, match v with
    | .inl v =>
        ∑ q : v.maximalIdeal.asIdeal.primesOver (𝓞 L),
          (arithmeticPlaceLocalDegree
            (.inl (finitePlaceOfPrimeOver v q)) : ℝ)
    | .inr v =>
        ∑ w : NumberField.InfinitePlace L,
          if w ∈ v.placesOver L then
            (arithmeticPlaceLocalDegree (.inr w) : ℝ)
          else 0

private lemma finitePlace_localDegree_eq
    (v : NumberField.FinitePlace K)
    (q : v.maximalIdeal.asIdeal.primesOver (𝓞 L)) :
    arithmeticPlaceLocalDegree (.inl (finitePlaceOfPrimeOver v q)) =
      (q.1.ramificationIdx (𝓞 K) * q.1.inertiaDeg (𝓞 K)) *
        arithmeticPlaceLocalDegree (.inl v) := by
  letI : q.1.LiesOver v.maximalIdeal.asIdeal := q.2.2
  rw [arithmeticPlaceLocalDegree, arithmeticPlaceLocalDegree]
  unfold finitePlaceOfPrimeOver
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  unfold heightOneSpectrumOfPrimeOver
  rw [Ideal.ramificationIdx_tower (R := ℤ) v.maximalIdeal.asIdeal q.1,
    Ideal.inertiaDeg_tower (R := ℤ) v.maximalIdeal.asIdeal q.1]
  ring

private lemma infinitePlace_localDegree_eq
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L)
    (hw : w ∈ v.placesOver L) :
    arithmeticPlaceLocalDegree (.inr w) =
      v.inertiaDeg w * arithmeticPlaceLocalDegree (.inr v) := by
  haveI : w.1.LiesOver v.1 := hw
  have hcomap := NumberField.InfinitePlace.LiesOver.comap_eq w v
  by_cases hu : w.IsUnramified K
  · have hi := NumberField.InfinitePlace.inertiaDeg_eq_one
      (show w ∈ v.unramifiedPlacesOver L from ⟨hw, hu⟩)
    rw [arithmeticPlaceLocalDegree, arithmeticPlaceLocalDegree, hi, one_mul]
    simpa [hcomap] using hu.eq.symm
  · have hi := NumberField.InfinitePlace.inertiaDeg_eq_two
      (show w ∈ v.ramifiedPlacesOver L from ⟨hw, hu⟩)
    have hr : w.IsRamified K := hu
    have hwComplex : ¬w.IsReal :=
      NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr hr.isComplex
    have hvReal : v.IsReal := by
      rw [← hcomap]
      exact hr.isReal
    rw [arithmeticPlaceLocalDegree, arithmeticPlaceLocalDegree, hi]
    simp [NumberField.InfinitePlace.mult, hwComplex, hvReal]

private lemma pullbackLocalDegreeSum_eq
    (E : Finset (ArithmeticPlace K)) :
    pullbackLocalDegreeSum (L := L) E =
      (Module.finrank K L : ℝ) *
        ∑ v ∈ E, (arithmeticPlaceLocalDegree v : ℝ) := by
  classical
  rw [pullbackLocalDegreeSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  cases v with
  | inl v =>
      simp_rw [finitePlace_localDegree_eq]
      simp only [Nat.cast_mul]
      have hsum := Ideal.sum_ramification_inertia_eq_finrank
        v.maximalIdeal.asIdeal (𝓞 L)
      rw [ringOfIntegers_finrank_eq (K := K) (L := L)] at hsum
      have hsumR : (∑ q : v.maximalIdeal.asIdeal.primesOver (𝓞 L),
          (q.1.ramificationIdx (𝓞 K) : ℝ) * q.1.inertiaDeg (𝓞 K)) =
          (Module.finrank K L : ℝ) := by exact_mod_cast hsum
      rw [← hsumR, Finset.sum_mul]
  | inr v =>
      have hsum := NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank K L v
      have hsumR : (∑ w ∈ (v.placesOver L).toFinset, (v.inertiaDeg w : ℝ)) =
          (Module.finrank K L : ℝ) := by exact_mod_cast hsum
      simp only [arithmeticPlaceLocalDegree]
      rw [← hsumR, Finset.sum_mul]
      calc
        (∑ w : NumberField.InfinitePlace L,
            if w ∈ v.placesOver L then (w.mult : ℝ) else 0) =
            ∑ w ∈ Finset.univ.filter (fun w => w ∈ v.placesOver L),
              (w.mult : ℝ) :=
          (Finset.sum_filter (fun w : NumberField.InfinitePlace L => w ∈ v.placesOver L)
            (fun w => (w.mult : ℝ))).symm
        _ = ∑ w ∈ Finset.univ.filter (fun w => w ∈ v.placesOver L),
              (v.inertiaDeg w : ℝ) * v.mult := by
          apply Finset.sum_congr rfl
          intro w hw
          have hw' : w ∈ v.placesOver L := by simpa using hw
          exact_mod_cast infinitePlace_localDegree_eq v w hw'
        _ = ∑ w ∈ (v.placesOver L).toFinset,
              (v.inertiaDeg w : ℝ) * v.mult := by
          congr 1
          ext w
          simp

private lemma localDegreeSum_pos
    (E : Finset (ArithmeticPlace K)) (hE : E.Nonempty) :
    0 < ∑ v ∈ E, (arithmeticPlaceLocalDegree v : ℝ) := by
  apply Finset.sum_pos
  · intro v hv
    exact_mod_cast arithmeticPlaceLocalDegree_pos v
  · simpa using hE

/-- Definition 1.9(ii): normalized local degree is invariant after pulling back
both the divisor part and its finite/infinite place fibers. -/
theorem normalizedLocalDegree_pullback
    (D : ArithmeticDivisor K) (E : Finset (ArithmeticPlace K))
    (hE : E.Nonempty) :
    arithmeticDivisorDegree
          (arithmeticDivisorPullback (L := L)
            (arithmeticDivisorPart D (· ∈ E))) /
        pullbackLocalDegreeSum (L := L) E =
      normalizedLocalDegree D E := by
  rw [arithmeticDivisorDegree_pullback, pullbackLocalDegreeSum_eq,
    normalizedLocalDegree]
  have hExt : (Module.finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank K L).ne'
  have hLocal : (∑ v ∈ E, (arithmeticPlaceLocalDegree v : ℝ)) ≠ 0 :=
    (localDegreeSum_pos E hE).ne'
  field_simp

end Extension

end Iut4Sec1
