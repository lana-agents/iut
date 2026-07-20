/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib

/-!
# Finite weighted averages

This file proves Proposition 1.7 of *Inter-universal Teichmüller Theory IV* and
records the positive finite-weight normalization used for packet averages.
-/

namespace Iut4Sec1

noncomputable def tupleWeight {n : ℕ} {E : Type*}
    (weight : E → ℝ) (x : Fin n → E) : ℝ :=
  ∏ j, weight (x j)

noncomputable def tupleValue {n : ℕ} {E : Type*}
    (β : E → ℝ) (x : Fin n → E) : ℝ :=
  ∑ j, β (x j)

private lemma sum_tupleWeight {E : Type*} [Fintype E] (n : ℕ) (weight : E → ℝ) :
    ∑ x : Fin n → E, tupleWeight weight x = (∑ e : E, weight e) ^ n := by
  calc
    ∑ x : Fin n → E, tupleWeight weight x =
        ∑ x : Fin n → E, ∏ _j : Fin n, weight (x _j) := rfl
    _ = ∏ _j : Fin n, ∑ e : E, weight e :=
      (Fintype.prod_sum (fun _j : Fin n => weight)).symm
    _ = (∑ e : E, weight e) ^ n := by simp

private lemma sum_coordinate_mul_tupleWeight {E : Type*} [Fintype E]
    {n : ℕ} (weight β : E → ℝ) (i : Fin n) :
    ∑ x : Fin n → E, β (x i) * tupleWeight weight x =
      (∑ e : E, β e * weight e) * (∑ e : E, weight e) ^ (n - 1) := by
  let g : Fin n → E → ℝ := fun j e => if j = i then β e * weight e else weight e
  have hprod (x : Fin n → E) :
      (∏ j, g j (x j)) = β (x i) * tupleWeight weight x := by
    classical
    rw [show (∏ j, g j (x j)) =
        g i (x i) * ∏ j ∈ (Finset.univ.erase i), g j (x j) by
      exact (Finset.mul_prod_erase Finset.univ (fun j => g j (x j)) (Finset.mem_univ i)).symm]
    rw [show g i (x i) = β (x i) * weight (x i) by simp [g]]
    have herase : (∏ j ∈ Finset.univ.erase i, g j (x j)) =
        ∏ j ∈ Finset.univ.erase i, weight (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [g, (Finset.mem_erase.mp hj).1]
    rw [herase, tupleWeight, show (∏ j, weight (x j)) =
        weight (x i) * ∏ j ∈ (Finset.univ.erase i), weight (x j) by
      exact (Finset.mul_prod_erase Finset.univ (fun j => weight (x j))
        (Finset.mem_univ i)).symm]
    ring
  calc
    ∑ x : Fin n → E, β (x i) * tupleWeight weight x =
        ∑ x : Fin n → E, ∏ j, g j (x j) := by simp_rw [hprod]
    _ = ∏ j, ∑ e : E, g j e := by rw [Fintype.prod_sum]
    _ = (∑ e : E, β e * weight e) * (∑ e : E, weight e) ^ (n - 1) := by
      classical
      rw [show (∏ j, ∑ e : E, g j e) =
          (∑ e : E, g i e) * ∏ j ∈ (Finset.univ.erase i), ∑ e : E, g j e by
        exact (Finset.mul_prod_erase Finset.univ (fun j => ∑ e : E, g j e)
          (Finset.mem_univ i)).symm]
      rw [show (∑ e : E, g i e) = ∑ e : E, β e * weight e by simp [g]]
      have herase : (∏ j ∈ Finset.univ.erase i, ∑ e : E, g j e) =
          ∏ _j ∈ Finset.univ.erase i, ∑ e : E, weight e := by
        apply Finset.prod_congr rfl
        intro j hj
        simp [g, (Finset.mem_erase.mp hj).1]
      rw [herase, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]

/-- Proposition 1.7: the symmetrized and fixed-coordinate weighted averages agree. -/
theorem weighted_average_eq {E : Type*} [Fintype E] [Nonempty E]
    {n : ℕ} [NeZero n] (weight β : E → ℝ)
    (hweight : ∀ e, 0 < weight e) (i : Fin n) :
    (∑ x : Fin n → E, tupleValue β x * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) =
        (∑ x : Fin n → E, n * β (x i) * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) ∧
      (∑ x : Fin n → E, n * β (x i) * tupleWeight weight x) /
          (∑ x : Fin n → E, tupleWeight weight x) =
        n * ((∑ e : E, β e * weight e) / (∑ e : E, weight e)) := by
  let S : ℝ := ∑ e : E, weight e
  let B : ℝ := ∑ e : E, β e * weight e
  have hS : 0 < S := Finset.sum_pos (fun e _ => hweight e) Finset.univ_nonempty
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hpow : S ^ n = S ^ (n - 1) * S := by
    conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add, pow_one]
  have hdenom : ∑ x : Fin n → E, tupleWeight weight x = S ^ n :=
    sum_tupleWeight n weight
  have hcoord : ∑ x : Fin n → E, β (x i) * tupleWeight weight x = B * S ^ (n - 1) :=
    sum_coordinate_mul_tupleWeight weight β i
  have hfixed : ∑ x : Fin n → E, n * β (x i) * tupleWeight weight x =
      n * (B * S ^ (n - 1)) := by
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [hcoord]
  have hall : ∑ x : Fin n → E, tupleValue β x * tupleWeight weight x =
      n * (B * S ^ (n - 1)) := by
    calc
      ∑ x : Fin n → E, tupleValue β x * tupleWeight weight x =
          ∑ x : Fin n → E, ∑ j : Fin n, β (x j) * tupleWeight weight x := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [tupleValue, Finset.sum_mul]
      _ = ∑ j : Fin n, ∑ x : Fin n → E, β (x j) * tupleWeight weight x :=
        Finset.sum_comm
      _ = ∑ _j : Fin n, B * S ^ (n - 1) := by
        apply Finset.sum_congr rfl
        intro j _
        exact sum_coordinate_mul_tupleWeight weight β j
      _ = n * (B * S ^ (n - 1)) := by simp
  constructor
  · rw [hall, hfixed]
  · rw [hfixed, hdenom, hpow]
    have hpow_ne : S ^ (n - 1) ≠ 0 := pow_ne_zero _ hS.ne'
    rw [show (n : ℝ) * (B * S ^ (n - 1)) =
        ((n : ℝ) * B) * S ^ (n - 1) by ring,
      mul_comm (S ^ (n - 1)) S, mul_div_mul_right _ _ hpow_ne]
    ring

/-! ## Positive packet weights -/

/-- The raw weight of a packet tuple is the product of its positive local degrees. -/
noncomputable def rawPacketWeight {A E : Type*} [Fintype A]
    (localDegree : E → ℝ) (t : A → E) : ℝ :=
  ∏ a, localDegree (t a)

lemma rawPacketWeight_pos {A E : Type*} [Fintype A]
    (localDegree : E → ℝ) (hlocalDegree : ∀ e, 0 < localDegree e) (t : A → E) :
    0 < rawPacketWeight localDegree t := by
  exact Finset.prod_pos fun a _ => hlocalDegree (t a)

lemma rawPacketWeight_sum_pos {A E : Type*} [Fintype A] [DecidableEq A]
    [Fintype E] [Nonempty E]
    (localDegree : E → ℝ) (hlocalDegree : ∀ e, 0 < localDegree e) :
    0 < ∑ t : A → E, rawPacketWeight localDegree t := by
  exact Finset.sum_pos (fun t _ => rawPacketWeight_pos localDegree hlocalDegree t)
    Finset.univ_nonempty

/-- A packet weight normalized by the sum of all raw weights. -/
noncomputable def normalizedPacketWeight {A E : Type*} [Fintype A] [DecidableEq A]
    [Fintype E]
    (localDegree : E → ℝ) (t : A → E) : ℝ :=
  rawPacketWeight localDegree t / ∑ u : A → E, rawPacketWeight localDegree u

lemma normalizedPacketWeight_pos {A E : Type*} [Fintype A] [DecidableEq A]
    [Fintype E] [Nonempty E]
    (localDegree : E → ℝ) (hlocalDegree : ∀ e, 0 < localDegree e) (t : A → E) :
    0 < normalizedPacketWeight localDegree t :=
  div_pos (rawPacketWeight_pos localDegree hlocalDegree t)
    (rawPacketWeight_sum_pos localDegree hlocalDegree)

/-- Positive raw packet weights normalize to a probability distribution. -/
theorem sum_normalizedPacketWeight_eq_one {A E : Type*}
    [Fintype A] [DecidableEq A] [Fintype E] [Nonempty E]
    (localDegree : E → ℝ) (hlocalDegree : ∀ e, 0 < localDegree e) :
    ∑ t : A → E, normalizedPacketWeight localDegree t = 1 := by
  rw [show (∑ t : A → E, normalizedPacketWeight localDegree t) =
      (∑ t : A → E, rawPacketWeight localDegree t) /
        ∑ t : A → E, rawPacketWeight localDegree t by
    simp_rw [normalizedPacketWeight]
    exact (Finset.sum_div Finset.univ
      (fun t : A → E => rawPacketWeight localDegree t)
      (∑ t : A → E, rawPacketWeight localDegree t)).symm]
  exact div_self (rawPacketWeight_sum_pos localDegree hlocalDegree).ne'

end Iut4Sec1
