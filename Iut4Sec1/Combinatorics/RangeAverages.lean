/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib

/-!
# Arithmetic progression averages

This file proves the elementary identities (E1) and (E2) used in the proof of
Theorem 1.10.
-/

namespace Iut4Sec1

private lemma range_succ_sum (n : ℕ) :
    ∑ m ∈ Finset.range n, (m + 1 : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private lemma range_succ_sq_sum (n : ℕ) :
    ∑ m ∈ Finset.range n, (m + 1 : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- Identity (E1): the average of `1, ..., n` is `(n + 1) / 2`. -/
theorem average_range_sum (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) =
      ((n : ℝ) + 1) / 2 := by
  rw [range_succ_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Identity (E2): the average of the squares `1², ..., n²`. -/
theorem average_range_sq_sum (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) ^ 2 =
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) / 6 := by
  rw [range_succ_sq_sum]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end Iut4Sec1
