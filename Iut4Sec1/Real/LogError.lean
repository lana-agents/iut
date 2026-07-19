/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib

/-!
# Nonarchimedean logarithmic errors

This file proves the elementary ceiling estimate used in the numerical core of
Proposition 1.4(iii) of *Inter-universal Teichmüller Theory IV*.
-/

namespace Iut4Sec1

noncomputable def nonarchimedeanLogError (p e : ℕ) : ℝ :=
  ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e - 1 / e

lemma nonarchimedeanLogError_nonneg (p e : ℕ) (hp2 : 2 < p) (he : 0 < e) :
    0 ≤ nonarchimedeanLogError p e := by
  have hd_nat : 0 < p - 2 := Nat.sub_pos_of_lt hp2
  have he_real : 0 < (e : ℝ) := by exact_mod_cast he
  have hd_real : 0 < ((p - 2 : ℕ) : ℝ) := by exact_mod_cast hd_nat
  have hx : 0 < (e : ℝ) / (p - 2 : ℕ) := div_pos he_real hd_real
  have hceil : (1 : ℝ) ≤ ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) := by
    exact_mod_cast (Int.ceil_pos.mpr hx)
  rw [nonarchimedeanLogError]
  exact sub_nonneg.mpr (div_le_div_of_nonneg_right hceil he_real.le)

lemma nonarchimedeanLogError_eq_zero_of_le (p e : ℕ) (hp2 : 2 < p)
    (he : 0 < e) (hle : e ≤ p - 2) :
    nonarchimedeanLogError p e = 0 := by
  have hd_nat : 0 < p - 2 := Nat.sub_pos_of_lt hp2
  have he_real : 0 < (e : ℝ) := by exact_mod_cast he
  have hd_real : 0 < ((p - 2 : ℕ) : ℝ) := by exact_mod_cast hd_nat
  have hx_pos : 0 < (e : ℝ) / (p - 2 : ℕ) := div_pos he_real hd_real
  have hx_le : (e : ℝ) / (p - 2 : ℕ) ≤ 1 := by
    rw [div_le_one hd_real]
    exact_mod_cast hle
  have hceil : ⌈(e : ℝ) / (p - 2 : ℕ)⌉ = (1 : ℤ) := by
    rw [Int.ceil_eq_iff]
    norm_num
    exact ⟨hx_pos, hx_le⟩
  simp [nonarchimedeanLogError, hceil]

lemma nonarchimedeanLogError_le_four_div (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (he : 0 < e) : nonarchimedeanLogError p e ≤ 4 / (p : ℝ) := by
  have hd_nat : 0 < p - 2 := Nat.sub_pos_of_lt hp2
  have he_real : 0 < (e : ℝ) := by exact_mod_cast he
  have hd_real : 0 < ((p - 2 : ℕ) : ℝ) := by exact_mod_cast hd_nat
  have hp_real : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hceil := Int.ceil_lt_add_one ((e : ℝ) / (p - 2 : ℕ))
  have herr_lt : nonarchimedeanLogError p e < 1 / ((p - 2 : ℕ) : ℝ) := by
    rw [nonarchimedeanLogError]
    apply (sub_lt_iff_lt_add).2
    have hid : 1 / ((p - 2 : ℕ) : ℝ) + 1 / (e : ℝ) =
        ((e : ℝ) / (p - 2 : ℕ) + 1) / e := by
      field_simp
    rw [hid]
    exact (div_lt_div_iff_of_pos_right he_real).2 hceil
  have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
    rw [Nat.cast_sub hp2.le]
    norm_num
  have hdenom : 1 / ((p - 2 : ℕ) : ℝ) ≤ 4 / (p : ℝ) := by
    rw [hcast]
    apply (div_le_div_iff₀ (by rw [← hcast]; exact hd_real) hp_real).2
    nlinarith [show (3 : ℝ) ≤ p by exact_mod_cast hp2]
  exact herr_lt.le.trans hdenom

/-- The total ceiling error is supported on the exceptional index set. -/
theorem nonarchimedean_logError_sum_le {ι : Type*} [DecidableEq ι]
    (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hIstar : Istar ⊆ I)
    (he : ∀ i ∈ I, 0 < e i)
    (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
    ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
      4 * (Istar.card : ℝ) / p := by
  have hpointwise : ∀ i ∈ I, nonarchimedeanLogError p (e i) ≤
      if i ∈ Istar then 4 / (p : ℝ) else 0 := by
    intro i hi
    split_ifs with histar
    · exact nonarchimedeanLogError_le_four_div p (e i) hp hp2 (he i hi)
    · rw [nonarchimedeanLogError_eq_zero_of_le p (e i) hp2 (he i hi)
        (hsmall i hi histar)]
  have hfilter : I.filter (fun i => i ∈ Istar) = Istar := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · exact fun hi => hi.2
    · exact fun hi => ⟨hIstar hi, hi⟩
  calc
    ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
        ∑ i ∈ I, if i ∈ Istar then 4 / (p : ℝ) else 0 :=
      Finset.sum_le_sum fun i hi => hpointwise i hi
    _ = ∑ i ∈ I.filter (fun i => i ∈ Istar), 4 / (p : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ _i ∈ Istar, 4 / (p : ℝ) := by rw [hfilter]
    _ = 4 * (Istar.card : ℝ) / p := by
      simp
      ring

end Iut4Sec1
