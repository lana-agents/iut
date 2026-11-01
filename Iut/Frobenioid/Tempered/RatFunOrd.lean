/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunDiv

/-!
# Orders of zeros of entire Laurent series; the cuspidal divisor of `Θ̈` (MR18 T8, B-an)

For `f ∈ E(K)`, `f ≠ 0`, and `α ∈ Kˣ`, the **order of `f` at `α`** is the unique `k` with
`f = (U - α)^k·g`, `g(α) ≠ 0` (`HasOrderAt`, `ord`). It exists because each division by `U - α`
lowers the width of the Newton polygon on `|U| = ‖α‖` (`RatFunDiv.lean`), and it is unique since
`E(K)` is a domain. It is additive (`ord_mul`), and `ord f α = 0 ↔ f(α) ≠ 0`.

This is the cuspidal part of the divisor of [EtTh] Definition 3.1 on `𝔾_m^an` (orders at the cusp
points); with the Gauss norms on the component circles (`RatFunGauss.lean`) it gives the
log-divisor of a regular function. For `Θ̈`: `ord_thetaDd_cusp` (order `1` at each cusp `±q^{a/2}`)
and `ord_thetaDd_of_not_cusp` (order `0` elsewhere) — **[EtTh] Proposition 1.4(i)** ("the zeroes
of `Θ̈` are precisely the cusps; each zero has multiplicity 1") in `E(K)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open Polynomial TateCurvesTheta TateParameter

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- `f` vanishes to order exactly `k` at `α`. -/
def HasOrderAt (f : Entire K) (α : Kˣ) (k : ℕ) : Prop :=
  ∃ g : Entire K, f = polyE (lin (α : K)) ^ k * g ∧ (g : Kˣ → K) α ≠ 0

lemma polyE_lin_apply_self (α : Kˣ) : ((polyE (lin (α : K)) : Entire K) : Kˣ → K) α = 0 := by
  rw [coe_polyE]; simp

lemma polyE_lin_ne_zero (α : K) : polyE (lin α) ≠ 0 := polyE_ne_zero (X_sub_C_ne_zero α)

/-- **Existence of the order.** -/
theorem exists_hasOrderAt {f : Entire K} (hf : f ≠ 0) (α : Kˣ) : ∃ k, HasOrderAt f α k := by
  have hr : 0 < ‖(α : K)‖ := norm_pos_iff.mpr α.ne_zero
  suffices H : ∀ n : ℕ, ∀ f : Entire K, f ≠ 0 →
      hi (Entire.coeff f) ‖(α : K)‖ - lo (Entire.coeff f) ‖(α : K)‖ ≤ n → ∃ k, HasOrderAt f α k
    from H _ f hf (Int.self_le_toNat _)
  intro n
  induction n with
  | zero =>
    intro f hf hw
    by_cases h0 : (f : Kˣ → K) α = 0
    · obtain ⟨g, rfl⟩ := exists_eq_lin_mul h0
      have hg : g ≠ 0 := by rintro rfl; exact hf (mul_zero _)
      have := width_lin_mul (α := α) hg
      have := lo_le_hi (Entire.isEntire_coeff g) (Entire.coeff_ne_zero hg) hr
      push_cast at hw
      omega
    · exact ⟨0, f, by rw [pow_zero, one_mul], h0⟩
  | succ n ih =>
    intro f hf hw
    by_cases h0 : (f : Kˣ → K) α = 0
    · obtain ⟨g, rfl⟩ := exists_eq_lin_mul h0
      have hg : g ≠ 0 := by rintro rfl; exact hf (mul_zero _)
      have hwg := width_lin_mul (α := α) hg
      obtain ⟨k, g', hg', hg'α⟩ := ih g hg (by push_cast at hw ⊢; omega)
      exact ⟨k + 1, g', by rw [hg', pow_succ]; ring, hg'α⟩
    · exact ⟨0, f, by rw [pow_zero, one_mul], h0⟩

/-- **Uniqueness of the order.** -/
theorem HasOrderAt.unique {f : Entire K} {α : Kˣ} {k l : ℕ} (hk : HasOrderAt f α k)
    (hl : HasOrderAt f α l) : k = l := by
  obtain ⟨g, hg, hgα⟩ := hk
  obtain ⟨g', hg', hg'α⟩ := hl
  have hP := polyE_lin_ne_zero (α : K)
  wlog hkl : k ≤ l generalizing k l g g'
  · exact (this g' hg' hg'α g hg hgα (le_of_not_ge hkl)).symm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rfl
  exfalso
  rw [hg, pow_add, mul_assoc] at hg'
  have hcancel : g = polyE (lin (α : K)) ^ d * g' := mul_left_cancel₀ (pow_ne_zero _ hP) hg'
  apply hgα
  rw [hcancel, Entire.coe_mul, Pi.mul_apply]
  have : ((polyE (lin (α : K)) ^ d : Entire K) : Kˣ → K) α = 0 := by
    rw [show ((polyE (lin (α : K)) ^ d : Entire K) : Kˣ → K) =
      ((polyE (lin (α : K)) : Entire K) : Kˣ → K) ^ d from rfl, Pi.pow_apply,
      polyE_lin_apply_self, zero_pow hd.ne']
  rw [this, zero_mul]

open Classical in
/-- **The order of `f` at `α`** (`0` for `f = 0`). -/
def ord (f : Entire K) (α : Kˣ) : ℕ :=
  if hf : f = 0 then 0 else (exists_hasOrderAt hf α).choose

lemma hasOrderAt_ord {f : Entire K} (hf : f ≠ 0) (α : Kˣ) : HasOrderAt f α (ord f α) := by
  rw [ord, dif_neg hf]; exact (exists_hasOrderAt hf α).choose_spec

lemma ord_eq_of_hasOrderAt {f : Entire K} {α : Kˣ} {k : ℕ} (h : HasOrderAt f α k) :
    ord f α = k := by
  have hf : f ≠ 0 := by
    rintro rfl
    obtain ⟨g, hg, hgα⟩ := h
    have hP := pow_ne_zero k (polyE_lin_ne_zero (α : K))
    rcases mul_eq_zero.mp hg.symm with h1 | h1
    · exact hP h1
    · rw [h1] at hgα; exact hgα rfl
  exact (hasOrderAt_ord hf α).unique h

/-- **The order is additive.** -/
theorem ord_mul {f g : Entire K} (hf : f ≠ 0) (hg : g ≠ 0) (α : Kˣ) :
    ord (f * g) α = ord f α + ord g α := by
  obtain ⟨f₁, hf₁, hf₁α⟩ := hasOrderAt_ord hf α
  obtain ⟨g₁, hg₁, hg₁α⟩ := hasOrderAt_ord hg α
  refine ord_eq_of_hasOrderAt ⟨f₁ * g₁, ?_, ?_⟩
  · conv_lhs => rw [hf₁, hg₁]
    rw [pow_add]; ring
  · rw [Entire.coe_mul, Pi.mul_apply]; exact mul_ne_zero hf₁α hg₁α

/-- `ord f α = 0` iff `f(α) ≠ 0`. -/
theorem ord_eq_zero_iff {f : Entire K} (hf : f ≠ 0) (α : Kˣ) :
    ord f α = 0 ↔ (f : Kˣ → K) α ≠ 0 := by
  constructor
  · intro h0
    obtain ⟨g, hg, hgα⟩ := hasOrderAt_ord hf α
    rw [h0, pow_zero, one_mul] at hg
    rwa [hg]
  · intro h
    exact ord_eq_of_hasOrderAt ⟨f, by rw [pow_zero, one_mul], h⟩

/-! ### The cuspidal divisor of `Θ̈` -/

variable (t : TateParameter K)

/-- **[EtTh] Proposition 1.4(i)**: `Θ̈` has order `1` at each cusp `±q^{a/2}`. -/
theorem ord_thetaDd_cusp (h2 : (2 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (a : ℤ)
    {α : Kˣ} (hα : α = s ^ a ∨ α = -(s ^ a)) : ord (thetaDd t) α = 1 := by
  obtain ⟨h, hh, hhα⟩ := thetaDd_simple_zero t h2 hs a hα
  exact ord_eq_of_hasOrderAt ⟨h, by rw [pow_one]; exact hh, hhα⟩

/-- **[EtTh] Proposition 1.4(i)**: `Θ̈` has order `0` away from the cusps `Ü² ∈ q^ℤ`. -/
theorem ord_thetaDd_of_not_cusp {α : Kˣ} (hα : ¬ ∃ k : ℤ, (α : K) ^ 2 = (t.q : K) ^ k) :
    ord (thetaDd t) α = 0 :=
  (ord_eq_zero_iff (thetaDd_ne_zero t) α).mpr fun h => hα ((thetaDd_eq_zero_iff t α).mp h)

end Iut.Frobenioid.BAn
