/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Abc.Counting.Basic

/-!
# Theorem V6: semistable curves with `k`-full discriminant

This file proves the counting reduction of Theorem V6 of the LANA note `V6.md`:

  `#𝒮_k(X) ≪_{k,ε} X ^ (1 / k - δ_k + ε)`,  `δ_k = 1 / (k (k (C + 1) + 1))`,

from three cited inputs, bundled as the hypotheses of `Iut.Abc.Counting.V6Inputs`:

* the conductor formula `N_E = 2 ^ f₂ 3 ^ f₃ rad(Δ′)`, `f₂ ≤ 8`, `f₃ ≤ 5`;
* Duke–Kowalski, Invent. Math. 139 (2000), Prop. 1;
* Prop S3.2(k), the uniform bound `#𝒞_k(T) ≤ C₀ T ^ C` (true for `k ≥ 7` by `V6.md` §2;
  the reduction itself works for every `k ≥ 1`).

The proof splits `𝒮_k(X)` at `T_k(E) = X ^ β`, `β = 1 / (k (C + 1) + 1)`.
* Region I (`T > X ^ β`) is `CurveData.regionI`.
* Region II (`T ≤ X ^ β`) is `CurveData.regionII_v6`: it sums the uniform bound over the at
  most `X ^ β` values of `T`.
The balance `(1 - β) / k = β (C + 1) = 1 / k - δ_k` is `betaV6_balance`.

## Main results

* `Iut.Abc.Counting.CurveData.thmV6`: Theorem V6, for finite subsets of `𝒮_k(X)`.
* `Iut.Abc.Counting.CurveData.thmV6_ncard`: `𝒮_k(X)` is finite and
  `#𝒮_k(X) ≤ c X ^ (1 / k - δ_k + ε)`.
* `Iut.Abc.Counting.CurveData.thmV6_seven`: at `k = 7` the saving is `1 / (7 (7 C + 8))`, the
  `δ′` of Theorem U1.B.
-/

namespace Iut.Abc.Counting

open Finset

/-- The cited inputs of Theorem V6 at level `k`, as hypotheses. -/
structure V6Inputs {ι : Type*} (M : CurveData ι) (k : ℕ) where
  /-- Ogg's formula off `6` and the Brumer–Kramer bounds `f₂ ≤ 8`, `f₃ ≤ 5`. -/
  conductorFormula : M.ConductorFormula
  /-- Duke–Kowalski, Invent. Math. 139 (2000), Prop. 1. -/
  dukeKowalski : M.DukeKowalski
  /-- The multiplier `C₀(k)` of Prop S3.2(k). -/
  C₀ : ℝ
  /-- The exponent `C(k)` of Prop S3.2(k). -/
  C : ℝ
  /-- Prop S3.2(k): `#𝒞_k(T) ≤ C₀ T ^ C`. -/
  uniform : M.UniformTwistBound k C₀ C

namespace CurveData

variable {ι : Type*} (M : CurveData ι)

/-- **Region II** of Theorem V6. Given Prop S3.2(k) with parameters `C₀, C`, for every `β` the
curves of `𝒮_k(X)` with `T_k(E) ≤ X ^ β` number at most `C₀ X ^ (β (C + 1))`. -/
theorem regionII_v6 {k : ℕ} {C₀ C : ℝ} (h : M.UniformTwistBound k C₀ C) {β : ℝ}
    {X : ℝ} (hX : 1 ≤ X) (s : Finset ι)
    (hs : ∀ E ∈ s, E ∈ M.S k X ∧ (M.T k E : ℝ) ≤ X ^ β) :
    (s.card : ℝ) ≤ C₀ * X ^ (β * (C + 1)) := by
  obtain ⟨hC₀, hC, hb⟩ := h
  have hX0 : 0 < X := by linarith
  have hXβ : 0 ≤ X ^ β := (Real.rpow_pos_of_pos hX0 β).le
  set N := ⌊X ^ β⌋₊ with hN
  have hfib : ∀ t : ℕ, 1 ≤ t → t ≤ N →
      (#{E ∈ s | M.T k E = t} : ℝ) ≤ C₀ * X ^ (β * C) := by
    intro t ht1 htN
    have htX : (t : ℝ) ≤ X ^ β := le_trans (by exact_mod_cast htN) (Nat.floor_le hXβ)
    have hpow : (t : ℝ) ^ C ≤ X ^ (β * C) := by
      rw [Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow (by positivity) htX hC
    by_cases hne : (s.filter fun E => M.T k E = t).Nonempty
    · obtain ⟨E₀, hE₀⟩ := hne
      have hE₀' := (mem_filter.mp hE₀).2
      have hsq : Squarefree t := hE₀' ▸ M.T_squarefree k E₀
      have hco : Nat.Coprime t 6 := hE₀' ▸ M.T_coprime_six k E₀
      calc (#{E ∈ s | M.T k E = t} : ℝ) ≤ C₀ * (t : ℝ) ^ C := by
            apply hb t hsq hco
            intro E hE
            obtain ⟨hEs, hEt⟩ := mem_filter.mp hE
            rw [← hEt]
            exact M.mem_twistFamily_of_mem_S (hs E hEs).1 (dvd_refl k)
        _ ≤ C₀ * X ^ (β * C) := by gcongr
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
      positivity
  have hf : ∀ E ∈ s, 1 ≤ M.T k E ∧ M.T k E ≤ N := fun E hE =>
    ⟨M.T_pos k E, Nat.le_floor (hs E hE).2⟩
  calc (s.card : ℝ) ≤ N * (C₀ * X ^ (β * C)) := card_le_of_fibres (M.T k) N hf hfib
    _ ≤ X ^ β * (C₀ * X ^ (β * C)) := by gcongr; exact Nat.floor_le hXβ
    _ = C₀ * X ^ (β * (C + 1)) := by
        rw [mul_add, mul_one, Real.rpow_add hX0]; ring

/-- **Theorem V6** (`V6.md` §1), from the cited inputs. For every `ε > 0` there is `c` with
`#s ≤ c X ^ (1 / k - δ_k + ε)` for every finite `s ⊆ 𝒮_k(X)` and every `X ≥ 1`, where
`δ_k = 1 / (k (k (C + 1) + 1))` and `C` is the exponent of Prop S3.2(k). -/
theorem thmV6 {k : ℕ} (h : V6Inputs M k) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset ι, (∀ E ∈ s, E ∈ M.S k X) →
      (s.card : ℝ) ≤ c * X ^ (1 / k - deltaV6 k h.C + ε) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hC := h.uniform.2.1
  set β := betaV6 k h.C
  obtain ⟨c₁, hc₁, hI⟩ := M.regionI h.conductorFormula h.dukeKowalski hk
    (betaV6_pos hk0.le hC).le (betaV6_le_one hk0.le hC) hε
  refine ⟨c₁ + h.C₀, add_nonneg hc₁ h.uniform.1, fun X hX s hs => ?_⟩
  rw [← card_filter_add_card_filter_not (fun E => X ^ β < M.T k E)]
  push_cast
  apply balance_v6 hk0 hC hX hc₁ h.uniform.1 hε.le
  · exact hI X hX _ fun E hE => ⟨hs E (mem_filter.mp hE).1, (mem_filter.mp hE).2⟩
  · exact M.regionII_v6 h.uniform hX _ fun E hE =>
      ⟨hs E (mem_filter.mp hE).1, not_lt.mp (mem_filter.mp hE).2⟩

/-- **Theorem V6**, as a statement about `𝒮_k(X)` itself: it is finite, and
`#𝒮_k(X) ≤ c X ^ (1 / k - δ_k + ε)` for `X ≥ 1`. -/
theorem thmV6_ncard {k : ℕ} (h : V6Inputs M k) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X →
      (M.S k X).Finite ∧ ((M.S k X).ncard : ℝ) ≤ c * X ^ (1 / k - deltaV6 k h.C + ε) := by
  obtain ⟨c, hc, hV6⟩ := M.thmV6 h hk hε
  exact ⟨c, hc, fun X hX => ncard_le_of_forall_finset (hV6 X hX)⟩

/-- **Theorem V6 at `k = 7`**: `#𝒮_7(X) ≤ c X ^ (1 / 7 - 1 / (7 (7 C + 8)) + ε)`, the bound
of Theorem U1.B (whose set `𝒫(X)` is contained in `𝒮_7(X)`). -/
theorem thmV6_seven (h : V6Inputs M 7) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset ι, (∀ E ∈ s, E ∈ M.S 7 X) →
      (s.card : ℝ) ≤ c * X ^ (1 / 7 - 1 / (7 * (7 * h.C + 8)) + ε) := by
  obtain ⟨c, hc, hV6⟩ := M.thmV6 h (by norm_num) hε
  refine ⟨c, hc, fun X hX s hs => ?_⟩
  have := hV6 X hX s hs
  rwa [Nat.cast_ofNat, deltaV6_seven] at this

end CurveData

end Iut.Abc.Counting
