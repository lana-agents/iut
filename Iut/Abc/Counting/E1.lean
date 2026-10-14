/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Abc.Counting.V6

/-!
# Theorem E1(k): the height-restricted count with an explicit saving

This file proves the counting reduction of Theorem E1(k) of the LANA note `V5V7.md` §4. Let
`k ≥ 1`, let `ℓ ∣ k` (in the application a prime `ℓ ≥ 7`, with `μ = μ_ℓ = |PSL₂(𝔽_ℓ)|`) and
`0 < κ` with `2 κ k < μ`. Then

  `#{E ∈ 𝒮_k(X) : H(j(E)) ≤ X ^ κ} ≪_ε X ^ (1 / k - δ + ε)`,
  `δ = (μ - 2 κ k) / (k μ (2 k + 1))`.

For `k = ℓ = 7`, `μ = 168`, `κ = 1` this is `#Π₇₈(X) ≪ X ^ (169 / 1260 + ε)`, `δ = 11 / 1260`.

The cited inputs are bundled in `Iut.Abc.Counting.E1Inputs`:
* the conductor formula and Duke–Kowalski Prop. 1 (Region I, as for V6);
* `CurveData.TwistClassCount` (Lemma 3.1 of `V5V7.md`, from the refined Serre conjecture for
  `ℓ ≥ 5`, i.e. Khare–Wintenberger and Diamond, with Carayol–Livné): the classes `ρ = E[ℓ]`
  met by `𝒞_ℓ(T)` number `≪_η T ^ (1 + η)`;
* `CurveData.PerTwistHeightCount` (Lemma 2.1 of `V5V7.md`, from the uniform Bombieri–Pila
  bound of Castryck–Cluckers–Dittmann–Nguyen, Thm 2, on an `m`-canonical model of the twisted
  modular curve `X_ρ(ℓ)`): the curves of `𝒞_ℓ(T)` with a fixed class `ρ` and `H(j) ≤ Y`
  number `≪_η T ^ η Y ^ (2 / μ + η)`.

## Main results

* `CurveData.perT_count_e1`: the two lemmas combined, `≪ T ^ (1 + 2 η) Y ^ (2 / μ + η)`.
* `CurveData.regionII_e1`: Region II, `≪ X ^ (β (2 + 2 η) + κ (2 / μ + η))`.
* `CurveData.thmE1`: Theorem E1(k).
* `CurveData.thmE1_pi78`: the case `k = 7`, `κ = 1`: exponent `169 / 1260 + ε`.
-/

namespace Iut.Abc.Counting

open Finset

namespace CurveData

variable {ι : Type*} (M : CurveData ι)

/-- **Hypothesis** (Lemma 3.1 of `V5V7.md`; refined Serre for `ℓ ≥ 5`, Carayol–Livné). For
every `η > 0` there is `c` such that, for squarefree `T` prime to `6`, the values of `ρ` on any
finite subset of `𝒞_ℓ(T)` lie in a set of at most `c T ^ (1 + η)` classes. -/
def TwistClassCount {R : Type*} (rho : ι → R) (ℓ : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 →
    ∀ s : Finset ι, (∀ E ∈ s, E ∈ M.twistFamily ℓ T) →
      ∃ t : Finset R, (∀ E ∈ s, rho E ∈ t) ∧ (t.card : ℝ) ≤ c * (T : ℝ) ^ (1 + η)

/-- **Hypothesis** (Lemma 2.1 of `V5V7.md`; CCDN Thm 2, Minkowski, Serre's local discriminant
bound, the Weil height machine on the fixed curve `X_{E₀[ℓ]}(ℓ)`, and the twist multiplicity
of `j`). For every `η > 0` there is `c` such that, for squarefree `T` prime to `6`, every class
`r` and every `Y ≥ 1`, the curves of `𝒞_ℓ(T)` with `ρ(E) = r` and `H(j(E)) ≤ Y` number at most
`c T ^ η Y ^ (2 / μ + η)`. -/
def PerTwistHeightCount {R : Type*} (rho : ι → R) (height : ι → ℝ) (ℓ : ℕ) (μ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 ≤ c ∧ ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ r : R,
    ∀ Y : ℝ, 1 ≤ Y → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.twistFamily ℓ T ∧ rho E = r ∧ height E ≤ Y) →
        (s.card : ℝ) ≤ c * (T : ℝ) ^ η * Y ^ (2 / μ + η)

end CurveData

/-- The cited inputs of Theorem E1(k) at the prime `ℓ ∣ k` with `μ = μ_ℓ`, as hypotheses.
`R` is a type of isomorphism classes of mod-`ℓ` representations, `rho E` the class of `E[ℓ]`
and `height E` the naive height `H(j(E))`. -/
structure E1Inputs {ι : Type*} (M : CurveData ι) (R : Type*) (ℓ : ℕ) (μ : ℝ) where
  /-- Ogg's formula off `6` and the Brumer–Kramer bounds `f₂ ≤ 8`, `f₃ ≤ 5`. -/
  conductorFormula : M.ConductorFormula
  /-- Duke–Kowalski, Invent. Math. 139 (2000), Prop. 1. -/
  dukeKowalski : M.DukeKowalski
  /-- The class of the mod-`ℓ` representation `E[ℓ]` (with its Weil pairing). -/
  rho : ι → R
  /-- The naive height `H(j(E))`. -/
  height : ι → ℝ
  /-- Lemma 3.1 of `V5V7.md`. -/
  twistClasses : M.TwistClassCount rho ℓ
  /-- Lemma 2.1 of `V5V7.md`. -/
  perTwist : M.PerTwistHeightCount rho height ℓ μ

namespace CurveData

variable {ι : Type*} (M : CurveData ι)

/-- Lemmas 3.1 and 2.1 combined: for squarefree `T` prime to `6` and `Y ≥ 1`, the curves of
`𝒞_ℓ(T)` with `H(j) ≤ Y` number at most `c₁ c₂ T ^ (1 + 2 η) Y ^ (2 / μ + η)`. -/
theorem perT_count_e1 {R : Type*} {rho : ι → R} {height : ι → ℝ} {ℓ : ℕ} {μ c₁ c₂ η : ℝ}
    (hc₂ : 0 ≤ c₂)
    (htc : ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.twistFamily ℓ T) →
        ∃ t : Finset R, (∀ E ∈ s, rho E ∈ t) ∧ (t.card : ℝ) ≤ c₁ * (T : ℝ) ^ (1 + η))
    (hpt : ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ r : R, ∀ Y : ℝ, 1 ≤ Y →
      ∀ s : Finset ι, (∀ E ∈ s, E ∈ M.twistFamily ℓ T ∧ rho E = r ∧ height E ≤ Y) →
        (s.card : ℝ) ≤ c₂ * (T : ℝ) ^ η * Y ^ (2 / μ + η))
    {T : ℕ} (hT : Squarefree T) (hT6 : Nat.Coprime T 6) {Y : ℝ} (hY : 1 ≤ Y)
    (s : Finset ι) (hs : ∀ E ∈ s, E ∈ M.twistFamily ℓ T ∧ height E ≤ Y) :
    (s.card : ℝ) ≤ c₁ * c₂ * (T : ℝ) ^ (1 + 2 * η) * Y ^ (2 / μ + η) := by
  classical
  obtain ⟨t, hts, htcard⟩ := htc T hT hT6 s fun E hE => (hs E hE).1
  have hT0 : (0 : ℝ) < T := by exact_mod_cast Nat.pos_of_ne_zero hT.ne_zero
  have hmaps : (s : Set ι).MapsTo rho t := fun E hE => hts E hE
  set B := c₂ * (T : ℝ) ^ η * Y ^ (2 / μ + η) with hB
  have hB0 : 0 ≤ B := by positivity
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc ∑ r ∈ t, (#{E ∈ s | rho E = r} : ℝ) ≤ ∑ _r ∈ t, B := by
        apply sum_le_sum
        intro r _
        apply hpt T hT hT6 r Y hY
        intro E hE
        obtain ⟨hEs, hEr⟩ := mem_filter.mp hE
        exact ⟨(hs E hEs).1, hEr, (hs E hEs).2⟩
    _ = t.card * B := by simp
    _ ≤ (c₁ * (T : ℝ) ^ (1 + η)) * B := by gcongr
    _ = c₁ * c₂ * (T : ℝ) ^ (1 + 2 * η) * Y ^ (2 / μ + η) := by
        rw [hB, show (1 + 2 * η) = (1 + η) + η by ring, Real.rpow_add hT0 (1 + η) η]; ring

/-- **Region II** of Theorem E1(k). Let `ℓ ∣ k`, `κ ≥ 0`, and let `c₁ T ^ (1 + η)`, `c₂ T ^ η`
be the bounds of Lemmas 3.1 and 2.1 (`c₁ ≥ 0`, `c₂ ≥ 0`). For every `β` and `X ≥ 1`, the curves
of `𝒮_k(X)` with `H(j) ≤ X ^ κ` and `T_k(E) ≤ X ^ β` number at most
`c₁ c₂ X ^ (β (2 + 2 η) + κ (2 / μ + η))`. -/
theorem regionII_e1 {R : Type*} {rho : ι → R} {height : ι → ℝ} {k ℓ : ℕ} {μ c₁ c₂ η κ β : ℝ}
    (hℓ : ℓ ∣ k) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hη : 0 ≤ η) (hκ : 0 ≤ κ)
    (htc : ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.twistFamily ℓ T) →
        ∃ t : Finset R, (∀ E ∈ s, rho E ∈ t) ∧ (t.card : ℝ) ≤ c₁ * (T : ℝ) ^ (1 + η))
    (hpt : ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ r : R, ∀ Y : ℝ, 1 ≤ Y →
      ∀ s : Finset ι, (∀ E ∈ s, E ∈ M.twistFamily ℓ T ∧ rho E = r ∧ height E ≤ Y) →
        (s.card : ℝ) ≤ c₂ * (T : ℝ) ^ η * Y ^ (2 / μ + η))
    {X : ℝ} (hX : 1 ≤ X) (s : Finset ι)
    (hs : ∀ E ∈ s, E ∈ M.S k X ∧ height E ≤ X ^ κ ∧ (M.T k E : ℝ) ≤ X ^ β) :
    (s.card : ℝ) ≤ c₁ * c₂ * X ^ (β * (2 + 2 * η) + κ * (2 / μ + η)) := by
  have hX0 : 0 < X := by linarith
  have hXβ : 0 ≤ X ^ β := (Real.rpow_pos_of_pos hX0 β).le
  have hY : 1 ≤ X ^ κ := Real.one_le_rpow hX hκ
  set N := ⌊X ^ β⌋₊
  set B := c₁ * c₂ * X ^ (β * (1 + 2 * η)) * X ^ (κ * (2 / μ + η)) with hB
  have hfib : ∀ t : ℕ, 1 ≤ t → t ≤ N → (#{E ∈ s | M.T k E = t} : ℝ) ≤ B := by
    intro t _ htN
    have htX : (t : ℝ) ≤ X ^ β := le_trans (by exact_mod_cast htN) (Nat.floor_le hXβ)
    have hpow : (t : ℝ) ^ (1 + 2 * η) ≤ X ^ (β * (1 + 2 * η)) := by
      rw [Real.rpow_mul hX0.le]
      exact Real.rpow_le_rpow (by positivity) htX (by positivity)
    by_cases hne : (s.filter fun E => M.T k E = t).Nonempty
    · obtain ⟨E₀, hE₀⟩ := hne
      have hE₀' := (mem_filter.mp hE₀).2
      have hsq : Squarefree t := hE₀' ▸ M.T_squarefree k E₀
      have hco : Nat.Coprime t 6 := hE₀' ▸ M.T_coprime_six k E₀
      calc (#{E ∈ s | M.T k E = t} : ℝ)
          ≤ c₁ * c₂ * (t : ℝ) ^ (1 + 2 * η) * (X ^ κ) ^ (2 / μ + η) := by
            apply M.perT_count_e1 hc₂ htc hpt hsq hco hY
            intro E hE
            obtain ⟨hEs, hEt⟩ := mem_filter.mp hE
            rw [← hEt]
            exact ⟨M.mem_twistFamily_of_mem_S (hs E hEs).1 hℓ, (hs E hEs).2.1⟩
        _ ≤ B := by
            rw [hB, ← Real.rpow_mul hX0.le]
            gcongr
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
      positivity
  have hf : ∀ E ∈ s, 1 ≤ M.T k E ∧ M.T k E ≤ N := fun E hE =>
    ⟨M.T_pos k E, Nat.le_floor (hs E hE).2.2⟩
  calc (s.card : ℝ) ≤ N * B := card_le_of_fibres (M.T k) N hf hfib
    _ ≤ X ^ β * B := by gcongr; exact Nat.floor_le hXβ
    _ = c₁ * c₂ * X ^ (β * (2 + 2 * η) + κ * (2 / μ + η)) := by
        rw [hB, show β * (2 + 2 * η) + κ * (2 / μ + η) =
          β + β * (1 + 2 * η) + κ * (2 / μ + η) by ring,
          Real.rpow_add hX0, Real.rpow_add hX0]
        ring

/-- **Theorem E1(k)** (`V5V7.md` §4), from the cited inputs. Let `1 ≤ k`, `ℓ ∣ k`, `0 < κ`
and `2 κ k < μ`. For every `ε > 0` there is `c` with
`#{E ∈ s} ≤ c X ^ (1 / k - δ + ε)` for every `X ≥ 1` and every finite set `s` of curves in
`𝒮_k(X)` with `H(j(E)) ≤ X ^ κ`, where `δ = deltaE1 k κ μ = (μ - 2 κ k) / (k μ (2 k + 1))`. -/
theorem thmE1 {R : Type*} {k ℓ : ℕ} {μ : ℝ} (h : E1Inputs M R ℓ μ) (hℓ : ℓ ∣ k) (hk : 1 ≤ k)
    {κ : ℝ} (hκ : 0 < κ) (hμ : 2 * κ * k < μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.S k X ∧ h.height E ≤ X ^ κ) →
        (s.card : ℝ) ≤ c * X ^ (1 / k - deltaE1 k κ μ + ε) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hμ0 : 0 < μ := by nlinarith
  set β := betaE1 k κ μ with hβdef
  have hβ0 : 0 < β := betaE1_pos hk0.le hμ hκ.le
  have hβ1 : β ≤ 1 := betaE1_le_one hk0.le hμ hκ.le
  obtain ⟨hbal1, hbal2⟩ := betaE1_balance (κ := κ) hk0 hμ0
  set η := ε / (2 * β + κ) with hηdef
  have hden : 0 < 2 * β + κ := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨cI, hcI, hI⟩ := M.regionI h.conductorFormula h.dukeKowalski hk hβ0.le hβ1 hε
  obtain ⟨c₁, hc₁, htc⟩ := h.twistClasses η hη
  obtain ⟨c₂, hc₂, hpt⟩ := h.perTwist η hη
  have hexp : β * (2 + 2 * η) + κ * (2 / μ + η) = (1 - β) / k + ε := by
    have : η * (2 * β + κ) = ε := by rw [hηdef]; field_simp
    rw [← hbal1]
    linear_combination this
  refine ⟨cI + c₁ * c₂, by positivity, fun X hX s hs => ?_⟩
  rw [← card_filter_add_card_filter_not (fun E => X ^ β < M.T k E)]
  push_cast
  have hA := hI X hX _ fun E hE => ⟨(hs E (mem_filter.mp hE).1).1, (mem_filter.mp hE).2⟩
  have hB := M.regionII_e1 (β := β) hℓ hc₁ hc₂ hη.le hκ.le htc hpt hX _ fun E hE =>
    ⟨(hs E (mem_filter.mp hE).1).1, (hs E (mem_filter.mp hE).1).2,
      not_lt.mp (mem_filter.mp hE).2⟩
  rw [hexp] at hB
  rw [← hbal2]
  linarith

/-- **Theorem E1 for `Π₇₈`** (`k = ℓ = 7`, `μ = μ_7 = 168`, `κ = 1`): the curves of `𝒮_7(X)`
with `H(j(E)) ≤ X` (which contain `Π₇₈(X)`, where `|j| ≤ 1`) number
`≪_ε X ^ (169 / 1260 + ε)`, i.e. `δ = 11 / 1260`. -/
theorem thmE1_pi78 {R : Type*} (h : E1Inputs M R 7 168) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.S 7 X ∧ h.height E ≤ X) →
        (s.card : ℝ) ≤ c * X ^ ((169 : ℝ) / 1260 + ε) := by
  obtain ⟨c, hc, hE1⟩ := M.thmE1 h (dvd_refl 7) (by norm_num) one_pos (by norm_num) hε
  refine ⟨c, hc, fun X hX s hs => ?_⟩
  have := hE1 X hX s fun E hE => ⟨(hs E hE).1, by rw [Real.rpow_one]; exact (hs E hE).2⟩
  rwa [Nat.cast_ofNat, exponentE1_pi78.2] at this

end CurveData

end Iut.Abc.Counting
