/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Exponent arithmetic of the counting theorems V6 and E1

This file contains the real-analysis part of the counting reductions of the LANA notes
`V6.md` (Theorem V6) and `V5V7.md` (Theorem E1): the choice of the splitting parameter `β`,
the resulting power saving `δ`, and the "balance" lemma which adds the two regional bounds.

## Main definitions

* `Iut.Abc.Counting.betaV6 k C = 1 / (k (C + 1) + 1)`, the splitting parameter of Theorem V6.
* `Iut.Abc.Counting.deltaV6 k C = 1 / (k (k (C + 1) + 1))`, the power saving `δ_k` of V6.
* `Iut.Abc.Counting.betaE1 k κ μ = (μ - 2 κ k) / (μ (2 k + 1))` and
  `Iut.Abc.Counting.deltaE1 k κ μ = betaE1 k κ μ / k`, the parameters of Theorem E1(k).

## Main results

* `betaV6_balance`: `(1 - β) / k = β (C + 1) = 1 / k - δ_k`.
* `deltaV6_seven`: at `k = 7`, `δ_7 = 1 / (7 (7 C + 8))`, the saving `δ′` of Theorem U1.B.
* `betaE1_balance`: `2 β + 2 κ / μ = (1 - β) / k = 1 / k - δ`.
* `deltaE1_seven`, `deltaE1_eleven`, `deltaE1_thirteen`: the sample values `(12 - κ) / 1260`,
  `29 / 7590`, `41 / 14742`; `exponentE1_pi78`: `1 / 7 - 11 / 1260 = 169 / 1260`.
* `balance_le`, `balance_v6`: two bounds `A ≤ c₁ X ^ (a + ε)` and `B ≤ c₂ X ^ b` with
  `a, b ≤ e` give `A + B ≤ (c₁ + c₂) X ^ (e + ε)` for `X ≥ 1`; in V6 the two exponents agree.
-/

namespace Iut.Abc.Counting

/-- The splitting parameter `β = 1 / (k (C + 1) + 1)` of Theorem V6: curves with `T > X ^ β`
are counted by conductor, the others by the uniform bound `C₀ T ^ C`. -/
noncomputable def betaV6 (k C : ℝ) : ℝ := 1 / (k * (C + 1) + 1)

/-- The power saving `δ_k = 1 / (k (k (C + 1) + 1))` of Theorem V6. -/
noncomputable def deltaV6 (k C : ℝ) : ℝ := 1 / (k * (k * (C + 1) + 1))

theorem betaV6_pos {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C) : 0 < betaV6 k C := by
  unfold betaV6; positivity

theorem betaV6_le_one {k C : ℝ} (hk : 0 ≤ k) (hC : 0 ≤ C) : betaV6 k C ≤ 1 := by
  unfold betaV6
  rw [div_le_one (by positivity)]
  have : 0 ≤ k * (C + 1) := by positivity
  linarith

theorem deltaV6_pos {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C) : 0 < deltaV6 k C := by
  unfold deltaV6; positivity

/-- The balance of Theorem V6: with `β = betaV6 k C`, the Region I exponent `(1 - β) / k`
equals the Region II exponent `β (C + 1)`, and both equal `1 / k - δ_k`. -/
theorem betaV6_balance {k C : ℝ} (hk : 0 < k) (hC : 0 ≤ C) :
    (1 - betaV6 k C) / k = betaV6 k C * (C + 1) ∧
      betaV6 k C * (C + 1) = 1 / k - deltaV6 k C := by
  have h1 : k * (C + 1) + 1 ≠ 0 := by positivity
  have h2 : k ≠ 0 := hk.ne'
  unfold betaV6 deltaV6
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- At `k = 7` the saving of Theorem V6 is the saving `δ′ = 1 / (7 (7 C + 8))` of U1.B. -/
theorem deltaV6_seven (C : ℝ) : deltaV6 7 C = 1 / (7 * (7 * C + 8)) := by
  unfold deltaV6; ring_nf

/-- The splitting parameter `β = (μ - 2 κ k) / (μ (2 k + 1))` of Theorem E1(k). -/
noncomputable def betaE1 (k κ μ : ℝ) : ℝ := (μ - 2 * κ * k) / (μ * (2 * k + 1))

/-- The power saving `δ = β / k = (μ - 2 κ k) / (k μ (2 k + 1))` of Theorem E1(k). -/
noncomputable def deltaE1 (k κ μ : ℝ) : ℝ := betaE1 k κ μ / k

theorem betaE1_pos {k κ μ : ℝ} (hk : 0 ≤ k) (hμ : 2 * κ * k < μ) (hκ : 0 ≤ κ) :
    0 < betaE1 k κ μ := by
  have hμ0 : 0 < μ := by nlinarith
  unfold betaE1
  apply div_pos (by linarith) (by positivity)

theorem betaE1_le_one {k κ μ : ℝ} (hk : 0 ≤ k) (hμ : 2 * κ * k < μ) (hκ : 0 ≤ κ) :
    betaE1 k κ μ ≤ 1 := by
  have hμ0 : 0 < μ := by nlinarith
  unfold betaE1
  rw [div_le_one (by positivity)]
  nlinarith

theorem deltaE1_pos {k κ μ : ℝ} (hk : 0 < k) (hμ : 2 * κ * k < μ) (hκ : 0 ≤ κ) :
    0 < deltaE1 k κ μ :=
  div_pos (betaE1_pos hk.le hμ hκ) hk

/-- The balance of Theorem E1(k): `2 β + 2 κ / μ = (1 - β) / k = 1 / k - δ`. -/
theorem betaE1_balance {k κ μ : ℝ} (hk : 0 < k) (hμ : 0 < μ) :
    2 * betaE1 k κ μ + 2 * κ / μ = (1 - betaE1 k κ μ) / k ∧
      (1 - betaE1 k κ μ) / k = 1 / k - deltaE1 k κ μ := by
  have h1 : 2 * k + 1 ≠ 0 := by positivity
  unfold deltaE1 betaE1
  constructor
  · field_simp
    ring
  · field_simp

/-- Theorem E1 at `k = ℓ = 7` (`μ_7 = 168`): `δ = (12 - κ) / 1260`. -/
theorem deltaE1_seven (κ : ℝ) : deltaE1 7 κ 168 = (12 - κ) / 1260 := by
  unfold deltaE1 betaE1; ring

/-- The splitting parameter of Theorem E1 for `Π₇₈` (`k = 7`, `κ = 1`): `β = 11 / 180`. -/
theorem betaE1_pi78 : betaE1 7 1 168 = 11 / 180 := by
  unfold betaE1; norm_num

/-- Theorem E1 for `Π₇₈`: `δ = 11 / 1260` and exponent `1 / 7 - δ = 169 / 1260`. -/
theorem exponentE1_pi78 : deltaE1 7 1 168 = 11 / 1260 ∧ 1 / 7 - deltaE1 7 1 168 = 169 / 1260 := by
  rw [deltaE1_seven]; norm_num

/-- Theorem E1(11) at `κ = 1` (`μ_11 = 660`): `δ = 29 / 7590`. -/
theorem deltaE1_eleven : deltaE1 11 1 660 = 29 / 7590 := by
  unfold deltaE1 betaE1; norm_num

/-- Theorem E1(13) at `κ = 1` (`μ_13 = 1092`): `δ = 41 / 14742`. -/
theorem deltaE1_thirteen : deltaE1 13 1 1092 = 41 / 14742 := by
  unfold deltaE1 betaE1; norm_num

/-- For `X ≥ 1` and `a ≤ 1`, `ε ≥ 0`: `X ^ (a (1 + ε)) ≤ X ^ (a + ε)`. This absorbs the
`Q ^ ε` loss of the conductor count into `X ^ ε`. -/
theorem rpow_mul_one_add_le {X a ε : ℝ} (hX : 1 ≤ X) (ha : a ≤ 1) (hε : 0 ≤ ε) :
    X ^ (a * (1 + ε)) ≤ X ^ (a + ε) := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  nlinarith

/-- The balance lemma: if `A ≤ c₁ X ^ (a + ε)` and `B ≤ c₂ X ^ b` with `a, b ≤ e`, `ε ≥ 0`,
`c₁, c₂ ≥ 0` and `X ≥ 1`, then `A + B ≤ (c₁ + c₂) X ^ (e + ε)`. -/
theorem balance_le {X A B c₁ c₂ a b e ε : ℝ} (hX : 1 ≤ X) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (ha : a ≤ e) (hb : b ≤ e) (hε : 0 ≤ ε) (hA : A ≤ c₁ * X ^ (a + ε))
    (hB : B ≤ c₂ * X ^ b) : A + B ≤ (c₁ + c₂) * X ^ (e + ε) := by
  have h1 : X ^ (a + ε) ≤ X ^ (e + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have h2 : X ^ b ≤ X ^ (e + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  calc A + B ≤ c₁ * X ^ (a + ε) + c₂ * X ^ b := add_le_add hA hB
    _ ≤ c₁ * X ^ (e + ε) + c₂ * X ^ (e + ε) := by gcongr
    _ = (c₁ + c₂) * X ^ (e + ε) := by ring

/-- The balance argument of Theorem V6: with `β = betaV6 k C`, a Region I bound
`A ≤ c₁ X ^ ((1 - β) / k + ε)` and a Region II bound `B ≤ c₂ X ^ (β (C + 1))` give
`A + B ≤ (c₁ + c₂) X ^ (1 / k - δ_k + ε)`. -/
theorem balance_v6 {k C X A B c₁ c₂ ε : ℝ} (hk : 0 < k) (hC : 0 ≤ C) (hX : 1 ≤ X)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hε : 0 ≤ ε)
    (hA : A ≤ c₁ * X ^ ((1 - betaV6 k C) / k + ε))
    (hB : B ≤ c₂ * X ^ (betaV6 k C * (C + 1))) :
    A + B ≤ (c₁ + c₂) * X ^ (1 / k - deltaV6 k C + ε) := by
  obtain ⟨h1, h2⟩ := betaV6_balance hk hC
  exact balance_le hX hc₁ hc₂ (by rw [h1, h2]) h2.le hε hA hB

end Iut.Abc.Counting
