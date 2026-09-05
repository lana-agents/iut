/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.TateTorsion

/-!
# Roots of the Tate parameter

For a Tate structure `S` on `E` over `k` (`Iut.TateStructure`) and an odd prime (or any odd
positive integer) `ℓ`:

* if `E(k)[ℓ]` has `ℓ²` elements, `q` has an `ℓ`-th root in `k^×`
  (`Iut.TateStructure.exists_pow_eq_q_of_card`), from the root class of
  `Iut.TateStructure.exists_root_class`: `u^ℓ = q^{1 + ℓm}` gives `(u·q^{−m})^ℓ = q`;
* if moreover `E(k)[2]` has `4` elements, `q` has a square root, and combining the two with
  `2b + ℓa = 1` gives a `2ℓ`-th root `q^{1/2ℓ} = s^a r^b`
  (`Iut.TateStructure.exists_pow_eq_q`).
-/

namespace Iut.TateStructure

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

noncomputable section

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
variable {E : WeierstrassCurve k} (S : TateStructure E)

/-- If `E(k)[ℓ]` has `ℓ²` elements, the Tate parameter has an `ℓ`-th root. -/
theorem exists_pow_eq_q_of_card (ℓ : ℕ) [NeZero ℓ] (h : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) :
    ∃ r : kˣ, r ^ ℓ = S.t.q := by
  obtain ⟨u, m, hu⟩ := S.exists_root_class ℓ h
  refine ⟨u * S.t.q ^ (-m), ?_⟩
  rw [mul_pow, hu, ← zpow_natCast, ← zpow_mul, ← zpow_add]
  convert zpow_one S.t.q using 2
  ring

/-- Bézout for `2` and an odd `ℓ`: `2b + ℓa = 1`. -/
lemma exists_two_mul_add_mul_eq_one {ℓ : ℕ} (hodd : Odd ℓ) :
    ∃ a b : ℤ, 2 * b + (ℓ : ℤ) * a = 1 := by
  have hcop : Nat.Coprime 2 ℓ := Nat.coprime_two_left.mpr hodd
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  refine ⟨y, x, ?_⟩
  push_cast at hxy
  linear_combination hxy

/-- A `2ℓ`-th root from a square root and an `ℓ`-th root, `ℓ` odd. -/
lemma exists_pow_two_mul_eq {G : Type*} [CommGroup G] {q r s : G} {ℓ : ℕ} (hodd : Odd ℓ)
    (hr : r ^ ℓ = q) (hs : s ^ 2 = q) : ∃ x : G, x ^ (2 * ℓ) = q := by
  obtain ⟨a, b, hab⟩ := exists_two_mul_add_mul_eq_one hodd
  refine ⟨s ^ a * r ^ b, ?_⟩
  have h1 : (s ^ a) ^ (2 * ℓ) = q ^ ((ℓ : ℤ) * a) := by
    rw [← zpow_natCast, ← zpow_mul, ← hs, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have h2 : (r ^ b) ^ (2 * ℓ) = q ^ (2 * b) := by
    rw [← zpow_natCast, ← zpow_mul, ← hr, ← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow, h1, h2, ← zpow_add, add_comm, hab, zpow_one]

/-- **The `2ℓ`-th root of the Tate parameter**: if `E(k)[ℓ]` has `ℓ²` elements and `E(k)[2]`
has `4` elements, `ℓ` odd, then `q` has a `2ℓ`-th root in `k`. -/
theorem exists_pow_eq_q (ℓ : ℕ) [NeZero ℓ] (hodd : Odd ℓ)
    (hℓ : ℓ * ℓ ≤ Nat.card ↥(torsion ℓ E)) (h2 : 2 * 2 ≤ Nat.card ↥(torsion 2 E)) :
    ∃ x : k, x ^ (2 * ℓ) = (S.t.q : k) := by
  obtain ⟨r, hr⟩ := S.exists_pow_eq_q_of_card ℓ hℓ
  obtain ⟨s, hs⟩ := S.exists_pow_eq_q_of_card 2 h2
  obtain ⟨x, hx⟩ := exists_pow_two_mul_eq hodd hr hs
  exact ⟨x, by rw [← Units.val_pow_eq_pow_val, hx]⟩

end

end Iut.TateStructure
