/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Theta.Inversion

/-!
# The theta function `Θ̈` on the theta covering `Ÿ → Y → X` ([EtTh], §1)

Let `t : TateParameter K` be a Tate parameter `q` over a complete non-archimedean field `K`, so
that the Tate curve is `X = Kˣ/qᶻ` (`tate-curves-theta`). [EtTh], §1 considers the tempered
coverings

* `Y → X`: the `ℤ`-covering (the universal covering of the dual graph of the special fibre),
  with multiplicative coordinate `U` on the component labelled `0`;
* `Ÿ → Y`: the double covering given by a square root `Ü` of `U`,

and on `Ÿ` the theta function ([EtTh], Prop. 1.4)
```
Θ̈(Ü) = q^{-1/8} ∑ₙ (-1)ⁿ q^{(n+1/2)²/2} Ü^{2n+1} = ∑ₙ (-1)ⁿ q^{n(n+1)/2} Ü^{2n+1},
```
since `(n+1/2)²/2 - 1/8 = n(n+1)/2`. In terms of the theta series `θ(u) = ∑ q^{n(n+1)/2} uⁿ` of
`tate-curves-theta`, `Θ̈(Ü) = Ü·θ(-Ü²)`: this is `TateParameter.thetaOdd`.

The coverings are recorded by the action of their deck groups on the coordinate `Ü` (scope
decision S1 of `README.md`): `Gal(Ÿ/Y) = {±1}` acts by `Ü ↦ -Ü`, and, given a square root `s`
of `q` (`s² = q`), the `ℤ`-action on `Ÿ` lifting `Gal(Y/X) ≅ ℤ` is `Ü ↦ s^a·Ü`.

## Main results

* `hasSum_etaleTheta`: the series of [EtTh], Prop. 1.4.
* `etaleTheta_inv`, `etaleTheta_neg`, `etaleTheta_zpow_sqrt_mul`: the three functional equations
  of [EtTh], Prop. 1.4(ii), `Θ̈(Ü⁻¹) = -Θ̈(Ü)`, `Θ̈(-Ü) = -Θ̈(Ü)`,
  `Θ̈(q^{a/2}Ü) = (-1)^a q^{-a²/2} Ü^{-2a} Θ̈(Ü)` (with `q^{a/2} = s^a`, `q^{-a²/2} = s^{-a²}`).
* `etaleTheta_eq_zero_iff`: the zeros of `Θ̈` are the cusps `Ü² ∈ qᶻ` of `Ÿ` ([EtTh],
  Prop. 1.4(i)).
* `thetaFactor_add`: the automorphy factor `j(a, Ü) = (-1)^a s^{-a²} Ü^{-2a}` is a `1`-cocycle
  of `ℤ` acting through `Ü ↦ s^a Ü`.

## References

* S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*, §1.
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateCurvesTheta.TateParameter

variable {K : Type*} [NormedField K] (t : TateParameter K)

/-- The étale theta function `Θ̈(Ü) = Ü·θ(-Ü²)` of [EtTh], Prop. 1.4, on the `Ü`-coordinate of
the covering `Ÿ` (`= TateParameter.thetaOdd`). -/
abbrev etaleTheta (U : Kˣ) : K := t.thetaOdd U

lemma etaleTheta_def (U : Kˣ) : etaleTheta t U = (U : K) * t.theta (-(U ^ 2)) := rfl

/-- **The series of [EtTh], Prop. 1.4**: `Θ̈(Ü) = ∑ₙ (-1)ⁿ q^{n(n+1)/2} Ü^{2n+1}`. -/
theorem hasSum_etaleTheta [CompleteSpace K] [IsUltrametricDist K] (U : Kˣ) :
    HasSum (fun n : ℤ => (-1 : K) ^ n * (t.q : K) ^ thetaExp n * (U : K) ^ (2 * n + 1))
      (etaleTheta t U) := by
  have hU : (U : K) ≠ 0 := U.ne_zero
  have e : (fun n : ℤ => (-1 : K) ^ n * (t.q : K) ^ thetaExp n * (U : K) ^ (2 * n + 1)) =
      fun n => (U : K) * t.thetaTerm (-(U ^ 2)) n := by
    funext n
    simp only [thetaTerm, Units.val_neg, Units.val_pow_eq_pow_val]
    rw [neg_eq_neg_one_mul ((U : K) ^ 2), mul_zpow, zpow_add₀ hU, zpow_one, zpow_mul,
      zpow_ofNat]
    ring
  rw [e, etaleTheta_def, theta]
  exact ((t.thetaTerm_summable (-(U ^ 2))).hasSum).mul_left (U : K)

/-- **Inversion** ([EtTh], Prop. 1.4(ii)): `Θ̈(Ü⁻¹) = -Θ̈(Ü)`. -/
theorem etaleTheta_inv (U : Kˣ) : etaleTheta t U⁻¹ = -etaleTheta t U := t.thetaOdd_inv U

/-- **Oddness** under the deck involution of `Ÿ/Y` ([EtTh], Prop. 1.4(ii)):
`Θ̈(-Ü) = -Θ̈(Ü)`. -/
theorem etaleTheta_neg (U : Kˣ) : etaleTheta t (-U) = -etaleTheta t U := by
  simp only [etaleTheta_def, neg_sq, Units.val_neg, neg_mul]

/-- The automorphy factor `j(a, Ü) = (-1)^a s^{-a²} Ü^{-2a}` of the `ℤ`-action `Ü ↦ s^a Ü`. -/
def thetaFactor (s : Kˣ) (a : ℤ) (U : Kˣ) : K :=
  (-1 : K) ^ a * (s : K) ^ (-a ^ 2) * (U : K) ^ (-2 * a)

lemma thetaFactor_ne_zero (s : Kˣ) (a : ℤ) (U : Kˣ) : thetaFactor s a U ≠ 0 := by
  unfold thetaFactor
  have hs : (s : K) ≠ 0 := s.ne_zero
  have hU : (U : K) ≠ 0 := U.ne_zero
  exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
    (zpow_ne_zero _ hs)) (zpow_ne_zero _ hU)

/-- **The `ℤ`-action on `Ÿ`** ([EtTh], Prop. 1.4(ii)): for a square root `s` of `q`,
`Θ̈(s^a·Ü) = (-1)^a·s^{-a²}·Ü^{-2a}·Θ̈(Ü)`, i.e.
`Θ̈(q^{a/2}Ü) = (-1)^a q^{-a²/2} Ü^{-2a} Θ̈(Ü)`. -/
theorem etaleTheta_zpow_sqrt_mul {s : Kˣ} (hs : s ^ 2 = t.q) (a : ℤ) (U : Kˣ) :
    etaleTheta t (s ^ a * U) = thetaFactor s a U * etaleTheta t U := by
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hU : (U : K) ≠ 0 := U.ne_zero
  have hsq : (t.q : K) = (s : K) ^ 2 := by rw [← hs, Units.val_pow_eq_pow_val]
  have hUnit : -((s ^ a * U) ^ 2) = t.q ^ a * (-(U ^ 2)) := by
    rw [← hs, mul_pow, mul_neg, ← zpow_natCast (s ^ a), ← zpow_mul, ← zpow_natCast s,
      ← zpow_mul, mul_comm a]
  have hneg : ((-1 : K) ^ a)⁻¹ = (-1) ^ a := by
    rw [neg_one_zpow_eq_ite]; split_ifs <;> simp
  have key : ((((s : K) ^ 2) ^ thetaExp a * ((-1) ^ a * ((U : K) ^ 2) ^ a))⁻¹) =
      (-1) ^ a * (s : K) ^ (-(a * (a + 1))) * (U : K) ^ (-2 * a) := by
    rw [← zpow_natCast (s : K) 2, ← zpow_mul, ← zpow_natCast (U : K) 2, ← zpow_mul]
    push_cast
    rw [two_mul_thetaExp, mul_inv, mul_inv, hneg, ← zpow_neg, ← zpow_neg,
      show (-(2 * a) : ℤ) = -2 * a by ring]
    ring
  have hss : (s : K) ^ a * (s : K) ^ (-(a * (a + 1))) = (s : K) ^ (-a ^ 2) := by
    rw [← zpow_add₀ hs0]; congr 1; ring
  rw [etaleTheta_def, etaleTheta_def, hUnit, t.theta_zpow_q_smul, thetaFactor]
  simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul,
    Units.val_zpow_eq_zpow_val]
  rw [hsq, neg_eq_neg_one_mul ((U : K) ^ 2), mul_zpow, key, ← hss]
  ring

/-- **The automorphy factor is a `1`-cocycle** of `ℤ` acting by `Ü ↦ s^a Ü`:
`j(a + b, Ü) = j(a, s^b Ü)·j(b, Ü)`. -/
theorem thetaFactor_add (s : Kˣ) (a b : ℤ) (U : Kˣ) :
    thetaFactor s (a + b) U = thetaFactor s a (s ^ b * U) * thetaFactor s b U := by
  have hs : (s : K) ≠ 0 := s.ne_zero
  have hU : (U : K) ≠ 0 := U.ne_zero
  simp only [thetaFactor, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [zpow_add₀ (neg_ne_zero.2 one_ne_zero), mul_zpow, ← zpow_mul,
    show (-(a + b) ^ 2 : ℤ) = -a ^ 2 + b * (-2 * a) + -b ^ 2 by ring,
    show (-2 * (a + b) : ℤ) = -2 * a + -2 * b by ring, zpow_add₀ hs, zpow_add₀ hs,
    zpow_add₀ hU]
  ring

/-- **The zeros of `Θ̈`** ([EtTh], Prop. 1.4(i)): `Θ̈(Ü) = 0` exactly at the cusps `Ü² ∈ qᶻ` of
`Ÿ`. -/
theorem etaleTheta_eq_zero_iff [CompleteSpace K] [IsUltrametricDist K] (U : Kˣ) :
    etaleTheta t U = 0 ↔ ∃ k : ℤ, (U : K) ^ 2 = (t.q : K) ^ k :=
  t.thetaOdd_eq_zero_iff U

end Iut.EtaleTheta
