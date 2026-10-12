/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaValues
import Iut.Concrete.ThetaRegion

/-!
# The LGP theta values of the wall are the theta values of `Θ̈`

The η-algorithm of `Iut/Wall` (`Iut.Wall.lgpElt`, through `InitialThetaData.scaleEltAt`) and
the arithmetic line bundles `Iut.Arakelov.thetaBundle` use, at a bad place `v` of `K` with Tate
parameter `q` and the chosen root `q_v = D.qroot v` (`q_v^{2ℓ} = q`), the **theta values**
`q_v^{j²}` at the labels `j` ([LANA], §5.2(f); IUT I, Example 3.2(iv); IUT II, Remark 2.5.1).

Here we show that these are the theta values of (3) (`ThetaValues.lean`): with `s = q_v^ℓ`
(so `s² = q`), IUT's normalized theta function `Θ_v = Θ̈(√-1)/Θ̈(−)` takes the value
`(s^j θ(q^j)/θ(1))⁻¹ = s^{j²}` at the evaluation point `√-1·s^j` labelled `j`, and

* `qroot_pow_ell_mul_thetaRatio`: `(q_v^{j²})^ℓ · Θ̈(√-1·s^j)/Θ̈(√-1) = 1`, i.e. `q_v^{j²}` is an
  `ℓ`-th root of the theta value `Θ_v(√-1·s^j)`;
* `pow_eq_thetaRatio_inv_iff`: the `ℓ`-th roots of `Θ_v(√-1·s^j)` are exactly the
  `μ_ℓ`-multiples of `q_v^{j²}` — the `ℓ`-th root of the étale theta function is determined up to
  `μ_ℓ` (the `μ_{2ℓ}`-indeterminacy of IUT I, Example 3.2(ii), restricted to the `ℓ`-th root);
* `scaleEltAt_eq`: the element placed by the wall's LGP map in the tensor factor of the label `l`
  of the capsule `i` is the inclusion of `lgpValue D v (i + 1) = q_v^{(i+1)²}`.

The `√-1`-free form `thetaRatio` is used, so no assumption `√-1 ∈ K_v` is needed (with
`√-1 ∈ K_v`, `etaleTheta_ratio` identifies it with `Θ̈(√-1·s^j)/Θ̈(√-1)`).
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateCurvesTheta.TateParameter NumberField

universe u

variable (D : InitialThetaData.{u})

/-- The LGP theta value `q_v^{j²}` at the label `j` (`= D.qroot v ^ j²`). -/
abbrev lgpValue (v : FinitePlace D.Kt) (j : ℕ) : completionAt D.Kt v :=
  D.qroot v ^ j ^ 2

/-- The square root `s = q_v^ℓ` of the Tate parameter at a bad place. -/
def sqrtQ (v : FinitePlace D.Kt) : (completionAt D.Kt v)ˣ :=
  Units.mk0 (D.qroot v) (D.qroot_ne_zero v) ^ D.ℓ

lemma sqrtQ_sq {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    sqrtQ D v ^ 2 = (D.tate.S v hv).t.q := by
  apply Units.ext
  rw [sqrtQ, ← pow_mul, Units.val_pow_eq_pow_val, Units.val_mk0, mul_comm]
  exact qrootOf_spec D hv

/-- `θ(1) ≠ 0` at a bad place (`K_v` has characteristic `0`). -/
lemma theta_one_ne_zero_at {v : FinitePlace D.Kt} (hv : IsBadK D v) :
    (D.tate.S v hv).t.theta 1 ≠ 0 :=
  theta_one_ne_zero _ two_ne_zero

/-- **The LGP theta values are `ℓ`-th roots of the theta values of `Θ̈`**:
`(q_v^{j²})^ℓ · s^j θ(q^j)/θ(1) = 1` for `s = q_v^ℓ`, i.e. `(q_v^{j²})^ℓ = Θ_v(√-1·s^j)`. -/
theorem qroot_pow_ell_mul_thetaRatio {v : FinitePlace D.Kt} (hv : IsBadK D v) (j : ℕ) :
    lgpValue D v j ^ D.ℓ * thetaRatio (D.tate.S v hv).t (sqrtQ D v) j = 1 := by
  rw [thetaRatio_eq _ (sqrtQ_sq D hv) (theta_one_ne_zero_at D hv), sqrtQ,
    Units.val_pow_eq_pow_val, Units.val_mk0,
    ← zpow_natCast (D.qroot v) D.ℓ, ← zpow_mul, lgpValue, ← pow_mul, ← zpow_natCast,
    ← zpow_add₀ (D.qroot_ne_zero v)]
  convert zpow_zero (D.qroot v) using 2
  push_cast
  ring

/-- **The `ℓ`-th roots of the normalized theta value at the label `j` are the `μ_ℓ`-multiples of
the LGP theta value `q_v^{j²}`.** -/
theorem pow_eq_thetaRatio_inv_iff {v : FinitePlace D.Kt} (hv : IsBadK D v) (j : ℕ)
    (x : completionAt D.Kt v) :
    x ^ D.ℓ = (thetaRatio (D.tate.S v hv).t (sqrtQ D v) j)⁻¹ ↔
      ∃ ζ : completionAt D.Kt v, ζ ^ D.ℓ = 1 ∧ x = ζ * lgpValue D v j := by
  have h := qroot_pow_ell_mul_thetaRatio D hv j
  have hval : (thetaRatio (D.tate.S v hv).t (sqrtQ D v) j)⁻¹ = lgpValue D v j ^ D.ℓ :=
    (eq_inv_of_mul_eq_one_left h).symm
  have h0 : lgpValue D v j ≠ 0 := pow_ne_zero _ (D.qroot_ne_zero v)
  rw [hval]
  constructor
  · intro hx
    refine ⟨x / lgpValue D v j, ?_, by field_simp⟩
    rw [div_pow, hx, div_self (pow_ne_zero _ h0)]
  · rintro ⟨ζ, hζ, rfl⟩
    rw [mul_pow, hζ, one_mul]

/-- The element placed by the LGP map of the wall (`InitialThetaData.scaleEltAt`, used by
`Iut.Wall.lgpElt`) in the tensor factor of the label `l` of the capsule `i` is the inclusion of
the LGP theta value `lgpValue D v (i + 1)` at the place `v` of that factor. -/
theorem scaleEltAt_eq (n : ℕ) (i : Fin n) (p : Nat.Primes)
    (c : InitialThetaData.Lab n i → LocalTheory.Fiber D.Fmod (.finite p))
    (l : InitialThetaData.Lab n i) :
    D.scaleEltAt n i p c l =
      LocalTheory.incl D.Kt p (LocalTheory.tuple D.placeSect _ c) l
        (LocalTheory.sectPlace D.placeSect (c l)) (LocalTheory.tuple_finite D.placeSect c l)
        (lgpValue D (LocalTheory.sectPlace D.placeSect (c l)) (i.1 + 1)) :=
  rfl

end Iut.EtaleTheta
