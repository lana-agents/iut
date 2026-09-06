/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TorsionBasis
import Iut.Concrete.ModEllRepConstruct
import Iut.Concrete.CurveArithmeticProved

/-!
# The curve-level data of the Legendre curves from propositions

All the data attached to the curve `E_λ/F_λ` of a point of the tripod (its Tate parameters,
its mod-`ℓ` representations, the finiteness of its torsion) is constructed from two
propositions (`Iut.Tripod.CurveProps`): `E_λ/F_λ` has stable reduction everywhere, and
`F_λ/F_mod` is Galois of degree prime to `ℓ` for `ℓ ≥ 7`. The finiteness of the torsion of
`E_λ(ℚ̄)` and the bases `E_λ(ℚ̄)[ℓ] ≅ (ℤ/ℓ)²` are theorems (`Iut.Tripod.legendre_torsionFinite`,
`Iut.Tripod.legendre_torsionBasis`, from the division polynomials, `Iut.Torsion`).
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData WeierstrassCurve
open scoped Classical

/-- **The propositions about the Legendre curves** from which all curve-level data is
constructed. -/
structure CurveProps : Prop where
  /-- `E_λ/F_λ` has stable reduction at every finite place (Raynaud's criterion:
  the `3`- and `5`-torsion is rational). -/
  stable_reduction : ∀ (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (w : NumberField.FinitePlace (curveOf x h3 h5).F), HasStableReductionAt (curveOf x h3 h5).E w
  /-- `F_λ/F_mod` is Galois of degree prime to `ℓ` for every prime `ℓ ≥ 7`. -/
  galois_deg_prime : ∀ (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo (curveOf x h3 h5).F (curveOf x h3 h5).E ℓ

/-- The data providers of the Legendre curves, from `CurveProps`. -/
noncomputable def providersOfProps (hp : CurveProps) : CurveProviders where
  torsionFinite3 l := legendre_torsionFinite l 3 (by norm_num)
  torsionFinite5 l := legendre_torsionFinite l 5 (by norm_num)
  arith x := CurveArithmetic.ofCore _ (sqrt_neg_one x _ _) (hp.stable_reduction x _ _)
    (six_torsion_rational x _ _) (hp.galois_deg_prime x _ _)
  modRep x ℓ hℓ :=
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    modEllRepData _ ℓ (legendre_torsionBasis x ℓ)

end Iut.Tripod
