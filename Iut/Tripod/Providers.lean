/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveFacts
import Iut.Concrete.ModEllRepConstruct
import Iut.Concrete.CurveArithmeticProved

/-!
# The curve-level data of the Legendre curves from propositions

All the data attached to the curve `E_λ/F_λ` of a point of the tripod (its Tate parameters,
its mod-`ℓ` representations, the finiteness of its torsion) is constructed from three
propositions (`Iut.Tripod.CurveProps`): the ℓ-torsion of `E_λ(ℚ̄)` is a rank-two
`ℤ/ℓ`-module, `E_λ/F_λ` has stable reduction everywhere, and `F_λ/F_mod` is Galois of
degree prime to `ℓ` for `ℓ ≥ 7`.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData WeierstrassCurve
open scoped Classical

/-- **The propositions about the Legendre curves** from which all curve-level data is
constructed. -/
structure CurveProps : Prop where
  /-- `E_λ[n](ℚ̄) ≅ (ℤ/n)²` for every `n ≠ 0`. -/
  torsion_basis : ∀ (l : Qbar) (n : ℕ), n ≠ 0 →
    Nonempty (AddSubgroup.torsionBy (legendre l).toAffine.Point n ≃+ (Fin 2 → ZMod n))
  /-- `E_λ/F_λ` has stable reduction at every finite place (Raynaud's criterion:
  the `3`- and `5`-torsion is rational). -/
  stable_reduction : ∀ (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (w : NumberField.FinitePlace (curveOf x h3 h5).F), HasStableReductionAt (curveOf x h3 h5).E w
  /-- `F_λ/F_mod` is Galois of degree prime to `ℓ` for every prime `ℓ ≥ 7`. -/
  galois_deg_prime : ∀ (x : Pt) (h3 : TorsionFinite x.1 3) (h5 : TorsionFinite x.1 5)
    (ℓ : ℕ), ℓ.Prime → 7 ≤ ℓ → IsGaloisOfDegreePrimeTo (curveOf x h3 h5).F (curveOf x h3 h5).E ℓ

/-- The data providers of the Legendre curves, from `CurveProps`. -/
noncomputable def providersOfProps (hp : CurveProps) : CurveProviders where
  torsionFinite3 l := torsionFinite_of_equiv (hp.torsion_basis l 3 (by norm_num))
  torsionFinite5 l := torsionFinite_of_equiv (hp.torsion_basis l 5 (by norm_num))
  arith x := CurveArithmetic.ofCore _ (sqrt_neg_one x _ _) (hp.stable_reduction x _ _)
    (six_torsion_rational x _ _) (hp.galois_deg_prime x _ _)
  modRep x ℓ hℓ :=
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    modEllRepData _ ℓ (hp.torsion_basis x.1 ℓ hℓ.ne_zero)

end Iut.Tripod
