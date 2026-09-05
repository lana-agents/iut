/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Galois
import Iut.Tripod.StableTwo
import Iut.Concrete.ModEllRepConstruct
import Iut.Concrete.CurveArithmeticProved

/-!
# The curve-level data of the Legendre curves from propositions

All the data attached to the curve `E_λ/F_λ` of a point of the tripod (its Tate parameters,
its mod-`ℓ` representations, the finiteness of its torsion) is constructed from two
proposition (`Iut.Tripod.CurveProps`): the `n`-torsion of `E_λ(ℚ̄)` is a rank-two
`ℤ/n`-module. The stable reduction of `E_λ/F_λ` at every finite place is **proved**
(`Iut.Tripod.stable_reduction`): from the Legendre model at the places of odd residue
characteristic, and from the rational `3`-torsion (which follows from `E_λ[3](ℚ̄) ≅ (ℤ/3)²`)
at the places over `2`. That `F_λ/F_mod` is Galois of degree prime to `ℓ` for `ℓ ≥ 7` is a
theorem (`Iut.Tripod.galois_deg_prime_of_torsion_basis`, from the torsion bases).
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

/-- The data providers of the Legendre curves, from `CurveProps`: the Galois-degree property
of `F_λ/F_mod` is the theorem `Iut.Tripod.galois_deg_prime_of_torsion_basis`. -/
noncomputable def providersOfProps (hp : CurveProps) : CurveProviders where
  torsionFinite3 l := torsionFinite_of_equiv (hp.torsion_basis l 3 (by norm_num))
  torsionFinite5 l := torsionFinite_of_equiv (hp.torsion_basis l 5 (by norm_num))
  arith x := CurveArithmetic.ofCore _ (sqrt_neg_one x _ _)
    (stable_reduction x _ _ (hp.torsion_basis x.1 3 (by norm_num)))
    (six_torsion_rational x _ _) (galois_deg_prime_of_torsion_basis hp.torsion_basis x _ _)
  modRep x ℓ hℓ :=
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    modEllRepData _ ℓ (hp.torsion_basis x.1 ℓ hℓ.ne_zero)

end Iut.Tripod
