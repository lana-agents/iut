/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Galois
import Iut.Tripod.StableTwo
import Iut.Tripod.TorsionBasis
import Iut.Concrete.ModEllRepConstruct
import Iut.Concrete.CurveArithmeticProved

/-!
# The curve-level data of the Legendre curves from propositions

All the data attached to the curve `E_λ/F_λ` of a point of the tripod (its Tate parameters,
its mod-`ℓ` representations, the finiteness of its torsion) is constructed from two
theorems: the finiteness of the torsion of `E_λ(ℚ̄)` and the bases `E_λ(ℚ̄)[ℓ] ≅ (ℤ/ℓ)²`
(`Iut.Tripod.legendre_torsionFinite`, `Iut.Tripod.legendre_torsionBasis`, from the division
polynomials, `Iut.Torsion`), the stable reduction of `E_λ/F_λ` at every finite place
(`Iut.Tripod.stable_reduction`: from the Legendre model at the places of odd residue
characteristic, and from the rational `3`-torsion at the places over `2`), and that
`F_λ/F_mod` is Galois of degree prime to `ℓ` for `ℓ ≥ 7` (`Iut.Tripod.galois_deg_prime`).
No proposition remains: `Iut.Tripod.tripodProviders` is a closed term.
-/

namespace Iut.Tripod

open Iut Iut.EllipticCurveData WeierstrassCurve
open scoped Classical

/-- **The data providers of the Legendre curves**, a closed term: every curve-level fact is a
theorem (torsion bases, stable reduction, the Galois-degree property of `F_λ/F_mod`). -/
noncomputable def tripodProviders : CurveProviders where
  torsionFinite3 l := legendre_torsionFinite l 3 (by norm_num)
  torsionFinite5 l := legendre_torsionFinite l 5 (by norm_num)
  arith x := CurveArithmetic.ofCore _ (sqrt_neg_one x _ _)
    (stable_reduction x _ _ (legendre_torsionBasis x 3))
    (six_torsion_rational x _ _) (galois_deg_prime x _ _)
  modRep x ℓ hℓ :=
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    modEllRepData _ ℓ (legendre_torsionBasis x ℓ)

end Iut.Tripod
