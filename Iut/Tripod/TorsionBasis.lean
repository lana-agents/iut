/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Torsion.Count
import Iut.Tripod.TorsionDegree

/-!
# The torsion of the Legendre curves

The `n`-torsion of every Legendre curve `E_λ(ℚ̄)` is finite (`Iut.Tripod.legendre_torsionFinite`),
and for a point `λ ∉ {0, 1}` of the tripod and a prime `ℓ`, `E_λ(ℚ̄)[ℓ] ≅ (ℤ/ℓ)²`
(`Iut.Tripod.legendre_torsionBasis`), from the general theorems of `Iut.Torsion.Count` for the
curve `y² = x³ − (1 + λ)x² + λx` (`a₁ = a₃ = 0`) over the algebraically closed field `ℚ̄` of
characteristic `0`. Consequently the torsion degree bounds for `n = 3, 5` are theorems
(`Iut.Tripod.torsionDegreeBound_three'`, `Iut.Tripod.torsionDegreeBound_five'`).
-/

namespace Iut.Tripod

open WeierstrassCurve

open scoped Classical

/-- **The `n`-torsion of `E_λ(ℚ̄)` is finite** for every `λ ∈ ℚ̄` and `n ≠ 0`. -/
theorem legendre_torsionFinite (l : Qbar) (n : ℕ) (hn : n ≠ 0) : TorsionFinite l n :=
  Iut.Torsion.torsion_finite (W := legendre l) rfl rfl n hn

/-- **`E_λ(ℚ̄)[ℓ] ≅ (ℤ/ℓ)²`** for a point `λ ∉ {0, 1}` of the tripod and a prime `ℓ`. -/
theorem legendre_torsionBasis (x : Pt) (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (AddSubgroup.torsionBy (legendre x.1).toAffine.Point ℓ ≃+ (Fin 2 → ZMod ℓ)) :=
  haveI : (legendre x.1).IsElliptic := legendre_isElliptic x.2.1 x.2.2
  Iut.Torsion.torsionBasis (W := legendre x.1) rfl rfl ℓ

/-- The torsion degree bound for `n = 3` at the points of the tripod. -/
theorem torsionDegreeBound_three' (x : Pt) : TorsionDegreeBound x.1 3 :=
  torsionDegreeBound_three x.1 (legendre_torsionBasis x 3)

/-- The torsion degree bound for `n = 5` at the points of the tripod. -/
theorem torsionDegreeBound_five' (x : Pt) : TorsionDegreeBound x.1 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  torsionDegreeBound_five x.1 (legendre_torsionBasis x 5)

end Iut.Tripod
