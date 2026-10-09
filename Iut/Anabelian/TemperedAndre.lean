/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Tempered
import Pi1.Orbifold.Smooth

/-!
# The tempered group of a model orbicurve is André's tempered group

`Orbicurve.temperedPi1 X` (`Iut.Anabelian.Tempered`) is the integral-model construction of
lana-agents/tempered-fundamental-groups for the presentation `X.temperedPresentation` over the
canonical valuation `O = canonicalValuationSubring k`. This module identifies it with
**André's tempered fundamental group** `Orbicurve.andrePi1 X` of the same presentation (the
automorphism group of the fibre functor on the tempered coverings defined through semistable
models, `TemperedFundamentalGroups.andreGroup`), by Theorem A of that repository
(`TemperedFundamentalGroups.andreEquiv'`, unconditional).

The hypotheses of Theorem A are supplied as follows (`Orbicurve.temperedEquivAndre`):

* in characteristic `0` the presentation is the Galois presentation `Genuine.orbifold`: `R` is
  the integral closure of `k[x]` in `L_X`, a domain, smooth over `k` and of Krull dimension `1`
  (`Pi1.Orbifold.GaloisData.smooth_R`, `Pi1.Orbifold.GaloisData.ringKrullDim_R`), `A` is finite
  (`Pi1.Orbifold.GaloisData.finite_A`) and `Ω` is an algebraic closure;
* the canonical valuation of `k` is assumed to be a complete discrete valuation ring with
  perfect residue field of mixed characteristic. For the completions `K_v` of number fields at
  finite places this is proved in `Iut.Anabelian.AdicCompletion`, and the identification at the
  places of initial Θ-data is `Iut.LocalThetaData.pivBadEquivAndre`.
-/

namespace Iut.Anabelian

universe u

open TemperedFundamentalGroups IsLocalRing

attribute [local instance low] Classical.propDecidable

noncomputable section

variable {k : Type u} [Field k]

/-- **André's tempered fundamental group** of a model orbicurve: `andreGroup` of the presentation
`Orbicurve.temperedPresentation` over the canonical valuation of `k` (the same presentation and
valuation as `Orbicurve.temperedPi1`). -/
abbrev Orbicurve.andrePi1 (X : Orbicurve k) : Type u :=
  andreGroup (canonicalValuationSubring k) X.temperedPresentation.1.R X.temperedPresentation.1.A
    (X.temperedPresentation.1.V (canonicalValuationSubring k))
    (X.temperedPresentation.1.V_comap (canonicalValuationSubring k))

variable [CharZero k] [IsDiscreteValuationRing (canonicalValuationSubring k)]
  [IsAdicComplete (maximalIdeal (canonicalValuationSubring k)) (canonicalValuationSubring k)]
  [PerfectField (ResidueField (canonicalValuationSubring k))]

/-- Theorem A for an affine orbifold equal to the Galois presentation `Genuine.orbifold` of a
model orbicurve. -/
def genuineAndreEquiv
    (hp : ∃ p : ℕ, p.Prime ∧ (p : canonicalValuationSubring k) ∈ maximalIdeal _)
    (E : WeierstrassCurve k) [E.IsElliptic] (ℓ : ℕ) (M : AddSubgroup E.toAffine.Point)
    (pm : Bool) (Y : AffineOrbifold k) (hY : Y = Genuine.orbifold E ℓ M pm) :
    Y.canonicalTemperedPi1 ≃ₜ* andreGroup (canonicalValuationSubring k) Y.R Y.A
      (Y.V (canonicalValuationSubring k)) (Y.V_comap (canonicalValuationSubring k)) := by
  subst hY
  haveI : Algebra.Smooth k (Genuine.orbifold E ℓ M pm).R :=
    Pi1.Orbifold.GaloisData.smooth_R (Genuine.galoisData E ℓ M pm)
  haveI : IsDomain (Genuine.orbifold E ℓ M pm).R :=
    inferInstanceAs (IsDomain (Genuine.galoisData E ℓ M pm).R)
  haveI : Finite (Genuine.orbifold E ℓ M pm).A :=
    inferInstanceAs (Finite (Genuine.galoisData E ℓ M pm).A)
  haveI : IsAlgClosed (Genuine.orbifold E ℓ M pm).Ω :=
    inferInstanceAs (IsAlgClosed (Genuine.Ω E))
  exact andreEquiv' _ _ hp (Pi1.Orbifold.GaloisData.ringKrullDim_R (Genuine.galoisData E ℓ M pm))

/-- **The tempered fundamental group of a model orbicurve is André's tempered fundamental
group** (Theorem A, `TemperedFundamentalGroups.andreEquiv'`), over a field of characteristic `0`
whose canonical valuation is a complete discrete valuation ring with perfect residue field of
mixed characteristic. -/
def Orbicurve.temperedEquivAndre
    (hp : ∃ p : ℕ, p.Prime ∧ (p : canonicalValuationSubring k) ∈ maximalIdeal _)
    (X : Orbicurve k) : X.temperedPi1 ≃ₜ* X.andrePi1 :=
  genuineAndreEquiv hp X.E X.level X.M X.pm _
    (congrArg Sigma.fst X.temperedPresentation_of_charZero)

end

end Iut.Anabelian
