/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Geometry
import TemperedFundamentalGroups

/-!
# Tempered fundamental groups of the model orbicurves (taxis #7)

This module builds a term of the residual interface `Iut.Anabelian.TemperedPi1Theory Pi1` from the
construction of lana-agents/tempered-fundamental-groups.

* A model orbicurve `X = (E, ℓ, M, ±)` over `k` is presented as the affine orbifold
  `[Spec R / A]` with `Spec R = E ∖ S`, `S = E(k)[ℓ] + M` (rational points), and `A` the group of
  affine maps `P ↦ εP + m`, `m ∈ M`, `ε = 1` (or `ε = ±1` when the `±`-flag is set), acting on
  functions by pullback; the geometric point is the generic one (`Orbicurve.affineOrbifold`).
  When `E[ℓ] ⊆ E(k)` — which holds at every place used by the Θ-data — this is exactly the
  orbicurve `(E/M) ∖ (E[ℓ]/M)` (resp. its `{±1}`-quotient). Otherwise the removed set is only
  the rational part of `E[ℓ] + M`.
* `tempPi1 X` is `TemperedFundamentalGroups.AffineOrbifold.canonicalTemperedPi1`: the tempered
  fundamental group over the canonical valuation of `k` (the henselian discrete valuation ring
  of `k` if there is one — `O_v` for the completions `K_v` — and the trivial valuation
  otherwise), defined as the automorphism group of the fibre functor on tempered coverings
  presented through projective integral models (see that repository's `Blueprint.md` for the
  identification with André's definition and what is cited there).
* `tempToEtale X` is the comparison map to the étale fundamental group
  `AffineOrbifold.etalePi1` of the same presentation, followed by a continuous comparison
  `EtaleComparison` with `Pi1.pi1`. For the genuine étale theory this comparison is the
  identification of two presentations of `π₁ᵉᵗ` of the orbicurve; it is the identity when the
  étale theory is defined through `AffineOrbifold.etalePi1Profinite`.
-/

namespace Iut.Anabelian

universe u

open TemperedFundamentalGroups
open scoped Classical

/-- **The affine presentation** of a model orbicurve: `[Spec R / A]` with `Spec R = E ∖ S`,
`S = E(k)[ℓ] + M`, `A = {P ↦ εP + m}`, at the generic geometric point. -/
noncomputable def Orbicurve.affineOrbifold {k : Type u} [Field k] (X : Orbicurve k) :
    AffineOrbifold k :=
  TemperedFundamentalGroups.Orbicurve.orbicurveOrbifold X.E X.level X.M X.pm

/-- A continuous comparison of the étale fundamental group of the affine presentation with the
étale fundamental groups of an étale theory. -/
structure EtaleComparison (Pi1 : EtalePi1Theory.{u}) : Type (u + 1) where
  /-- The comparison homomorphism. -/
  hom : ∀ {k : Type u} [Field k] (X : Orbicurve k), X.affineOrbifold.etalePi1 →* Pi1.pi1 X
  /-- It is continuous. -/
  continuous_hom : ∀ {k : Type u} [Field k] (X : Orbicurve k), Continuous (hom X)

/-- **The tempered fundamental groups of the model orbicurves**, from the construction through
integral models (lana-agents/tempered-fundamental-groups), over the canonical valuation of the
base field. -/
noncomputable def temperedTheory (Pi1 : EtalePi1Theory.{u}) (C : EtaleComparison Pi1) :
    TemperedPi1Theory Pi1 where
  tempPi1 X := X.affineOrbifold.canonicalTemperedPi1
  tempPi1Group _ := inferInstance
  tempPi1Topology _ := inferInstance
  tempToEtale X := (C.hom X).comp (X.affineOrbifold.temperedToEtale _)
  tempToEtale_continuous X :=
    (C.continuous_hom X).comp (X.affineOrbifold.continuous_temperedToEtale _)

end Iut.Anabelian
