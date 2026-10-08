/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalEstimate
import Iut.Implication.Corollary23

/-!
# The implication for the concrete variant (taxis #1449)

The Corollary 3.12 variant, assumed only for the **concrete** data bundles
`Iut.concreteVariantData D` (a function of the initial Θ-data `D` alone: the tensor packets of
the `ℓ`-torsion field, the local theta data of `D` and its `q`-pilot data), feeds the
implication of `Iut/Implication/Corollary23.lean` through `IsConcrete` and
`ConcreteThetaDataExistence.toThetaDataExistence`.

The existence of suitable initial Θ-data is required in concrete form
(`ConcreteThetaDataExistence`): for a point of large height and a prime `ℓ` satisfying
(P1)–(P6), initial Θ-data `D` with the prime `ℓ` and the tower arithmetic. Everything else — the Theorem 1.10 invariants, certificate and
local estimates — is constructed from these (`InitialThetaData.invariants`,
`TowerArithmetic.certificate`, `TowerArithmetic.localEstimate`). The existence statement
itself is proved from the curves of the points in `Iut.Concrete.Existence`
(`CurveInputs.concreteThetaDataExistence`).
-/

namespace Iut

universe u

open NumberField

variable {T : Genl.HeightTheory}

/-- The data bundles produced by the concrete construction. -/
def IsConcrete (X : Corollary312VariantData.{u, u}) : Prop :=
  ∃ D : InitialThetaData.{u}, X = concreteVariantData D

/-- **Existence of suitable initial Θ-data, concrete form** ((P7) in the proof of
Corollary 2.2): for a point `x` outside the exceptional set and a prime `ℓ ≥ 7` satisfying
(P2), (P3), (P5), (P6), initial Θ-data with prime `ℓ` together with the arithmetic of its
tower ((R4) and Steps (ii), (iii) of the proof of Theorem 1.10), with the expected relations
to `x`. Proved for the tripod in `Iut.Tripod.concreteThetaDataExistence'` from the curves of
the points and the anabelian construction of IUT I, Definition 3.1(d)–(f)
(`Iut.AdmissiblePrimeData.orbicurveData`, `localThetaData`; taxis #1469). -/
def ConcreteThetaDataExistence {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d) : Prop :=
  ∀ x (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ v ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv v) →
    (∀ v ∈ (I.localData x hx).bad, (I.localData x hx).p v = ℓ →
      ((I.localData x hx).hv v : ℝ) < Real.sqrt (I.h x)) →
    (∃ v ∈ (I.localData x hx).bad, (I.localData x hx).p v ≠ 2 ∧ (I.localData x hx).p v ≠ ℓ) →
    I.SL2Image x ℓ →
    ∃ D : InitialThetaData.{u}, TowerArithmetic D ∧
      D.ℓ = ℓ ∧ D.dmod ≤ d ∧
      (concreteVariantData.{u} D).qPilot.logQ =
        (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = logDifferentDeg ↥D.tripodalField ∧
      D.logConductorDeg ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ D.logConductorDeg + Real.log (2 * ℓ)

/-- The concrete existence statement provides the general one, with the concrete data
bundles. -/
theorem ConcreteThetaDataExistence.toThetaDataExistence {K : T.CBS} {d : ℕ}
    {I : Corollary22Inputs T K d}
    (ex : ConcreteThetaDataExistence.{u} I) :
    ThetaDataExistence (IsConcrete.{u}) I where
  thetaData x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6 := by
    obtain ⟨D, TA, hℓ, hd, hq, hdiff, hc1, hc2⟩ :=
      ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
    refine ⟨concreteVariantData.{u} D, D.invariants, ⟨D, rfl⟩,
      TA.certificate (hℓ ▸ hℓ7), ⟨TA.localEstimate⟩, hℓ, hd, hq, hdiff, hc1, ?_⟩
    exact hc2

end Iut
