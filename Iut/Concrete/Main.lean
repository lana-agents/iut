/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalEstimate
import Iut.Implication.Corollary23

/-!
# The implication for the concrete variant (taxis #1449)

The main theorem `Iut.cor312Variant_implies_abc_concrete`: the Corollary 3.12 variant,
assumed only for the **concrete** data bundles `Iut.concreteVariantData D LT TL QI` —
initial Θ-data together with the local-field theory of the `ℓ`-torsion field, the local
theta data and the finiteness of the bad locus — implies ABC.

The existence of suitable initial Θ-data is required in concrete form
(`ConcreteThetaDataExistence`): for a point of large height and a prime `ℓ` satisfying
(P1)–(P6), initial Θ-data `D` with the prime `ℓ`, its local theory and local theta data,
and the tower arithmetic. Everything else — the Theorem 1.10 invariants, certificate and
local estimates — is constructed from these (`ThetaLocalData.invariants`,
`TowerArithmetic.certificate`, `TowerArithmetic.localEstimate`). The existence statement
itself is proved from the curves of the points in `Iut.Concrete.Existence`
(`CurveInputs.concreteThetaDataExistence`).
-/

namespace Iut

universe u v

open NumberField

variable {T : Genl.HeightTheory}
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The data bundles produced by the concrete construction. -/
def IsConcrete (X : Corollary312VariantData.{u, v} AG TG) : Prop :=
  ∃ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)
    (QI : QPilotInputs D), X = concreteVariantData D LT TL QI

/-- **Existence of suitable initial Θ-data, concrete form** ((P7) in the proof of
Corollary 2.2): for a point `x` outside the exceptional set and a prime `ℓ ≥ 7` satisfying
(P2), (P3), (P5), (P6), initial Θ-data with prime `ℓ` together with the local-field theory
and local theta data of its `ℓ`-torsion field, the finiteness of its bad locus, the
arithmetic inputs of its tower, and Steps (ii), (iii) of the proof of Theorem 1.10, with
the expected relations to `x`. Proved in `Iut.Concrete.Existence` from the curves of the
points, the standard providers, and the anabelian existence `Iut.AnabelianExistence`
(IUT I, Definition 3.1(d)–(f); taxis #1469). -/
def ConcreteThetaDataExistence {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d) : Prop :=
  ∀ x (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ v ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv v) →
    (∀ v ∈ (I.localData x hx).bad, (I.localData x hx).p v = ℓ →
      ((I.localData x hx).hv v : ℝ) < Real.sqrt (I.h x)) →
    (∃ v ∈ (I.localData x hx).bad, (I.localData x hx).p v ≠ 2 ∧ (I.localData x hx).p v ≠ ℓ) →
    I.SL2Image x ℓ →
    ∃ (D : InitialThetaData.{u} AG TG) (LT : LocalTheory.{u, v} D.Kt) (TL : ThetaLocalData D LT)
      (QI : QPilotInputs D), TowerArithmetic D LT TL ∧
      D.ℓ = ℓ ∧ D.dmod ≤ d ∧
      (concreteVariantData.{u, v} D LT TL QI).qPilot.logQ =
        (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = logDifferentDeg ↥D.tripodalField ∧
      D.logConductorDeg ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ D.logConductorDeg + Real.log (2 * ℓ)

/-- The concrete existence statement provides the general one, with the concrete data
bundles. -/
theorem ConcreteThetaDataExistence.toThetaDataExistence {K : T.CBS} {d : ℕ}
    {I : Corollary22Inputs T K d}
    (ex : ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) I) :
    ThetaDataExistence (IsConcrete.{u, v} (AG := AG) (TG := TG)) I where
  thetaData x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6 := by
    obtain ⟨D, LT, TL, QI, TA, hℓ, hd, hq, hdiff, hc1, hc2⟩ :=
      ex x hx hxe ℓ hℓp hℓ7 hP2 hP3 hP5 hP6
    refine ⟨concreteVariantData.{u, v} D LT TL QI, TL.invariants QI, ⟨D, LT, TL, QI, rfl⟩,
      TA.certificate (hℓ ▸ hℓ7), ⟨TA.localEstimate⟩, hℓ, hd, hq, hdiff, hc1, ?_⟩
    exact hc2

/-- **The Corollary 3.12 variant for the concrete data bundles implies ABC.** -/
theorem cor312Variant_implies_abc_concrete (A : T.ProofPackage)
    (I : ∀ (K : T.CBS) (d : ℕ), Corollary22Inputs T K d)
    (ex : ∀ K d, ConcreteThetaDataExistence.{u, v} (AG := AG) (TG := TG) (I K d))
    (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ (D : InitialThetaData AG TG) (LT : LocalTheory.{u, v} D.Kt)
      (TL : ThetaLocalData D LT) (QI : QPilotInputs D),
      Corollary312Variant (concreteVariantData.{u, v} D LT TL QI)) :
    ABC T :=
  cor312Variant_implies_abc A I (fun K d => (ex K d).toThetaDataExistence) cheb pnt
    fun _ ⟨D, LT, TL, QI, hX⟩ => hX ▸ h312 D LT TL QI

end Iut
