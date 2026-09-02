/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Local
import Iut.Cor312.ThetaData.LocalConditions

/-!
# The model terms of the anabelian and tempered interfaces (taxis #276, #279)

`Iut.Anabelian.modelAG Pi1` is a term of `Iut.AnabelianGeometry` built from the model
orbicurves of `Iut.Anabelian.Model` and the local predicates of `Iut.Anabelian.Local`,
with the fundamental-group fields supplied by the residual interface
`Iut.Anabelian.EtalePi1Theory Pi1`. `Iut.Anabelian.modelTG Pi1 T` is the corresponding term of
`Iut.TemperedGeometry`, with the tempered fundamental groups supplied by the residual
interface `Iut.Anabelian.TemperedPi1Theory Pi1 T` (taxis #7).

Field by field (taxis #276):

1. `Orbicurve` — the model orbicurves `(E, ℓ, M, ±)`.
2. `Cover`, `coverComp` — the covers induced by `[n]`, composed.
3. `baseChange`, `coverBaseChange`, `cuspBaseChange` — transport along field embeddings.
4. `oncePunctured` — `(E, 1, 0, −)`.
5. `pmQuotient` — setting the `±`-flag.
6.–7. `pi1`, `pi1Cover`, continuity and open-immersion — residual (`EtalePi1Theory`).
8. `IsCartesianSquare` — the `±`-quotient squares.
9. `Cusp` — `E(k)[ℓ]/M`, modulo `±`.
10. `HasCore` — residual (`EtalePi1Theory`; its classification is taxis #10).
11. `IsTypeOneEllTors`, `IsTypeOneEllTorsPM`, `IsTypeOneZModPM` — the orbicurve types.
12. `RankOneQuotient`, `cuspOfQuotient` — `E(k)[ℓ]/M` and the class map.
-/

namespace Iut.Anabelian

universe u

open WeierstrassCurve
open scoped Classical

/-- **The model anabelian geometry** attached to a theory of étale fundamental groups of
the model orbicurves. -/
noncomputable def modelAG (Pi1 : EtalePi1Theory.{u}) : AnabelianGeometry.{u} where
  Orbicurve k _ := Orbicurve k
  Cover := Orbicurve.Cover
  coverComp := Orbicurve.Cover.comp
  baseChange f X := X.baseChange f
  coverBaseChange := @fun _ _ _ _ f _ _ c => Orbicurve.Cover.baseChange f c
  oncePunctured E _ := Orbicurve.oncePunctured E
  pmQuotient := Orbicurve.pmQuotient
  pi1 := Pi1.pi1
  pi1Cover := Pi1.pi1Cover
  pi1Cover_continuous := Pi1.pi1Cover_continuous
  pi1Cover_isOpenEmbedding := Pi1.pi1Cover_isOpenEmbedding
  IsCartesianSquare := Orbicurve.IsCartesianSquare
  Cusp := Orbicurve.Cusp
  cuspBaseChange f X c := X.cuspBaseChange f c
  HasCore := Pi1.HasCore
  IsTypeOneEllTors := Orbicurve.IsTypeOneEllTors
  IsTypeOneEllTorsPM := Orbicurve.IsTypeOneEllTorsPM
  IsTypeOneZModPM := Orbicurve.IsTypeOneZModPM
  RankOneQuotient X _ := X.Q
  cuspOfQuotient X _ q := X.cuspOf q

/-- **Tempered fundamental groups of the model orbicurves** (residual interface of taxis
#7): the tempered fundamental group of each model orbicurve as a topological group, with
its comparison homomorphism to the profinite étale fundamental group. -/
structure TemperedPi1Theory (Pi1 : EtalePi1Theory.{u}) : Type (u + 1) where
  /-- The tempered fundamental group. -/
  tempPi1 : {k : Type u} → [Field k] → Orbicurve k → Type u
  /-- Group structure. -/
  tempPi1Group : ∀ {k : Type u} [Field k] (X : Orbicurve k), Group (tempPi1 X)
  /-- Topology. -/
  tempPi1Topology : ∀ {k : Type u} [Field k] (X : Orbicurve k), TopologicalSpace (tempPi1 X)
  /-- The comparison homomorphism to the étale fundamental group. -/
  tempToEtale : ∀ {k : Type u} [Field k] (X : Orbicurve k),
    letI := tempPi1Group X; tempPi1 X →* Pi1.pi1 X
  /-- The comparison homomorphism is continuous. -/
  tempToEtale_continuous : ∀ {k : Type u} [Field k] (X : Orbicurve k),
    letI := tempPi1Group X; letI := tempPi1Topology X
    Continuous (tempToEtale X)

/-- **The model tempered geometry**: tempered fundamental groups from the residual
interface, theta-root models and the canonical graph cusp from the local predicates of
`Iut.Anabelian.Local`. -/
noncomputable def modelTG (Pi1 : EtalePi1Theory.{u}) (T : TemperedPi1Theory Pi1) :
    TemperedGeometry (modelAG Pi1) where
  tempPi1 := T.tempPi1
  tempPi1Group := T.tempPi1Group
  tempPi1Topology := T.tempPi1Topology
  tempToEtale := T.tempToEtale
  tempToEtale_continuous := T.tempToEtale_continuous
  IsThetaRootModel := Orbicurve.IsThetaRootModel
  canonicalGraphCusp X := X.canonicalGraphCusp

end Iut.Anabelian
