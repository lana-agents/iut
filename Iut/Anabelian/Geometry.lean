/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Anabelian.Local
import Iut.Cor312.ThetaData.LocalConditions

/-!
# The model terms of the anabelian and tempered interfaces (taxis #276, #279)

`Iut.Anabelian.modelAG` is a term of `Iut.AnabelianGeometry` built from the model
orbicurves of `Iut.Anabelian.Model` and the local predicates of `Iut.Anabelian.Local`;
`Iut.Anabelian.modelTG` is the corresponding term of `Iut.TemperedGeometry`. Both are
closed terms: no residual interface remains (fundamental groups and cores are not part of
the interfaces; see the README, "Honesty boundary").

Field by field (taxis #276):

1. `Orbicurve` — the model orbicurves `(E, ℓ, M, ±)`.
2. `Cover`, `coverComp` — the covers induced by `[n]`, composed.
3. `baseChange`, `coverBaseChange`, `cuspBaseChange` — transport along field embeddings.
4. `oncePunctured` — `(E, 1, 0, −)`.
5. `pmQuotient` — setting the `±`-flag.
6. `IsCartesianSquare` — the `±`-quotient squares.
7. `Cusp` — `E(k)[ℓ]/M`, modulo `±`.
8. `IsTypeOneEllTors`, `IsTypeOneEllTorsPM`, `IsTypeOneZModPM` — the orbicurve types;
   `TateStructure` — the Tate structures `Iut.TateStructure` on the underlying curve.
9. `RankOneQuotient`, `cuspOfQuotient` — `E(k)[ℓ]/M` and the class map.
10. `IsThetaRootModel`, `canonicalGraphCusp` (of `TemperedGeometry`) — from
    `Iut.Anabelian.Local`.
-/

namespace Iut.Anabelian

universe u

open WeierstrassCurve
open scoped Classical

/-- **The model anabelian geometry.** -/
noncomputable def modelAG : AnabelianGeometry.{u} where
  Orbicurve k _ := Orbicurve k
  Cover := Orbicurve.Cover
  coverComp := Orbicurve.Cover.comp
  baseChange f X := X.baseChange f
  coverBaseChange := @fun _ _ _ _ f _ _ c => Orbicurve.Cover.baseChange f c
  oncePunctured E _ := Orbicurve.oncePunctured E
  pmQuotient := Orbicurve.pmQuotient
  IsCartesianSquare := Orbicurve.IsCartesianSquare
  Cusp := Orbicurve.Cusp
  cuspBaseChange f X c := X.cuspBaseChange f c
  IsTypeOneEllTors := Orbicurve.IsTypeOneEllTors
  IsTypeOneEllTorsPM := Orbicurve.IsTypeOneEllTorsPM
  TateStructure X := TateStructure X.E
  IsTypeOneZModPM := Orbicurve.IsTypeOneZModPM
  RankOneQuotient X _ := X.Q
  cuspOfQuotient X _ q := X.cuspOf q

/-- **The model tempered geometry**: theta-root models and the canonical graph cusp from
the local predicates of `Iut.Anabelian.Local`. -/
noncomputable def modelTG : TemperedGeometry modelAG.{u} where
  IsThetaRootModel := Orbicurve.IsThetaRootModel
  canonicalGraphCusp := Orbicurve.canonicalGraphCusp

end Iut.Anabelian
