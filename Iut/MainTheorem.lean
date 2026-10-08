/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.ClassicalAbc
import Iut.Tripod.GeneralPosition
import Iut.Tripod.Main

/-!
# The main theorem: the Corollary 3.12 variant implies the classical ABC conjecture

`Iut.classicalABC_of_variant : Iut.Cor312VariantHolds → Iut.ClassicalABC`, where

`Iut.Cor312VariantHolds := ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)`

(`Iut/Concrete/ThetaRegion.lean`). The hypothesis ranges over exactly the initial Θ-data of
IUT I, Definition 3.1 (`Iut.InitialThetaData`), stated about the genuine objects: the model
orbicurves `Iut.Anabelian.Orbicurve`, their arithmetic étale fundamental groups
`Orbicurve.genuinePi1` with the open immersions `genuinePi1Cover` induced by covers, the
genuine `k`-cores `genuineHasCore`, and the tempered fundamental groups `Orbicurve.temperedPi1`
with the comparison `Orbicurve.tempToEtale`. The variant data `concreteVariantData D` (the
`q`-pilot data, the tensor packets of the `ℓ`-torsion field with their log-shells,
log-volumes and hulls, and the theta-pilot region built from the `2ℓ`-th roots of the Tate
parameters) are a function of `D`.

The proof: the variant implies [GenEll] Theorem 2.1(ii) for the tripod
(`Iut.Tripod.abc_of_variant`), which implies Theorem 2.1(i)
(`Iut.Tripod.statementI_of_statementII`), which implies the classical ABC conjecture
(`Iut.Tripod.classicalABC_of_statementI`).
-/

namespace Iut

/-- **The Corollary 3.12 variant implies the classical ABC conjecture.** -/
theorem classicalABC_of_variant (h312 : Cor312VariantHolds) : ClassicalABC :=
  Tripod.classicalABC_of_statementI (Tripod.statementI_of_statementII (Tripod.abc_of_variant h312))

end Iut
