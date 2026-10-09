/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.ThetaData.LocalConditions
import Iut.Anabelian.AdicCompletion
import Iut.Anabelian.TemperedAndre

/-!
# `Π_v` at the bad places is André's tempered fundamental group

At a place `v` of the valuation section of initial Θ-data, `Π_v` at bad places
(`Iut.LocalThetaData.PivBad`) is the tempered fundamental group `Orbicurve.temperedPi1` of the
local model `X̲_v` over the completion `K_v`. This module identifies it, with no hypotheses
beyond the Θ-data, with André's tempered fundamental group `Orbicurve.andrePi1` of `X̲_v`
(`Iut.LocalThetaData.pivBadEquivAndre`), by Theorem A of lana-agents/tempered-fundamental-groups
(`TemperedFundamentalGroups.andreEquiv'`, via `Iut.Anabelian.Orbicurve.temperedEquivAndre`):

* `K_v` has characteristic `0`;
* the canonical valuation subring of `K_v` is `O_v` (F. K. Schmidt), a complete discrete
  valuation ring with finite, hence perfect, residue field of mixed characteristic
  (`Iut.Anabelian.AdicCompletion`);
* the presentation of `X̲_v` in characteristic `0` has a smooth coordinate ring of Krull
  dimension `1` and a finite group (`lana-agents/pi1`).

## Source correspondence

IUT I, Definition 3.1(e)–(f) (`Π_v` is the tempered fundamental group of `X̲_v` at bad places);
Y. André, *Period mappings and differential equations*, III.2.1 (the tempered fundamental group).
-/

namespace Iut

universe u

open NumberField IsDedekindDomain WeierstrassCurve OrbicurveDataSection Iut.Anabelian

section LocalData

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}
variable {P : AdmissiblePrimeData F E Fbar VBad}
variable [NumberField ↥P.torsionField]
variable [Algebra ↥(fieldOfModuli F E) ↥P.torsionField]

namespace LocalThetaData

variable {O : OrbicurveData F E Fbar VBad P} (L : LocalThetaData F E Fbar VBad P O)

/-- **`Π_v` is André's tempered fundamental group** (IUT I, Definition 3.1(e)/(f); Theorem A of
lana-agents/tempered-fundamental-groups): the tempered fundamental group `Π_v` of the local
model `X̲_v` (the convention at bad places) is isomorphic, as a topological group, to André's
tempered fundamental group of `X̲_v`. No hypothesis beyond the Θ-data is needed. -/
noncomputable def pivBadEquivAndre (v : FinitePlace ↥(fieldOfModuli F E)) :
    L.PivBad v ≃ₜ* (localize (L.sect.sectFin v) O.XKu).andrePi1 :=
  (localize (L.sect.sectFin v) O.XKu).temperedEquivAndre
    (AdicCompletion.exists_prime_canonical _)

end LocalThetaData

end LocalData

end Iut
