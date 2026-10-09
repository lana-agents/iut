/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Cor312.ThetaData.AdmissiblePrime
import Iut.Anabelian.GenuineEtale

/-!
# Initial Θ-data: ℓ-torsion orbicurves, K-core, and distinguished cusp (taxis #41)

The global orbicurve, core, covering, and distinguished-cusp portion of initial Θ-data,
IUT I, Definition 3.1(d) and the global part of (f), for the Corollary 3.12 variant
statement (taxis #33).

## The anabelian objects

The orbicurves are the model orbicurves `Iut.Anabelian.Orbicurve` (`(E, ℓ, M, ±)`, standing for
`(E/M) ∖ (E[ℓ]/M)` and its `±1`-quotient, `Iut.Anabelian.Model`) with their finite étale covers
`Orbicurve.Cover`, base change, cusps, rank-one quotients and the orbicurve types of *The Étale
Theta Function*, Definition 2.1. Their fundamental groups are the **genuine** arithmetic étale
fundamental groups `Orbicurve.genuinePi1`, a cover inducing the open immersion
`Iut.Anabelian.genuinePi1Cover` (`genuinePi1Cover_isOpenEmbedding`), and `k`-cores are the
**genuine** cores `Iut.Anabelian.genuineHasCore` of [CanLift], §2. Basepoints of fundamental
groups are suppressed throughout: each `π₁` is the étale fundamental group up to conjugation,
as is standard in IUT I, §3.

## The packaged data

`Iut.OrbicurveData` packages, over the global data (taxis #39) and admissible-prime
data (taxis #40):

* `C_F = X_F/{±1}` and its base change `C_K = C_F ×_F K` to the `ℓ`-torsion field `K`
  (both *derived*, not chosen: `OrbicurveData.CF`, `OrbicurveData.CK`);
* a chosen orbicurve `C̲_K` of type `(1, ℓ-tors)^±` with `K`-core `C_K`, and the
  associated `X̲_K` of type `(1, ℓ-tors)` with its covering diagram over `X_K` and
  `C_K`, required to be cartesian, with the induced open immersions of fundamental
  groups (IUT I, Definition 3.1(d); *The Étale Theta Function*, Definitions 2.1, 2.3);
* a distinguished cusp `ε` of `C̲_K` arising from a nonzero element of the rank-one
  quotient `Q` (IUT I, Definition 3.1(f), global part). The arrow-decorated covers at
  good places that `ε` determines are packaged with the valuation-indexed local data
  (taxis #42), as they are indexed by places.

The valuation-by-valuation conditions of Definition 3.1(e)–(f) are deliberately not
imposed here (scope of taxis #42).
-/

namespace Iut

universe u

open WeierstrassCurve Iut.Anabelian

namespace OrbicurveDataSection

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (NumberField.FinitePlace ↥(fieldOfModuli F E)))

/-- The quotient orbicurve `C_F = X_F/{±1}` (IUT I, Definition 3.1(a); derived, not
chosen). -/
noncomputable def CF : Orbicurve F := Orbicurve.pmQuotient (Orbicurve.oncePunctured E)

/-- **`X_F/{±1}` is the core of `X_F` after every extension of the base field** (of
characteristic `0`): for every embedding `F → K`, `C_K` is the `K`-core of `X_K`. This is the form
in which the core condition of IUT I, Definition 3.1(d) (over the `ℓ`-torsion field) is supplied
to the existence of Θ-data; for non-exceptional `j(E)` it follows from [CanLift], Proposition 2.7
over `K` (`j(E_K) = j(E)`), without any base-change property of cores. -/
def HasCoreUniversally : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : F →+* K),
    genuineHasCore ((Orbicurve.oncePunctured E).baseChange f) ((CF F E).baseChange f)

variable (P : AdmissiblePrimeData F E Fbar VBad)

/-- The base change `X_K = X_F ×_F K` to the `ℓ`-torsion field (derived). -/
noncomputable def XK : Orbicurve ↥P.torsionField :=
  (Orbicurve.oncePunctured E).baseChange (algebraMap F ↥P.torsionField)

/-- The base change `C_K = C_F ×_F K` to the `ℓ`-torsion field (IUT I,
Definition 3.1(d); derived). -/
noncomputable def CK : Orbicurve ↥P.torsionField :=
  (CF F E).baseChange (algebraMap F ↥P.torsionField)

/-- **IUT I, Definition 3.1(d) and the global part of (f)**: the chosen orbicurve
`C̲_K` of type `(1, ℓ-tors)^±` with `K`-core `C_K`, the associated `X̲_K` with its
cartesian covering diagram, and the distinguished cusp `ε` arising from a nonzero
element of the rank-one quotient `Q`. -/
structure OrbicurveData : Type u where
  /-- The chosen orbicurve `C̲_K` over `K` (IUT I, Definition 3.1(d)). -/
  CKu : Orbicurve ↥P.torsionField
  /-- `C̲_K` is of type `(1, ℓ-tors)^±`. -/
  CKu_type : CKu.IsTypeOneEllTorsPM P.ℓ
  /-- `C̲_K` has `K`-core `C_K = C_F ×_F K`. -/
  CKu_core : genuineHasCore CKu (CK F E Fbar VBad P)
  /-- The associated orbicurve `X̲_K` (IUT I, Definition 3.1(d)). -/
  XKu : Orbicurve ↥P.torsionField
  /-- `X̲_K` is of type `(1, ℓ-tors)`. -/
  XKu_type : XKu.IsTypeOneEllTors P.ℓ
  /-- The covering `X̲_K → X_K`. -/
  XKu_to_XK : Orbicurve.Cover XKu (XK F E Fbar VBad P)
  /-- The covering `X̲_K → C̲_K`. -/
  XKu_to_CKu : Orbicurve.Cover XKu CKu
  /-- The covering `X_K → C_K` (base change of `X_F → C_F`). -/
  XK_to_CK : Orbicurve.Cover (XK F E Fbar VBad P) (CK F E Fbar VBad P)
  /-- The covering `C̲_K → C_K`. -/
  CKu_to_CK : Orbicurve.Cover CKu (CK F E Fbar VBad P)
  /-- The covering diagram of IUT I, Definition 3.1(d) is **cartesian**: `X̲_K` is the
  fiber product of `X_K` and `C̲_K` over `C_K`. The corresponding open immersions of
  fundamental groups are `genuinePi1Cover` of the four covers (open immersions,
  `genuinePi1Cover_isOpenEmbedding`; see `OrbicurveData.pi1XKu_to_CKu` and its siblings). -/
  diagram_cartesian : Orbicurve.IsCartesianSquare XKu_to_XK XK_to_CK XKu_to_CKu CKu_to_CK
  /-- The identification of the rank-one quotient `Q` of `C̲_K` with `ℤ/ℓℤ` (chosen
  identification; only the nonvanishing in `epsilon_spec` depends on it, and that
  condition is invariant under the choice). -/
  QIso : CKu.Q ≃ ZMod P.ℓ
  /-- The element of `Q` giving rise to the distinguished cusp. -/
  q : CKu.Q
  /-- The chosen element of `Q` is nonzero (IUT I, Definition 3.1(f)). -/
  q_ne_zero : QIso q ≠ 0
  /-- The **distinguished cusp** `ε` of `C̲_K`: the cusp associated to the chosen
  nonzero element of the rank-one quotient (IUT I, Definition 3.1(f)). -/
  epsilon : CKu.Cusp
  /-- `ε` is the cusp of the chosen element. -/
  epsilon_spec : epsilon = CKu.cuspOf q

namespace OrbicurveData

variable {F E Fbar VBad P} (O : OrbicurveData F E Fbar VBad P)

/-- The open immersion of fundamental groups `π₁(X̲_K) → π₁(C̲_K)` induced by the
covering `X̲_K → C̲_K` (IUT I, Definition 3.1(d)). -/
noncomputable def pi1XKu_to_CKu : O.XKu.genuinePi1 →* O.CKu.genuinePi1 :=
  genuinePi1Cover O.XKu_to_CKu

lemma pi1XKu_to_CKu_isOpenEmbedding :
    Topology.IsOpenEmbedding O.pi1XKu_to_CKu :=
  genuinePi1Cover_isOpenEmbedding O.XKu_to_CKu

/-- The open immersion `π₁(X̲_K) → π₁(X_K)` induced by the covering `X̲_K → X_K`. -/
noncomputable def pi1XKu_to_XK : O.XKu.genuinePi1 →* (XK F E Fbar VBad P).genuinePi1 :=
  genuinePi1Cover O.XKu_to_XK

lemma pi1XKu_to_XK_isOpenEmbedding :
    Topology.IsOpenEmbedding O.pi1XKu_to_XK :=
  genuinePi1Cover_isOpenEmbedding O.XKu_to_XK

/-- The open immersion `π₁(X_K) → π₁(C_K)` induced by the covering `X_K → C_K`. -/
noncomputable def pi1XK_to_CK :
    (XK F E Fbar VBad P).genuinePi1 →* (CK F E Fbar VBad P).genuinePi1 :=
  genuinePi1Cover O.XK_to_CK

lemma pi1XK_to_CK_isOpenEmbedding :
    Topology.IsOpenEmbedding O.pi1XK_to_CK :=
  genuinePi1Cover_isOpenEmbedding O.XK_to_CK

/-- The open immersion `π₁(C̲_K) → π₁(C_K)` induced by the covering `C̲_K → C_K`. -/
noncomputable def pi1CKu_to_CK : O.CKu.genuinePi1 →* (CK F E Fbar VBad P).genuinePi1 :=
  genuinePi1Cover O.CKu_to_CK

lemma pi1CKu_to_CK_isOpenEmbedding :
    Topology.IsOpenEmbedding O.pi1CKu_to_CK :=
  genuinePi1Cover_isOpenEmbedding O.CKu_to_CK

end OrbicurveData

end OrbicurveDataSection

end Iut
