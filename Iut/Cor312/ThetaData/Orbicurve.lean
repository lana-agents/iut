/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.AdmissiblePrime

/-!
# Initial Θ-data: ℓ-torsion orbicurves, K-core, and distinguished cusp (taxis #41)

The global orbicurve, core, covering, and distinguished-cusp portion of initial Θ-data,
IUT I, Definition 3.1(d) and the global part of (f), for the Corollary 3.12 variant
statement (taxis #33).

## The anabelian interface

Hyperbolic orbicurves, their finite étale coverings, and their arithmetic fundamental
groups are not available in Mathlib. Following the honesty boundary of this repository,
they enter through the explicit interface structure `Iut.AnabelianGeometry`: a bundle
of types and operations (orbicurves over a field, finite étale covers, base change,
once-punctured elliptic curves, `±1`-quotients, étale fundamental groups as profinite
groups with open immersions for covers, cusps, cores, and the orbicurve-type predicates
of *The Étale Theta Function*, Definition 2.1). Every intended property is either a
field of the interface or a field of the data structures consuming it — never
axiomatic. Discharging this interface is the business of the anabelian-geometry
projects
(taxis #7 `lana-agents/tempered-fundamental-groups`, taxis #10
`lana-agents/orbicurve-cores`, and successors); this module supplies the definitions
that taxis #10 consumes, and does not prove the classification theorem requested there.

## The packaged data

`Iut.OrbicurveData` packages, over the global data (taxis #39) and admissible-prime
data (taxis #40) and relative to an anabelian interface:

* `C_F = X_F/{±1}` and its base change `C_K = C_F ×_F K` to the `ℓ`-torsion field `K`
  (both *derived*, not chosen: `OrbicurveData.CF`, `OrbicurveData.CK`);
* a chosen orbicurve `C̲_K` of type `(1, ℓ-tors)^±` with `K`-core `C_K`, and the
  associated `X̲_K` of type `(1, ℓ-tors)` with its covering diagram over `X_K` and
  `C_K`, required to be cartesian, with the induced open immersions of fundamental
  groups available from the interface (IUT I, Definition 3.1(d); *The Étale Theta
  Function*, Definitions 2.1, 2.3);
* a distinguished cusp `ε` of `C̲_K` arising from a nonzero element of the rank-one
  quotient `Q` (IUT I, Definition 3.1(f), global part). The arrow-decorated covers at
  good places that `ε` determines are packaged with the valuation-indexed local data
  (taxis #42), as they are indexed by places.

The valuation-by-valuation conditions of Definition 3.1(e)–(f) are deliberately not
imposed here (scope of taxis #42).
-/

namespace Iut

universe u

open WeierstrassCurve

/-- Interface for the anabelian geometry of hyperbolic orbicurves (seam for
taxis #7/#10 and successors): orbicurve types, finite étale covers, base change,
once-punctured elliptic curves, `±`-quotients, étale fundamental groups, cusps, cores,
and the orbicurve-type predicates of *The Étale Theta Function*, Definition 2.1.

Basepoints of fundamental groups are suppressed throughout: each `pi1` is the étale
fundamental group up to conjugation, as is standard in IUT I, §3. -/
structure AnabelianGeometry : Type (u + 1) where
  /-- Hyperbolic orbicurves over a field `k`. -/
  Orbicurve : (k : Type u) → [Field k] → Type u
  /-- Finite étale coverings of orbicurves over `k`. -/
  Cover : {k : Type u} → [Field k] → Orbicurve k → Orbicurve k → Type u
  /-- Composition of coverings. -/
  coverComp : {k : Type u} → [Field k] → {X Y Z : Orbicurve k} →
    Cover X Y → Cover Y Z → Cover X Z
  /-- Base change of an orbicurve along a field embedding. -/
  baseChange : {k K : Type u} → [Field k] → [Field K] → (k →+* K) →
    Orbicurve k → Orbicurve K
  /-- Base change of a finite étale cover along a field embedding. -/
  coverBaseChange : {k K : Type u} → [Field k] → [Field K] → (f : k →+* K) →
    {X Y : Orbicurve k} → Cover X Y → Cover (baseChange f X) (baseChange f Y)
  /-- The once-punctured elliptic curve `X = E ∖ {0}` attached to an elliptic curve. -/
  oncePunctured : {k : Type u} → [Field k] → (E : WeierstrassCurve k) →
    [E.IsElliptic] → Orbicurve k
  /-- The quotient of a hyperbolic orbicurve by its `±1`-action (where defined; for
  the once-punctured elliptic curve this is the quotient `C = X/{±1}`). -/
  pmQuotient : {k : Type u} → [Field k] → Orbicurve k → Orbicurve k
  /-- The arithmetic étale fundamental group of an orbicurve, a profinite group
  (basepoint suppressed; well-defined up to conjugation). -/
  pi1 : {k : Type u} → [Field k] → Orbicurve k → ProfiniteGrp.{u}
  /-- The homomorphism of fundamental groups induced by a finite étale cover. -/
  pi1Cover : {k : Type u} → [Field k] → {X Y : Orbicurve k} → Cover X Y →
    (pi1 X →* pi1 Y)
  /-- The induced homomorphisms are continuous. -/
  pi1Cover_continuous : ∀ {k : Type u} [Field k] {X Y : Orbicurve k} (f : Cover X Y),
    Continuous (pi1Cover f)
  /-- The induced homomorphisms are **open immersions** of profinite groups: open
  topological group embeddings onto open subgroups (IUT I, Definition 3.1(d), the
  displayed covering diagrams). -/
  pi1Cover_isOpenEmbedding : ∀ {k : Type u} [Field k] {X Y : Orbicurve k}
    (f : Cover X Y), Topology.IsOpenEmbedding (pi1Cover f)
  /-- A square of coverings is **cartesian** (a fiber-product square). -/
  IsCartesianSquare : {k : Type u} → [Field k] → {A B C D : Orbicurve k} →
    Cover A B → Cover B D → Cover A C → Cover C D → Prop
  /-- The cusps of an orbicurve. -/
  Cusp : {k : Type u} → [Field k] → Orbicurve k → Type u
  /-- Base change of cusps along a field embedding. -/
  cuspBaseChange : {k K : Type u} → [Field k] → [Field K] → (f : k →+* K) →
    {X : Orbicurve k} → Cusp X → Cusp (baseChange f X)
  /-- `core` relation: `C` is the `k`-core of `X` (the terminal object among the
  finite étale quotients of `X`; *Absolute Anabelian Geometry of Canonical Curves*,
  and IUT I, Definition 3.1(d) "with `K`-core `C_K`"). -/
  HasCore : {k : Type u} → [Field k] → (X C : Orbicurve k) → Prop
  /-- An orbicurve is of type `(1, ℓ-tors)` (*Étale Theta*, Definition 2.1). -/
  IsTypeOneEllTors : {k : Type u} → [Field k] → (ℓ : ℕ) → Orbicurve k → Prop
  /-- An orbicurve is of type `(1, ℓ-tors)^±` (*Étale Theta*, Definition 2.1). -/
  IsTypeOneEllTorsPM : {k : Type u} → [Field k] → (ℓ : ℕ) → Orbicurve k → Prop
  /-- An orbicurve is of type `(1, ℤ/ℓℤ)^±` (*Étale Theta*, Definition 2.5; used by
  the local conditions at bad places, taxis #42). -/
  IsTypeOneZModPM : {k : Type u} → [Field k] → (ℓ : ℕ) → Orbicurve k → Prop
  /-- The rank-one quotient `Q` attached to an orbicurve of type `(1, ℓ-tors)^±`
  (IUT I, Definition 3.1(f): the quotient of the module of cuspidal data that is free
  of rank one over `ℤ/ℓℤ`). For orbicurves not of that type the value is junk. -/
  RankOneQuotient : {k : Type u} → [Field k] → Orbicurve k → (ℓ : ℕ) → Type u
  /-- The cusp associated to an element of the rank-one quotient (junk at `0`;
  IUT I, Definition 3.1(f)). -/
  cuspOfQuotient : {k : Type u} → [Field k] → (X : Orbicurve k) → (ℓ : ℕ) →
    RankOneQuotient X ℓ → Cusp X

namespace OrbicurveDataSection

variable (AG : AnabelianGeometry.{u})
variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (NumberField.FinitePlace ↥(fieldOfModuli F E)))

/-- The quotient orbicurve `C_F = X_F/{±1}` (IUT I, Definition 3.1(a); derived, not
chosen). -/
noncomputable def CF : AG.Orbicurve F := AG.pmQuotient (AG.oncePunctured E)

variable (P : AdmissiblePrimeData F E Fbar VBad)

/-- The base change `X_K = X_F ×_F K` to the `ℓ`-torsion field (derived). -/
noncomputable def XK : AG.Orbicurve ↥P.torsionField :=
  AG.baseChange (algebraMap F ↥P.torsionField) (AG.oncePunctured E)

/-- The base change `C_K = C_F ×_F K` to the `ℓ`-torsion field (IUT I,
Definition 3.1(d); derived). -/
noncomputable def CK : AG.Orbicurve ↥P.torsionField :=
  AG.baseChange (algebraMap F ↥P.torsionField) (CF AG F E)

/-- **IUT I, Definition 3.1(d) and the global part of (f)**: the chosen orbicurve
`C̲_K` of type `(1, ℓ-tors)^±` with `K`-core `C_K`, the associated `X̲_K` with its
cartesian covering diagram, and the distinguished cusp `ε` arising from a nonzero
element of the rank-one quotient `Q`. -/
structure OrbicurveData : Type u where
  /-- The chosen orbicurve `C̲_K` over `K` (IUT I, Definition 3.1(d)). -/
  CKu : AG.Orbicurve ↥P.torsionField
  /-- `C̲_K` is of type `(1, ℓ-tors)^±`. -/
  CKu_type : AG.IsTypeOneEllTorsPM P.ℓ CKu
  /-- `C̲_K` has `K`-core `C_K = C_F ×_F K`. -/
  CKu_core : AG.HasCore CKu (CK AG F E Fbar VBad P)
  /-- The associated orbicurve `X̲_K` (IUT I, Definition 3.1(d)). -/
  XKu : AG.Orbicurve ↥P.torsionField
  /-- `X̲_K` is of type `(1, ℓ-tors)`. -/
  XKu_type : AG.IsTypeOneEllTors P.ℓ XKu
  /-- The covering `X̲_K → X_K`. -/
  XKu_to_XK : AG.Cover XKu (XK AG F E Fbar VBad P)
  /-- The covering `X̲_K → C̲_K`. -/
  XKu_to_CKu : AG.Cover XKu CKu
  /-- The covering `X_K → C_K` (base change of `X_F → C_F`). -/
  XK_to_CK : AG.Cover (XK AG F E Fbar VBad P) (CK AG F E Fbar VBad P)
  /-- The covering `C̲_K → C_K`. -/
  CKu_to_CK : AG.Cover CKu (CK AG F E Fbar VBad P)
  /-- The covering diagram of IUT I, Definition 3.1(d) is **cartesian**: `X̲_K` is the
  fiber product of `X_K` and `C̲_K` over `C_K`. The corresponding open immersions of
  fundamental groups are `AnabelianGeometry.pi1Cover` with
  `pi1Cover_isOpenEmbedding`. -/
  diagram_cartesian : AG.IsCartesianSquare XKu_to_XK XK_to_CK XKu_to_CKu CKu_to_CK
  /-- The identification of the rank-one quotient `Q` of `C̲_K` with `ℤ/ℓℤ` (chosen
  identification; only the nonvanishing in `epsilon_spec` depends on it, and that
  condition is invariant under the choice). -/
  QIso : AG.RankOneQuotient CKu P.ℓ ≃ ZMod P.ℓ
  /-- The element of `Q` giving rise to the distinguished cusp. -/
  q : AG.RankOneQuotient CKu P.ℓ
  /-- The chosen element of `Q` is nonzero (IUT I, Definition 3.1(f)). -/
  q_ne_zero : QIso q ≠ 0
  /-- The **distinguished cusp** `ε` of `C̲_K`: the cusp associated to the chosen
  nonzero element of the rank-one quotient (IUT I, Definition 3.1(f)). -/
  epsilon : AG.Cusp CKu
  /-- `ε` is the cusp of the chosen element. -/
  epsilon_spec : epsilon = AG.cuspOfQuotient CKu P.ℓ q

namespace OrbicurveData

variable {AG F E Fbar VBad P} (O : OrbicurveData AG F E Fbar VBad P)

/-- The open immersion of fundamental groups `π₁(X̲_K) → π₁(C̲_K)` induced by the
covering `X̲_K → C̲_K` (IUT I, Definition 3.1(d)). -/
noncomputable def pi1XKu_to_CKu : AG.pi1 O.XKu →* AG.pi1 O.CKu :=
  AG.pi1Cover O.XKu_to_CKu

lemma pi1XKu_to_CKu_isOpenEmbedding :
    Topology.IsOpenEmbedding O.pi1XKu_to_CKu :=
  AG.pi1Cover_isOpenEmbedding O.XKu_to_CKu

end OrbicurveData

end OrbicurveDataSection

end Iut
