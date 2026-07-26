/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.LeftHandSide
import Iut.Cor312.RightHandSide

/-!
# The Corollary 3.12 variant statement (taxis #33)

The capstone of the statement project: a type-correct Lean formulation of the
project-owner-specified **variant of IUT III, Corollary 3.12**, assembled from

* the initial Θ-data of IUT I, Definition 3.1 (taxis #38–#42),
* the `q`-pilot left-hand side `−|log(q)|` (taxis #34),
* the large volume container with its log-volume and holomorphic hull
  (taxis #43–#45), and
* the theta-pilot right-hand side `−|log(Θ)|` (taxis #35),

relative to the anabelian and tempered interfaces (`Iut.AnabelianGeometry`,
`Iut.TemperedGeometry`) and the Tate `q`-parameter stack of taxis #37
(`lana-agents/tate-curves-theta`).

## The statement and its specification boundary

`Iut.Corollary312Variant` is a `Prop`-valued **definition**:

`−|log(q)| ≤ −|log(Θ)|`

for a bundle `Iut.Corollary312VariantData` of Θ-data, `q`-pilot data, and
right-hand-side data. **It is deliberately left without proof and without axioms**: no
declaration in this repository proves, assumes, or axiomatizes it. This is the
visibly marked conjectural/specification boundary required by taxis #33 — proving the
proposition is explicitly out of scope for the project, and the honesty boundary of
this repository (see the README) forbids smuggling it in axiomatically or as a
hypothesis of a "theorem".

## Non-identification with the published Corollary 3.12

This formalization must not be read as Mochizuki's published Corollary 3.12:

* the published statement produces `−|log(Θ)| ∈ ℝ ∪ {+∞}` by a multiradial algorithm
  and asserts `CΘ ≥ −1` for `−|log(Θ)| = CΘ·|log(q)|`; here the theta-pilot region is
  an *input* (`RHSData.thetaPilot`) rather than the output of that algorithm, and the
  value is real by the admissibility hypotheses;
* the container, log-volume, and hull are the interface abstractions of
  taxis #43–#45, whose correspondence with IUT III, Propositions 3.1–3.3 and 3.9 and
  Remark 3.9.5 is documented per-module but not itself a theorem;
* every assumption is a visible field of the input bundle; in particular
  `RHSData.thetaPilot_le_shell` and the hull-admissibility of the theta-pilot region
  are hypotheses, and no disputed implication is encoded as a proved theorem.

The intended statement may differ from the formulation printed in the IUT papers; the
data, hypotheses, definitions and conclusion follow the per-issue specifications of
taxis #33–#45 supplied by the project owner.
-/

namespace Iut

universe u v

/-- The assembled input bundle of the Corollary 3.12 variant (taxis #33): initial
Θ-data with its `q`-pilot data (taxis #34) and right-hand-side data (taxis #35),
relative to the anabelian and tempered interfaces. -/
structure Corollary312VariantData (AG : AnabelianGeometry.{u})
    (TG : TemperedGeometry AG) : Type (max (u + 1) (v + 1)) where
  /-- The initial Θ-data (IUT I, Definition 3.1; taxis #38). -/
  data : InitialThetaData AG TG
  /-- The `q`-pilot data of the left-hand side (taxis #34). -/
  qPilot : QPilotData data
  /-- The container/log-volume/hull/theta-pilot data of the right-hand side
  (taxis #35, #43–#45). -/
  rhsData : RHSData.{u, v} data

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- **The variant of IUT III, Corollary 3.12** (taxis #33):

`−|log(q)| ≤ −|log(Θ)|`

— the `q`-pilot log-volume bounds the procession-normalized log-volume of the
holomorphic hull of the theta-pilot region.

This is a `Prop`-valued *definition*, the conjectural specification boundary of the
project: **no proof of this proposition exists in this repository, and none is
claimed**. See the module docstring for the exact sense in which this statement is
and is not related to the published Corollary 3.12. -/
noncomputable def Corollary312Variant (X : Corollary312VariantData.{u, v} AG TG) :
    Prop :=
  X.qPilot.lhs ≤ X.rhsData.rhs

/-- Unfolding of the variant statement: it is literally the inequality between the
left-hand side of taxis #34 and the right-hand side of taxis #35. -/
lemma corollary312Variant_iff (X : Corollary312VariantData.{u, v} AG TG) :
    Corollary312Variant X ↔ X.qPilot.lhs ≤ X.rhsData.rhs :=
  Iff.rfl

end Iut
