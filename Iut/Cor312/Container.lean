/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.Procession
import Iut.Cor312.RationalPlace
import Iut.Cor312.PacketPresentation

/-!
# The large volume container (taxis #43)

The **large volume container** of the Corollary 3.12 variant (taxis #33) is the
project's name for the combination of

1. the combinatorics of processions and capsules with their label sets `S_{j+1}`
   (IUT I, §§4–6; `Iut.Procession`), and
2. the local and global tensor-packets of log-shells
   (IUT III, Propositions 3.1–3.3 and 3.9; Hoshi, *Introduction to inter-universal
   Teichmüller theory (continued)*, §13).

"Large volume container" is project terminology, not the name of a single definition in
IUT III; this module documents exactly how the Lean abstraction corresponds to the
processions, tensor-packets and integral structures of the papers.

## Correspondence with IUT III, Propositions 3.1–3.3

For a capsule `S` of the procession and a rational place `v_Q`, the tensor-packet of
IUT III, Propositions 3.1–3.2 is the tensor product over the labels `j ∈ S` of the
direct sums `⊕_{v ∣ v_Q} log(F_v)` of local fields lying over `v_Q`. Expanding the
tensor product over the direct sums, the packet decomposes as a direct sum indexed by
the **tuples of places** `(v_j)_{j ∈ S}` with `v_j ∣ v_Q`, each summand a tensor
product of local fields presented as a direct sum of fields. Accordingly:

* the component index of the packet presentation at `(i, v_Q)` is *literally* the type
  `(capsule i).LabelType → fiber v_Q` of such tuples (`LargeVolumeContainerData.packet`),
  so the API retains both the `v_Q`-level direct-sum decomposition over `v ∣ v_Q` and
  the procession labels — replacing this by an unindexed product over `v ∈ V` would
  lose data used by the indeterminacies and by the log-volume (taxis #43, #44);
* the mono-analytic log-shell integral structures placed inside the packets
  (IUT III, Proposition 3.2) appear as the regions `logShell`, product regions which
  are relatively compact, agree with the holomorphic integral region at all but
  finitely many `v_Q` (only ramified and archimedean places contribute; cf. IUT I,
  Definition 5.4.5), and contain the holomorphic integral region at nonarchimedean
  places;
* nonarchimedean and archimedean places are treated separately: the index type
  `Iut.RationalPlace` distinguishes them, the containment
  `integral_subset_logShell_nonarch` is imposed only at nonarchimedean places, and the
  archimedean normalization (Hermitian metric, unit ball) is recorded by the
  log-volume interface of taxis #44.

## Honesty boundary

The *construction* of the packet presentations from actual completions of a number
field — direct sums over `v ∣ v_Q`, tensor products over the capsule labels, semisimple
decomposition, and the log-shells themselves via the `p`-adic logarithm — is local-field
infrastructure tracked in taxis #4 (`lana-agents/padic-log-volume`). Here each packet
presentation enters as an explicit structure field; nothing asserts that a theta-pilot
image lies in the container, and no multiradial algorithm is constructed (out of scope
for taxis #43).

## The global container and admissible regions

The global container is the **restricted product** of the packet totals with respect to
the holomorphic integral regions (`LargeVolumeContainerData.Container`), not a naive
infinite product. The class of admissible regions (`AdmissibleRegion`) consists of
families of packet regions equal to the holomorphic integral region for all but
finitely many `v_Q`; direct-product [pre-]regions and Borel regions are distinguished
by the predicates `AdmissibleRegion.IsProductFamily` and `AdmissibleRegion.IsBorelFamily`
(IUT III, Remark 3.9.5(ii)).
-/

open scoped RestrictedProduct

namespace Iut

universe u₁ u₂ v

/-- The data of the **large volume container** (taxis #43): a procession of capsules
with labels in `ι`, a set `V` of places mapped to rational places, and for each capsule
index `i` and rational place `v_Q` a tensor-packet presented as a direct sum of fields
indexed by tuples of places over `v_Q`, with its mono-analytic log-shell region.

See the module docstring for the exact correspondence with IUT III,
Propositions 3.1–3.3, and for the honesty boundary. -/
structure LargeVolumeContainerData (ι : Type u₁) (V : Type u₂) :
    Type (max u₁ u₂ (v + 1)) where
  /-- The procession of capsules; in the intended instantiation, the standard
  procession `Iut.Procession.standard ℓ*` with `ℓ* = (ℓ - 1)/2`. -/
  proc : Procession ι
  /-- The map sending a place `v ∈ V` to the rational place it divides. -/
  toRational : V → RationalPlace
  /-- Finiteness of the fibers `{v ∣ v_Q}` (a finite set for every place of a number
  field), as chosen data. -/
  fiberFintype : ∀ vQ : RationalPlace, Fintype {v : V // toRational v = vQ}
  /-- The tensor-packet at capsule `i` over `v_Q`, presented as a direct sum of fields
  indexed by the tuples of places `(v_j)_{j ∈ S_i}` with `v_j ∣ v_Q`. The component
  index retains the procession labels and the `v_Q`-level place decomposition. -/
  packet : (i : Fin proc.length) → (vQ : RationalPlace) →
    DirectSumPresentation.{max u₂ u₁, v}
      ((proc.capsule i).LabelType → {v : V // toRational v = vQ})
  /-- The mono-analytic log-shell region placed inside the packet
  (IUT III, Proposition 3.2). -/
  logShell : ∀ (i : Fin proc.length) (vQ : RationalPlace), Set (packet i vQ).Total
  /-- Log-shells are direct-product regions: products of the component log-shells. -/
  logShell_isProduct : ∀ i vQ, (packet i vQ).IsProductRegion (logShell i vQ)
  /-- Log-shells are relatively compact (compact subgroup regions at nonarchimedean
  places, bounded balls at archimedean ones). -/
  logShell_relCompact : ∀ i vQ, IsCompact (closure (logShell i vQ))
  /-- The log-shell agrees with the holomorphic integral region at all but finitely
  many rational places: only ramified and archimedean places contribute
  (cf. IUT I, Definition 5.4.5). -/
  logShell_finiteSupport :
    ∀ i, {vQ | logShell i vQ ≠ (packet i vQ).integralRegion}.Finite
  /-- At nonarchimedean places the log-shell contains the holomorphic integral region
  (IUT I, Definition 5.4.5; IUT III, Proposition 1.2). -/
  integral_subset_logShell_nonarch :
    ∀ i (p : Nat.Primes),
      (packet i (.finite p)).integralRegion ⊆ logShell i (.finite p)

namespace LargeVolumeContainerData

variable {ι : Type u₁} {V : Type u₂} (D : LargeVolumeContainerData.{u₁, u₂, v} ι V)

/-- The fiber of `V` over a rational place: the places `v ∣ v_Q`. -/
def Fiber (vQ : RationalPlace) : Type u₂ := {v : V // D.toRational v = vQ}

instance (vQ : RationalPlace) : Fintype (D.Fiber vQ) := D.fiberFintype vQ

/-- The component index of the packet at `(i, v_Q)`: tuples of places over `v_Q`
indexed by the labels of the `i`-th capsule. -/
abbrev Components (i : Fin D.proc.length) (vQ : RationalPlace) : Type max u₁ u₂ :=
  (D.proc.capsule i).LabelType → D.Fiber vQ

noncomputable instance (i : Fin D.proc.length) (vQ : RationalPlace) :
    Fintype (D.Components i vQ) :=
  Fintype.ofFinite _

/-- The **global container** at capsule `i`: the restricted product of the packet
totals with respect to the holomorphic integral regions. This is the
"global/restricted product container, with explicit admissibility or finite-support
conditions rather than a naive infinite product" of taxis #43. -/
abbrev Container (i : Fin D.proc.length) : Type max u₂ u₁ v :=
  Πʳ vQ : RationalPlace, [(D.packet i vQ).Total, (D.packet i vQ).integralRegion]

/-- An **admissible region** of the large volume container at capsule `i`: a family of
packet regions which agrees with the holomorphic integral region at all but finitely
many rational places. The later constructions (log-volume, taxis #44; holomorphic
hull, taxis #45) operate on this class. -/
structure AdmissibleRegion (i : Fin D.proc.length) : Type max u₁ u₂ v where
  /-- The packet region at each rational place. -/
  region : (vQ : RationalPlace) → Set (D.packet i vQ).Total
  /-- Finite support: away from finitely many rational places the region is the
  holomorphic integral region. -/
  finiteSupport : {vQ | region vQ ≠ (D.packet i vQ).integralRegion}.Finite

namespace AdmissibleRegion

variable {D} {i : Fin D.proc.length}

/-- The subset of the global container cut out by an admissible region. -/
def toSet (R : D.AdmissibleRegion i) : Set (D.Container i) :=
  {x | ∀ vQ, x vQ ∈ R.region vQ}

/-- An admissible region is a **direct-product family** if each of its packet regions
is a direct-product [pre-]region (IUT III, Remark 3.9.5(ii)). -/
def IsProductFamily (R : D.AdmissibleRegion i) : Prop :=
  ∀ vQ, (D.packet i vQ).IsProductRegion (R.region vQ)

/-- An admissible region is a **Borel family** if each of its packet regions is Borel
measurable — the class "arbitrary measurable subsets" of taxis #43, as opposed to the
direct-product [pre-]regions. -/
def IsBorelFamily (R : D.AdmissibleRegion i) : Prop :=
  ∀ vQ, (D.packet i vQ).IsBorelRegion (R.region vQ)

/-- Pointwise containment of admissible regions. -/
instance : LE (D.AdmissibleRegion i) :=
  ⟨fun R S => ∀ vQ, R.region vQ ⊆ S.region vQ⟩

lemma le_def {R S : D.AdmissibleRegion i} : R ≤ S ↔ ∀ vQ, R.region vQ ⊆ S.region vQ :=
  Iff.rfl

end AdmissibleRegion

/-- The holomorphic integral structure of the container, as an admissible region. -/
def integralAdmissible (i : Fin D.proc.length) : D.AdmissibleRegion i where
  region vQ := (D.packet i vQ).integralRegion
  finiteSupport := by simp

/-- The mono-analytic log-shell of the container, as an admissible region: this is the
region in which the images of the pilot objects are compared in IUT III,
Proposition 3.9 and Corollary 3.12. -/
def logShellAdmissible (i : Fin D.proc.length) : D.AdmissibleRegion i where
  region vQ := D.logShell i vQ
  finiteSupport := D.logShell_finiteSupport i

@[simp]
lemma logShellAdmissible_region (i : Fin D.proc.length) (vQ : RationalPlace) :
    (D.logShellAdmissible i).region vQ = D.logShell i vQ := rfl

lemma isProductFamily_logShellAdmissible (i : Fin D.proc.length) :
    (D.logShellAdmissible i).IsProductFamily :=
  fun vQ => D.logShell_isProduct i vQ

end LargeVolumeContainerData

end Iut
