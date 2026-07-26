/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Basic
import Iut.Cor312.ContainerHull
import Iut.Cor312.LogVolume

/-!
# The right-hand side of the Corollary 3.12 variant (taxis #35)

The **theta-pilot side** `−|log(Θ)|` of the project-owner-specified variant of IUT III,
Corollary 3.12 (taxis #33), composing the ingredient interfaces in the order of
IUT III, Corollary 3.12 itself:

1. **initial Θ-data** (taxis #38) supplies the prime `ℓ`, the `ℓ`-torsion field `K`
   and its places;
2. **Tate `q`-parameters** (taxis #37) enter through the Θ-data (they are consumed by
   the left-hand side, taxis #34; the right-hand side shares the same Θ-data);
3. the **large volume container** (taxis #43) is instantiated over the places of `K`
   with the standard procession of length `ℓ* = (ℓ−1)/2`;
4. a **theta-pilot region** — an admissible region of the container for each capsule,
   representing the union of the images of the theta-pilot under the indeterminacies
   `(Ind1)`, `(Ind2)`, `(Ind3)` of IUT III, Theorem 3.11 — enters as *data*: the
   multiradial algorithm that produces it is out of scope for this repository
   (taxis #43), so the region is an explicit input, with its containment in the
   log-shells recorded as an explicit hypothesis (not proved);
5. the **holomorphic hull** (taxis #45) is applied capsule-wise;
6. the **procession-normalized log-volume** (taxis #44) of the hull is the value.

The composed order — container → indeterminacy-closed region → holomorphic hull →
procession-normalized log-volume — is the order of IUT III, Corollary 3.12
(`−|log(Θ)|` is the procession-normalized log-volume of the holomorphic hull of the
union of theta-pilot images). The ingredient list is not treated as a proof, and
nothing here asserts that the project variant is literally identical to the printed
IUT formulation.

## Compatibility fields

The container is tied to the Θ-data by explicit compatibility fields: the procession
is the standard one of length `ℓ*`, and the place map of the container matches the
places of `K` (by residue characteristic at finite places, and sending infinite places
to the archimedean rational place). Each is a visible assumption, never silently
assumed.
-/

namespace Iut

universe u v

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The **right-hand-side input data** of the Corollary 3.12 variant (taxis #35): a
large volume container over the places of the `ℓ`-torsion field with the standard
procession of length `ℓ* = (ℓ−1)/2`, log-volume data, a holomorphic hull system, and
the theta-pilot region (with indeterminacies) as explicit data. See the module
docstring for the composition order and the honesty boundary. -/
structure RHSData (D : InitialThetaData AG TG) : Type (max u (v + 1)) where
  /-- The large volume container (taxis #43), indexed by the places of `K`. -/
  container : LargeVolumeContainerData.{0, u, v} ℕ (Place ↥D.prime.torsionField)
  /-- The procession is the standard one with `ℓ* = (ℓ − 1)/2` capsules
  (IUT III, Propositions 3.1–3.3). -/
  proc_standard : container.proc = Procession.standard ((D.ℓ - 1) / 2)
  /-- Compatibility at finite places: the container's rational-place map matches the
  residue characteristic. -/
  toRational_finite : ∀ w : FinitePlace ↥D.prime.torsionField,
    (container.toRational (Place.finite w)).residueChar = residueChar w
  /-- Compatibility at infinite places: infinite places lie over the archimedean
  rational place. -/
  toRational_infinite : ∀ w : InfinitePlace ↥D.prime.torsionField,
    container.toRational (Place.infinite w) = RationalPlace.infinite
  /-- The log-volume data on the container (taxis #44). -/
  vol : LogVolumeData container
  /-- The holomorphic hull system on the container (taxis #45). -/
  hull : ContainerHullSystem container
  /-- The **theta-pilot region**: for each capsule of the procession, the admissible
  region representing the union of the images of the theta-pilot object under the
  indeterminacies `(Ind1)`–`(Ind3)` (IUT III, Theorem 3.11 / Corollary 3.12). Data:
  the multiradial algorithm producing it is out of scope (taxis #43). -/
  thetaPilot : ∀ i, container.AdmissibleRegion i
  /-- The theta-pilot regions are admissible for the hull system (relative
  compactness and the finite-log-volume hypotheses live in the hull system's
  admissible class; explicit, per taxis #45). -/
  thetaPilot_hullAdmissible : ∀ i, hull.IsAdmissible (thetaPilot i)
  /-- Explicit hypothesis (not a theorem of this repository): the theta-pilot region
  is contained in the mono-analytic log-shells, placewise (IUT III,
  Proposition 3.9/Theorem 3.11 territory; recorded as a visible assumption). -/
  thetaPilot_le_shell : ∀ i, thetaPilot i ≤ container.logShellAdmissible i

namespace RHSData

variable {D : InitialThetaData AG TG} (R : RHSData.{u, v} D)

/-- The holomorphic hull of the theta-pilot region, capsule-wise (taxis #45). -/
noncomputable def thetaHull : ∀ i, R.container.AdmissibleRegion i :=
  R.hull.hullFamily R.thetaPilot

/-- **The right-hand side of the Corollary 3.12 variant** (taxis #35): the
procession-normalized log-volume of the holomorphic hull of the theta-pilot region —
the quantity `−|log(Θ)|` of IUT III, Corollary 3.12, in the interface of this
repository. A real number, in the ordered ambient type shared with the left-hand side
(taxis #34). No disputed equality or inequality is asserted. -/
noncomputable def rhs : ℝ := R.vol.processionVol R.thetaHull

end RHSData

end Iut
