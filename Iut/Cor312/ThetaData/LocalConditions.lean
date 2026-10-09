/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Orbicurve
import Iut.Anabelian.Local

/-!
# Initial Θ-data: valuation section and local conditions (taxis #42)

The valuation-indexed local portion of initial Θ-data, IUT I, Definition 3.1(e) and the
local part of (f), for the Corollary 3.12 variant statement (taxis #33).

## Contents

* The `ℓ`-torsion field `K` is finite over `F` — **proved** from openness of the kernel
  of the mod-`ℓ` representation (`AdmissiblePrimeData.finiteDimensional_torsionField`),
  giving `K` its `NumberField` instance.
* `Iut.ValuationSection`: a section `V ⊆ V(K)` of the restriction `V(K) → V_mod`,
  given by place-type-preserving maps on finite and infinite places, each lying over
  its base point; with the derived subsets `V^non`, `V^arc`, `V^good`, `V^bad`.
* The local anabelian objects: the tempered fundamental groups `Orbicurve.temperedPi1` of
  the model orbicurves with their continuous comparison `Orbicurve.tempToEtale` to the
  genuine étale fundamental groups (`Iut.Anabelian.Tempered`), the Tate structures
  `Iut.TateStructure`, the type `(1, ℤ/ℓℤ)^±`, the theta-root model predicate and the
  canonical graph-quotient cusp (`Iut.Anabelian.Local`).
* `Iut.LocalThetaData`: the packaged local data and conditions: completions and base
  changes at `v ∈ V`, the cartesian local covering diagrams with their injections of
  fundamental groups (`genuinePi1Cover` of the base-changed covers, open embeddings),
  decomposition groups up to conjugacy, the type `(1, ℤ/ℓℤ)^±`
  and theta-root-model conditions at bad places, the cusp condition for `ε_v`, and the
  `Π_v` convention (tempered at bad places, étale at good places), with the
  tempered-to-étale comparison at the bad places.

## Honesty boundary

The tempered fundamental group is the integral-model construction of
lana-agents/tempered-fundamental-groups (`Orbicurve.temperedPi1`); its identification with
André's tempered fundamental group is proved there (`andreEquiv'`) but not yet applied to the
local models here (see `Iut.Anabelian.Tempered`). The theta-root model
predicate and the canonical graph cusp are the model definitions of `Iut.Anabelian.Local`.
Conditions are structure fields, never postulates. This module states the local conditions;
existence of data satisfying them is `Iut.AdmissiblePrimeData.localThetaData`.

## Source correspondence

IUT I, Definition 3.1(e)–(f), pp. 70–71, including the local covering diagrams;
*The Étale Theta Function*, Definition 2.5 (the natural models obtained by extracting
an `ℓ`-th root of the theta function, and the cusp attached to the canonical generator
`±1` of the graph quotient).
-/

namespace Iut

universe u

open NumberField IsDedekindDomain WeierstrassCurve OrbicurveDataSection Iut.Anabelian

/-! ## Finiteness of the ℓ-torsion field -/

section TorsionFieldFinite

variable {F : Type u} [Field F] [NumberField F] {E : WeierstrassCurve F} [E.IsElliptic]
variable {Fbar : Type u} [Field Fbar] [Algebra F Fbar] [IsAlgClosure F Fbar]
variable {VBad : Set (FinitePlace ↥(fieldOfModuli F E))}

/-- The `ℓ`-torsion field is a finite extension of `F`: the kernel of the mod-`ℓ`
representation is open, hence so is the fixing subgroup of its fixed field, which by
the infinite Galois correspondence makes the fixed field finite-dimensional. -/
theorem AdmissiblePrimeData.finiteDimensional_torsionField
    (P : AdmissiblePrimeData F E Fbar VBad) :
    FiniteDimensional F ↥P.torsionField := by
  have hle : P.rep.ker ≤ P.torsionField.fixingSubgroup :=
    (IntermediateField.le_iff_le P.rep.ker P.torsionField).mp le_rfl
  have hopen : IsOpen (P.torsionField.fixingSubgroup : Set (Fbar ≃ₐ[F] Fbar)) :=
    Subgroup.isOpen_mono hle P.ker_isOpen
  exact (InfiniteGalois.isOpen_iff_finite P.torsionField).mp hopen

/-- The fixed field of an open subgroup of `Gal(F̄/F)` is a number field. -/
theorem numberField_fixedField_of_isOpen {H : Subgroup (Fbar ≃ₐ[F] Fbar)}
    (hH : IsOpen (H : Set (Fbar ≃ₐ[F] Fbar))) :
    NumberField ↥(IntermediateField.fixedField H) := by
  have hle : H ≤ (IntermediateField.fixedField H).fixingSubgroup :=
    (IntermediateField.le_iff_le H (IntermediateField.fixedField H)).mp le_rfl
  have hopen : IsOpen ((IntermediateField.fixedField H).fixingSubgroup :
      Set (Fbar ≃ₐ[F] Fbar)) := Subgroup.isOpen_mono hle hH
  have : FiniteDimensional F ↥(IntermediateField.fixedField H) :=
    (InfiniteGalois.isOpen_iff_finite _).mp hopen
  have : CharZero ↥(IntermediateField.fixedField H) :=
    charZero_of_injective_algebraMap (algebraMap F ↥(IntermediateField.fixedField H)).injective
  have : IsScalarTower ℚ F ↥(IntermediateField.fixedField H) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ ↥(IntermediateField.fixedField H) :=
    Module.Finite.trans F ↥(IntermediateField.fixedField H)
  exact { }

/-- The `ℓ`-torsion field of a number field is a number field. -/
theorem AdmissiblePrimeData.numberField_torsionField
    (P : AdmissiblePrimeData F E Fbar VBad) :
    NumberField ↥P.torsionField := by
  have : FiniteDimensional F ↥P.torsionField := P.finiteDimensional_torsionField
  have : CharZero ↥P.torsionField :=
    charZero_of_injective_algebraMap (algebraMap F ↥P.torsionField).injective
  have : IsScalarTower ℚ F ↥P.torsionField :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : FiniteDimensional ℚ ↥P.torsionField := Module.Finite.trans F ↥P.torsionField
  exact { }

end TorsionFieldFinite

/-! ## The valuation section and local data -/

section LocalData

variable (F : Type u) [Field F] [NumberField F] (E : WeierstrassCurve F) [E.IsElliptic]
variable (Fbar : Type u) [Field Fbar] [Algebra F Fbar]
variable (VBad : Set (FinitePlace ↥(fieldOfModuli F E)))
variable (P : AdmissiblePrimeData F E Fbar VBad)
variable [NumberField ↥P.torsionField]
variable [Algebra ↥(fieldOfModuli F E) ↥P.torsionField]

/-- A **section** `V ⊆ V(K)` of the restriction map `V(K) → V_mod`
(IUT I, Definition 3.1(e)): a choice, for every place of `F_mod`, of a place of `K` of
the same type (nonarchimedean/archimedean) lying over it. The subset `V ⊆ V(K)` is the
image of the section; `V ≅ V_mod`. The `NumberField` instance on `K` is available via
`AdmissiblePrimeData.numberField_torsionField`, and the algebra `F_mod → K` (the
restriction of the inclusions into `F̄`) is carried as an instance hypothesis. -/
structure ValuationSection : Type u where
  /-- The section on nonarchimedean places. -/
  sectFin : FinitePlace ↥(fieldOfModuli F E) → FinitePlace ↥P.torsionField
  /-- The section on archimedean places. -/
  sectInf : InfinitePlace ↥(fieldOfModuli F E) → InfinitePlace ↥P.torsionField
  /-- Nonarchimedean sections lie over their base points. -/
  sectFin_liesOver : ∀ v, FinitePlace.LiesOver (sectFin v) v
  /-- Archimedean sections lie over their base points. -/
  sectInf_liesOver : ∀ v, (sectInf v).1.LiesOver v.1

namespace ValuationSection

variable {F E Fbar VBad P}
variable (S : ValuationSection F E Fbar VBad P)

/-- The section as a map `V_mod → V(K)`. -/
noncomputable def sect : ModPlace F E → Place ↥P.torsionField
  | Sum.inl v => Place.finite (S.sectFin v)
  | Sum.inr v => Place.infinite (S.sectInf v)

/-- `V^non ⊆ V`: the nonarchimedean part of the section image. -/
noncomputable def Vnon : Set (Place ↥P.torsionField) :=
  Set.range fun v => Place.finite (S.sectFin v)

/-- `V^arc ⊆ V`: the archimedean part of the section image. -/
noncomputable def Varc : Set (Place ↥P.torsionField) :=
  Set.range fun v => Place.infinite (S.sectInf v)

/-- `V ⊆ V(K)`: the image of the section. -/
noncomputable def V : Set (Place ↥P.torsionField) := Set.range S.sect

/-- `V^bad ⊆ V`: the places of the section lying over `V_mod^bad`
(IUT I, Definition 3.1(e)). -/
noncomputable def Vbad : Set (FinitePlace ↥P.torsionField) := S.sectFin '' VBad

/-- `V^good ⊆ V`: the complement of `V^bad` in the section image. -/
noncomputable def Vgood : Set (Place ↥P.torsionField) :=
  Set.range S.sect \ (Place.finite '' S.Vbad)

end ValuationSection

variable {F E Fbar VBad P} in
/-- The base change of an orbicurve over `K` to the completed local field `K_v` at a
finite place `v` of `K`. -/
noncomputable def localize (v : FinitePlace ↥P.torsionField)
    (X : Orbicurve ↥P.torsionField) : Orbicurve (localCompletion v) :=
  X.baseChange (FinitePlace.embedding v.maximalIdeal)

/-- **IUT I, Definition 3.1(e) and the local part of (f)**: the valuation section with
its local completions, covering diagrams, decomposition groups, and the bad-place
conditions, packaged over the orbicurve data of taxis #41. -/
structure LocalThetaData (O : OrbicurveData F E Fbar VBad P) : Type u where
  /-- The valuation section `V ⊆ V(K)`. -/
  sect : ValuationSection F E Fbar VBad P
  /-- The cartesian local covering diagrams (IUT I, Definition 3.1(e)): at every
  finite place `v` of the section, the base change to `K_v` of the global diagram
  remains cartesian. The injections (open immersions) of local fundamental groups are
  `genuinePi1Cover` of the base-changed covers (`genuinePi1Cover_isOpenEmbedding`; see
  `LocalThetaData.pi1Local`). -/
  local_diagram_cartesian : ∀ v : FinitePlace ↥(fieldOfModuli F E),
    Orbicurve.IsCartesianSquare
      (O.XKu_to_XK.baseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal))
      (O.XK_to_CK.baseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal))
      (O.XKu_to_CKu.baseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal))
      (O.CKu_to_CK.baseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal))
  /-- A choice of **decomposition group** `G_v ⊆ Gal(F̄/K)` at every finite place of
  the section (IUT I, Definition 3.1(e); the group is well-defined up to conjugacy,
  and this field is a choice of representative). -/
  decomp : ∀ _ : FinitePlace ↥P.torsionField, Subgroup (Fbar ≃ₐ[↥P.torsionField] Fbar)
  /-- Decomposition groups are closed in the Krull topology. -/
  decomp_isClosed : ∀ v, IsClosed ((decomp v) : Set (Fbar ≃ₐ[↥P.torsionField] Fbar))
  /-- The Tate structure (Tate uniformization of `E` over `K_v`) on the local model `X̲_v`
  at each place of the section over `V_mod^bad` (IUT I, Definition 3.1(f) refers to the
  Tate uniformization; chosen data, pinned by the coordinates of the Tate parametrization
  in `Iut.TateStructure`). -/
  tateX : ∀ v ∈ VBad, TateStructure (localize (sect.sectFin v) O.XKu).E
  /-- The Tate structure on the local model `C̲_v`. -/
  tateC : ∀ v ∈ VBad, TateStructure (localize (sect.sectFin v) O.CKu).E
  /-- At places over `V_mod^bad`, the local model `X̲_v = X̲_K ×_K K_v` is of type
  `(1, ℤ/ℓℤ)^±` (IUT I, Definition 3.1(f); *Étale Theta*, Definition 2.5). -/
  bad_type : ∀ v (hv : v ∈ VBad),
    (localize (sect.sectFin v) O.XKu).IsTypeOneZModPM P.ℓ (tateX v hv)
  /-- At places over `V_mod^bad`, the local model is a natural model obtained by
  extracting an `ℓ`-th root of the theta function (*Étale Theta*, Definition 2.5;
  `Orbicurve.IsThetaRootModel`). -/
  bad_theta_model : ∀ v (hv : v ∈ VBad),
    (localize (sect.sectFin v) O.XKu).IsThetaRootModel P.ℓ (tateX v hv)
  /-- At places over `V_mod^bad`, the base change `ε_v` of the distinguished cusp `ε`
  is the cusp associated to the canonical generator `±1` of the graph quotient
  (IUT I, Definition 3.1(f); *Étale Theta*, Definition 2.5). -/
  epsilon_graph : ∀ v (hv : v ∈ VBad),
    O.CKu.cuspBaseChange (FinitePlace.embedding (sect.sectFin v).maximalIdeal) O.epsilon =
      (localize (sect.sectFin v) O.CKu).canonicalGraphCusp (tateC v hv)

namespace LocalThetaData

variable {F E Fbar VBad P} {O : OrbicurveData F E Fbar VBad P}
variable (L : LocalThetaData F E Fbar VBad P O)

/-- The **convention for `Π_v` at bad places** (IUT I, Definition 3.1(e)/(f)): at
`v ∈ V^bad`, `Π_v` is the **tempered** fundamental group of the local model. -/
noncomputable abbrev PivBad (v : FinitePlace ↥(fieldOfModuli F E)) : Type u :=
  (localize (L.sect.sectFin v) O.XKu).temperedPi1

/-- The **convention for `Π_v` at good places**: at `v ∈ V^good ∩ V^non`, `Π_v` is the
profinite **étale** fundamental group of the local model. -/
noncomputable abbrev PivGood (v : FinitePlace ↥(fieldOfModuli F E)) : Type u :=
  (localize (L.sect.sectFin v) O.XKu).genuinePi1

/-- The **tempered-to-étale comparison at a bad place** (IUT I, Definition 3.1(e)/(f)):
the continuous homomorphism `Π_v → π₁(X̲_v)` from the tempered to the profinite étale
fundamental group of the local model (`Orbicurve.tempToEtale`). -/
noncomputable def PivBadToEtale (v : FinitePlace ↥(fieldOfModuli F E)) :
    L.PivBad v →* (localize (L.sect.sectFin v) O.XKu).genuinePi1 :=
  (localize (L.sect.sectFin v) O.XKu).tempToEtale

lemma continuous_PivBadToEtale (v : FinitePlace ↥(fieldOfModuli F E)) :
    Continuous (L.PivBadToEtale v) :=
  (localize (L.sect.sectFin v) O.XKu).continuous_tempToEtale

/-- The **injection of local fundamental groups** `π₁(X̲_v) → π₁(C̲_v)` induced by the
base change to `K_v` of the covering `X̲_K → C̲_K` (IUT I, Definition 3.1(e)). -/
noncomputable def pi1Local (v : FinitePlace ↥(fieldOfModuli F E)) :
    (localize (L.sect.sectFin v) O.XKu).genuinePi1 →*
      (localize (L.sect.sectFin v) O.CKu).genuinePi1 :=
  genuinePi1Cover (O.XKu_to_CKu.baseChange (FinitePlace.embedding (L.sect.sectFin v).maximalIdeal))

lemma pi1Local_isOpenEmbedding (v : FinitePlace ↥(fieldOfModuli F E)) :
    Topology.IsOpenEmbedding (L.pi1Local v) :=
  genuinePi1Cover_isOpenEmbedding _

end LocalThetaData

end LocalData

end Iut
