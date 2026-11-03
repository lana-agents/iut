/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Arc
import Iut.Multiradial.PrimeStrip.Mu

/-!
# Prime-strips indexed by all of `V` (MR20 T4, T5, T7)

IUT I, Definition 4.1 (i), (iii), (iv) (l.6363–6450), Definition 5.2 (i)–(iii) (l.9153–9183),
Remark 5.2.1 (i) (l.9821–9850); IUT II, Definition 4.9 (v)–(vii) (l.11829–11900) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory {I,II}.txt`.

`V ≅ V_mod` is the disjoint union of the finite places `Vnon D` and the infinite places
`Varc D` of `F_mod` (IUT I, Definition 3.1 (e)). A prime-strip is its non-archimedean part
(`Strip.lean`, `Mu.lean`) together with the archimedean constituents (`Arc.lean`):

* `DStrip`, `DVdashStrip`, `FStrip`, `FVdashStrip`, `FMuStrip` with their isomorphisms
  (constituentwise isomorphisms; Definitions 4.1 (iv), 5.2 (iii); IUT II, Definition 4.9 (vii)),
  identities, inverses, composites, `nonempty_iso` (any two are isomorphic, through the models);
* the tautological strips `ofThetaData` (IUT I, Example 4.3 (iv));
* `F ↦ D`, `F^⊢ ↦ D^⊢` (Remark 5.2.1 (i)) on strips and isomorphisms.

**`F^{⊢×μ}` at `v ∈ V^arc`** (IUT II, Definition 4.9 (v)): the units `O^×(C_v) ≅ S¹` modulo
torsion, the inductive system of the quotients by the `N`-torsion; the base category is the
one-morphism category, so the group acting is trivial: the model is `{1} ↷ S¹/μ_∞`
(`fmuArcModel`). The `TM^⊢`-object `‡D^⊢_w` with its Kummer-type surjections `(‡D^⊢_w)^× ↠ O^{×μ_N}`
(Definition 4.9 (v)) is not recorded in this `G ↷ M` constituent.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

section Strips

variable (D : InitialThetaData.{0})

/-- The index set `V^arc ≅ V_mod^arc` (the infinite places of `F_mod`). -/
abbrev Varc : Type := InfinitePlace ↥(fieldOfModuli D.F D.E)

/-- **A `D`-prime-strip** (IUT I, Definition 4.1 (i)). -/
structure DStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : DStripNon D
  /-- The constituents at `V^arc`. -/
  arc : Varc D → DArcComp

/-- **A `D^⊢`-prime-strip** (IUT I, Definition 4.1 (iii)). -/
structure DVdashStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : DVdashStripNon D
  /-- The constituents at `V^arc`. -/
  arc : Varc D → DVdashArcComp

/-- **An `F`-prime-strip** (IUT I, Definition 5.2 (i)). -/
structure FStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : FStripNon D
  /-- The constituents at `V^arc`. -/
  arc : Varc D → FArcComp

/-- **An `F^⊢`-prime-strip** (IUT I, Definition 5.2 (ii)). -/
structure FVdashStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : FVdashStripNon D
  /-- The constituents at `V^arc`. -/
  arc : Varc D → FVdashArcComp

variable {D}

/-- **Isomorphisms of `D`-prime-strips** (IUT I, Definition 4.1 (iv)). -/
def DStrip.Iso (P Q : DStrip D) : Type := P.non.Iso Q.non × ∀ v, (P.arc v).S.Iso (Q.arc v).S

/-- **Isomorphisms of `D^⊢`-prime-strips** (IUT I, Definition 4.1 (iv)). -/
def DVdashStrip.Iso (P Q : DVdashStrip D) : Type :=
  P.non.Iso Q.non × ∀ v, (P.arc v).T.Iso (Q.arc v).T

/-- **Isomorphisms of `F`-prime-strips** (IUT I, Definition 5.2 (iii)). -/
def FStrip.Iso (P Q : FStrip D) : Type := P.non.Iso Q.non × ∀ v, (P.arc v).X.Iso (Q.arc v).X

/-- **Isomorphisms of `F^⊢`-prime-strips** (IUT I, Definition 5.2 (iii)). -/
def FVdashStrip.Iso (P Q : FVdashStrip D) : Type :=
  P.non.Iso Q.non × ∀ v, (P.arc v).X.Iso (Q.arc v).X

namespace DStrip

/-- The identity. -/
def Iso.refl (P : DStrip D) : P.Iso P :=
  ⟨fun _ => CategoryTheory.Equivalence.refl, fun _ => EllSp.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : DStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨fun v => (f.1 v).symm, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : DStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨fun v => (f.1 v).trans (g.1 v), fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `D`-prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : DStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non.comp v).equiv_model.some).trans (Q.non.comp v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

end DStrip

namespace DVdashStrip

/-- The identity. -/
def Iso.refl (P : DVdashStrip D) : P.Iso P :=
  ⟨fun _ => CategoryTheory.Equivalence.refl, fun _ => TMVdash.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : DVdashStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨fun v => (f.1 v).symm, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : DVdashStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨fun v => (f.1 v).trans (g.1 v), fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `D^⊢`-prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : DVdashStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non.comp v).equiv_model.some).trans (Q.non.comp v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

end DVdashStrip

namespace FStrip

/-- The identity. -/
def Iso.refl (P : FStrip D) : P.Iso P := ⟨FStripNon.Iso.refl _, fun _ => FArcData.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : FStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨FStripNon.Iso.symm f.1, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : FStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨FStripNon.Iso.trans f.1 g.1, fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `F`-prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : FStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non.comp v).equiv_model.some).trans (Q.non.comp v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

/-- **`F ↦ D`** (IUT I, Remark 5.2.1 (i)). -/
def toD (P : FStrip D) : DStrip D := ⟨P.non.toD, fun v => (P.arc v).toD⟩

/-- `F ↦ D` on isomorphisms. -/
def isoToD {P Q : FStrip D} (f : P.Iso Q) : P.toD.Iso Q.toD :=
  ⟨FStripNon.isoToD f.1, fun v => (f.2 v).S⟩

end FStrip

namespace FVdashStrip

/-- The identity. -/
def Iso.refl (P : FVdashStrip D) : P.Iso P :=
  ⟨FVdashStripNon.Iso.refl _, fun _ => FVdashArcData.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : FVdashStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨FVdashStripNon.Iso.symm f.1, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : FVdashStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨FVdashStripNon.Iso.trans f.1 g.1, fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `F^⊢`-prime-strips are isomorphic.** -/
theorem nonempty_iso (P Q : FVdashStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non.comp v).equiv_model.some).trans (Q.non.comp v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

/-- **`F^⊢ ↦ D^⊢`** (IUT I, Remark 5.2.1 (i)). -/
def toD (P : FVdashStrip D) : DVdashStrip D := ⟨P.non.toD, fun v => (P.arc v).toD⟩

/-- `F^⊢ ↦ D^⊢` on isomorphisms. -/
def isoToD {P Q : FVdashStrip D} (f : P.Iso Q) : P.toD.Iso Q.toD :=
  ⟨FVdashStripNon.isoToD f.1, fun v => (f.2 v).T⟩

end FVdashStrip

variable (D)

/-- **The tautological `D`-prime-strip** (IUT I, Example 4.3 (iv)). -/
def DStrip.ofThetaData : DStrip D :=
  ⟨DStripNon.ofThetaData D, fun _ => ⟨ellModel, ⟨EllSp.Iso.refl _⟩⟩⟩

/-- **The tautological `D^⊢`-prime-strip**. -/
def DVdashStrip.ofThetaData : DVdashStrip D :=
  ⟨DVdashStripNon.ofThetaData D, fun _ => ⟨tmModel, ⟨TMVdash.Iso.refl _⟩⟩⟩

/-- **The tautological `F`-prime-strip** `{F_v}` (IUT I, Examples 3.2–3.4). -/
def FStrip.ofThetaData : FStrip D :=
  ⟨FStripNon.ofThetaData D, fun _ => ⟨fArcModel, ⟨FArcData.Iso.refl _⟩⟩⟩

/-- **The tautological `F^⊢`-prime-strip** `{F^⊢_v}`. -/
def FVdashStrip.ofThetaData : FVdashStrip D :=
  ⟨FVdashStripNon.ofThetaData D, fun _ => ⟨fVdashArcModel, ⟨FVdashArcData.Iso.refl _⟩⟩⟩

end Strips

/-! ### `F^{⊢×μ}`-prime-strips -/

section Mu

/-- **`O^{×μ}_ℂ = S¹/μ_∞`** (IUT II, Definition 4.9 (v): the units `O^×(C_v) ≅ S¹` of the
archimedean Frobenioid modulo torsion). -/
abbrev OxMuArc : Type := Circle ⧸ CommGroup.torsion Circle

/-- The trivial group acts trivially. -/
instance : MulDistribMulAction PUnit OxMuArc where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_mul _ _ _ := rfl
  smul_one _ := rfl

/-- **The model `{1} ↷ O^{×μ}_ℂ`** at `v ∈ V^arc` (the base category of `C_v` is the
one-morphism category). -/
def fmuArcModel : GMObj := ⟨PUnit, OxMuArc⟩

/-- **A constituent of an `F^{⊢×μ}`-prime-strip** at `v ∈ V^arc` (IUT II, Definition 4.9 (vii)). -/
structure FMuArcComp : Type 1 where
  /-- The `G ↷ O^{×μ}` data. -/
  X : GMObj
  /-- It is isomorphic to the model. -/
  equiv_model : Nonempty (X.Iso fmuArcModel)

variable (D : InitialThetaData.{0})

/-- **An `F^{⊢×μ}`-prime-strip** (IUT II, Definition 4.9 (vii)). -/
structure FMuStrip : Type 1 where
  /-- The constituents at `V^non`. -/
  non : FMuStripNon D
  /-- The constituents at `V^arc`. -/
  arc : Varc D → FMuArcComp

variable {D}

/-- **Isomorphisms of `F^{⊢×μ}`-prime-strips** (constituentwise). -/
def FMuStrip.Iso (P Q : FMuStrip D) : Type := P.non.Iso Q.non × ∀ v, (P.arc v).X.Iso (Q.arc v).X

namespace FMuStrip

/-- The identity. -/
def Iso.refl (P : FMuStrip D) : P.Iso P :=
  ⟨fun _ => GMObj.Iso.refl _, fun _ => GMObj.Iso.refl _⟩

/-- The inverse. -/
def Iso.symm {P Q : FMuStrip D} (f : P.Iso Q) : Q.Iso P :=
  ⟨fun v => (f.1 v).symm, fun v => (f.2 v).symm⟩

/-- The composite. -/
def Iso.trans {P Q R : FMuStrip D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  ⟨fun v => (f.1 v).trans (g.1 v), fun v => (f.2 v).trans (g.2 v)⟩

/-- **Any two `F^{⊢×μ}`-prime-strips are isomorphic** (through the models). -/
theorem nonempty_iso (P Q : FMuStrip D) : Nonempty (P.Iso Q) :=
  ⟨⟨fun v => ((P.non.comp v).equiv_model.some).trans (Q.non.comp v).equiv_model.some.symm,
    fun v => ((P.arc v).equiv_model.some).trans (Q.arc v).equiv_model.some.symm⟩⟩

variable (D)

/-- **The tautological `F^{⊢×μ}`-prime-strip**. -/
def ofThetaData : FMuStrip D :=
  ⟨FMuStripNon.ofThetaData D, fun _ => ⟨fmuArcModel, ⟨GMObj.Iso.refl _⟩⟩⟩

end FMuStrip

end Mu

end PrimeStrip

end Multiradial

end Iut
