/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Components
import Mathlib.CategoryTheory.CatCommSq

/-!
# Non-archimedean constituents of prime-strips and their isomorphisms (MR20 T4, T5)

IUT I, Definition 4.1 (i), (iii), (iv) (l.6363–6450) and Definition 5.2 (i)–(iii) (l.9153–9183) of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`. At `v ∈ V^non`:

* a constituent of a **`D`-prime-strip** is a category `†D_v` which admits an equivalence
  `†D_v ≅ D_v` (`DComp`); of a **`D^⊢`-prime-strip**, a category admitting an equivalence with
  `D^⊢_v` (`DVdashComp`);
* a constituent of an **`F`-prime-strip** is a category `‡C_v` admitting an equivalence
  `‡C_v ≅ C_v`; of an **`F^⊢`-prime-strip**, a split Frobenioid admitting an isomorphism with
  `F^⊢_v = (C^⊢_v, τ^⊢_v)`;
* morphisms of `F`-, `F^⊢`-prime-strips are collections of isomorphisms of the constituents
  (Definition 5.2 (iii)); isomorphisms of categories are (isomorphism classes of) equivalences (§0,
  l.1965).

## Formalisation

* A Frobenioid constituent is recorded **with its base functor** (`FrobCat`: `C ⥤ D`), as in
  [FrdI], Definition 1.3 (a Frobenioid is a category with a functor to `D × F_Φ`), and an
  isomorphism of Frobenioids (`FrobCat.Iso`) is an equivalence `C ≌ C'` with an equivalence of
  base categories `D ≌ D'` and a natural isomorphism making the square commute (`CatCommSq`).
  For the models every equivalence of the categories admits such a base equivalence when the base
  is slim ([FrdI], Theorem 3.4 (v); `Frobenioid.thm34_galois_preservesBase`, MR16), so this is the
  isomorphism notion of Definition 5.2 (iii); recording the base equivalence makes the passage
  `F ↦ D` of Remark 5.2.1 (i) a functor on isomorphisms (`FComp.toD`, `FComp.isoToD`) without the
  slimness of `Π_v` (not available, MR13).
* A split Frobenioid (`SplitFrobCat`) is a `FrobCat` with a family `τ(A) ⊆ End(A)` (the
  characteristic splitting as a collection of base-identity linear endomorphisms, [FrdI],
  Definition 2.3; for the models `Model.splitEnd τ`, the endomorphisms with `u ∈ τ(A_D)`); an
  isomorphism of split Frobenioids is an isomorphism of Frobenioids whose functor and inverse
  preserve the splittings.
* The **strip conditions** "`†D_v` admits an equivalence with `D_v`" etc. are the `Prop` fields
  `equiv_model` (defining conditions of the paper, not shells).
* **The strips are the non-archimedean parts** (`DStripNon` etc., indexed by the finite places of
  `F_mod`, i.e. `V^non` through the section): the archimedean constituents (Aut-holomorphic
  orbispaces, the angular-region Frobenioid with its Kummer structure, objects of `TM^⊢`) are MR20
  T3-arc (not done; see `MR20-plan.md`).
* **The tautological strips** `DStripNon.ofThetaData D` etc. (IUT I, Example 4.3 (iv)) have the
  models as constituents; **the structure functors** of Remark 5.2.1 (i): `F ↦ D`
  (`FStripNon.toD`), `F^⊢ ↦ D^⊢` (`FVdashStripNon.toD`), functorial on isomorphisms.
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

universe u

/-! ### Frobenioids with base functor, and their isomorphisms -/

/-- **A Frobenioid with its base functor** `C ⥤ D` ([FrdI], Definition 1.3). -/
structure FrobCat : Type 1 where
  /-- The Frobenioid (a category). -/
  C : Cat.{0, 0}
  /-- The base category. -/
  D : Cat.{0, 0}
  /-- The base functor. -/
  base : C ⥤ D

namespace FrobCat

/-- **An isomorphism of Frobenioids**: equivalences of the Frobenioids and of the bases,
compatible with the base functors. -/
structure Iso (X Y : FrobCat) where
  /-- The equivalence of Frobenioids. -/
  C : X.C ≌ Y.C
  /-- The equivalence of base categories. -/
  D : X.D ≌ Y.D
  /-- Compatibility with the base functors: `C ⋙ base' ≅ base ⋙ D`. -/
  comm : CatCommSq C.functor X.base Y.base D.functor

namespace Iso

/-- The identity. -/
def refl (X : FrobCat) : X.Iso X where
  C := CategoryTheory.Equivalence.refl
  D := CategoryTheory.Equivalence.refl
  comm := CatCommSq.hId X.base

/-- The inverse. -/
def symm {X Y : FrobCat} (f : X.Iso Y) : Y.Iso X where
  C := f.C.symm
  D := f.D.symm
  comm := CatCommSq.hInv f.C X.base Y.base f.D f.comm

/-- The composite. -/
def trans {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z where
  C := f.C.trans g.C
  D := f.D.trans g.D
  comm := CatCommSq.hComp' f.comm g.comm

end Iso

/-- The Frobenioid with base of a model Frobenioid `P : C ⥤ F_Φ`. -/
def ofModel {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} (C : Type) [Category.{0} C]
    (P : C ⥤ Elem Φ) : FrobCat where
  C := Cat.of C
  D := Cat.of D
  base := P ⋙ Elem.proj

end FrobCat

/-- **A split Frobenioid** ([FrdI], Definition 2.3; IUT I, Example 3.2 (iv)): a Frobenioid with
a characteristic splitting, recorded by the endomorphisms `τ(A) ⊆ O^▷(A) ⊆ End(A)`. -/
structure SplitFrobCat : Type 1 where
  /-- The Frobenioid. -/
  F : FrobCat
  /-- The splitting. -/
  tau : ∀ A : F.C, Set (A ⟶ A)

namespace SplitFrobCat

/-- **An isomorphism of split Frobenioids**: an isomorphism of Frobenioids whose functor and
inverse preserve the splittings. -/
structure Iso (X Y : SplitFrobCat) where
  /-- The isomorphism of Frobenioids. -/
  iso : X.F.Iso Y.F
  /-- The functor preserves the splittings. -/
  map_tau : ∀ (A : X.F.C) (e : A ⟶ A), e ∈ X.tau A →
    iso.C.functor.map e ∈ Y.tau (iso.C.functor.obj A)
  /-- The inverse preserves the splittings. -/
  inv_tau : ∀ (B : Y.F.C) (e : B ⟶ B), e ∈ Y.tau B →
    iso.C.inverse.map e ∈ X.tau (iso.C.inverse.obj B)

namespace Iso

/-- The identity. -/
def refl (X : SplitFrobCat) : X.Iso X := ⟨FrobCat.Iso.refl _, fun _ _ h => h, fun _ _ h => h⟩

/-- The inverse. -/
def symm {X Y : SplitFrobCat} (f : X.Iso Y) : Y.Iso X := ⟨f.iso.symm, f.inv_tau, f.map_tau⟩

/-- The composite. -/
def trans {X Y Z : SplitFrobCat} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z :=
  ⟨f.iso.trans g.iso, fun _ _ h => g.map_tau _ _ (f.map_tau _ _ h),
    fun _ _ h => f.inv_tau _ _ (g.inv_tau _ _ h)⟩

end Iso

end SplitFrobCat

/-- **The splitting of a model Frobenioid as endomorphisms**: the base-identity linear
endomorphisms `e` of `X` whose rational function `u_e` lies in `τ(X_D)`
(`Model.orhdEquivSub`: `O^▷(X) ≅ {b ∈ B(X_D) : Div_B(b) ≥ 0}`). -/
def Model.splitEnd {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} {B : GrpOn.{0} D}
    {divB : DivHom B Φ.toGrpOn} (τ : ∀ A : D, AddSubmonoid (B.obj A)) (X : Model Φ B divB) :
    Set (X ⟶ X) :=
  {e | ∃ h : e ∈ Orhd (Model.toElem Φ B divB) X,
    ((Model.orhdEquivSub X ⟨e, h⟩ : Model.orhdSub divB X.base) : B.obj X.base) ∈ τ X.base}

/-! ### The models at `v ∈ V^non` -/

section Models

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`C_v` with its base `D_v`**. -/
def cvFrob : FrobCat := FrobCat.ofModel (Cv D v) (cvElem D v)

/-- **`C^⊢_v` with its base `D^⊢_v`**. -/
def cvdFrob : FrobCat := FrobCat.ofModel (CVdash D v) (cvdElem D v)

/-- **`F^⊢_v = (C^⊢_v, τ^⊢_v)`** (IUT I, Examples 3.2 (iv), 3.3 (i)). -/
def fVdashModel : SplitFrobCat where
  F := cvdFrob D v
  tau := Model.splitEnd (tauVdash D v)

end Models

/-! ### The constituents -/

section Comps

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **A constituent `†D_v` of a `D`-prime-strip** at `v ∈ V^non` (IUT I, Definition 4.1 (i)(a)):
a category admitting an equivalence with `D_v`. -/
structure DComp : Type 1 where
  /-- The category `†D_v`. -/
  C : Cat.{0, 0}
  /-- It admits an equivalence with `D_v`. -/
  equiv_model : Nonempty (C ≌ Dv D v)

/-- **A constituent `†D^⊢_v` of a `D^⊢`-prime-strip** at `v ∈ V^non` (IUT I, Definition 4.1
(iii)(a)). -/
structure DVdashComp : Type 1 where
  /-- The category `†D^⊢_v`. -/
  C : Cat.{0, 0}
  /-- It admits an equivalence with `D^⊢_v`. -/
  equiv_model : Nonempty (C ≌ DVdash D v)

/-- **A constituent `‡F_v` of an `F`-prime-strip** at `v ∈ V^non` (IUT I, Definition 5.2 (i)(a)):
a Frobenioid isomorphic to `C_v`. -/
structure FComp : Type 1 where
  /-- The Frobenioid `‡C_v` with its base. -/
  F : FrobCat
  /-- It is isomorphic to `C_v`. -/
  equiv_model : Nonempty (F.Iso (cvFrob D v))

/-- **A constituent `‡F^⊢_v` of an `F^⊢`-prime-strip** at `v ∈ V^non` (IUT I, Definition 5.2
(ii)(a)): a split Frobenioid isomorphic to `F^⊢_v`. -/
structure FVdashComp : Type 1 where
  /-- The split Frobenioid `‡F^⊢_v`. -/
  F : SplitFrobCat
  /-- It is isomorphic to `F^⊢_v`. -/
  equiv_model : Nonempty (F.Iso (fVdashModel D v))

variable {D v}

/-- **`F ↦ D`** on constituents (IUT I, Remark 5.2.1 (i)): the base category. -/
def FComp.toD (X : FComp D v) : DComp D v :=
  ⟨X.F.D, X.equiv_model.map fun f => f.D⟩

/-- `F ↦ D` on isomorphisms. -/
def FComp.isoToD {X Y : FComp D v} (f : X.F.Iso Y.F) : X.toD.C ≌ Y.toD.C := f.D

/-- **`F^⊢ ↦ D^⊢`** on constituents (IUT I, Remark 5.2.1 (i)): the base category. -/
def FVdashComp.toD (X : FVdashComp D v) : DVdashComp D v :=
  ⟨X.F.F.D, X.equiv_model.map fun f => f.iso.D⟩

/-- `F^⊢ ↦ D^⊢` on isomorphisms. -/
def FVdashComp.isoToD {X Y : FVdashComp D v} (f : X.F.Iso Y.F) : X.toD.C ≌ Y.toD.C := f.iso.D

end Comps

/-! ### Prime-strips (non-archimedean parts) -/

section Strips

variable (D : InitialThetaData.{0})

/-- The index set `V^non ≅ V_mod^non` (the finite places of `F_mod`; IUT I, Definition 3.1 (e)). -/
abbrev Vnon : Type := FinitePlace ↥(fieldOfModuli D.F D.E)

/-- **The non-archimedean part of a `D`-prime-strip** (IUT I, Definition 4.1 (i)). -/
structure DStripNon : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, DComp D v

/-- **The non-archimedean part of a `D^⊢`-prime-strip** (IUT I, Definition 4.1 (iii)). -/
structure DVdashStripNon : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, DVdashComp D v

/-- **The non-archimedean part of an `F`-prime-strip** (IUT I, Definition 5.2 (i)). -/
structure FStripNon : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, FComp D v

/-- **The non-archimedean part of an `F^⊢`-prime-strip** (IUT I, Definition 5.2 (ii)). -/
structure FVdashStripNon : Type 1 where
  /-- The constituents. -/
  comp : ∀ v : Vnon D, FVdashComp D v

variable {D}

/-- **Isomorphisms of `D`-prime-strips** (Definition 4.1 (iv)): constituentwise equivalences. -/
def DStripNon.Iso (P Q : DStripNon D) : Type := ∀ v, (P.comp v).C ≌ (Q.comp v).C

/-- **Isomorphisms of `D^⊢`-prime-strips** (Definition 4.1 (iv)). -/
def DVdashStripNon.Iso (P Q : DVdashStripNon D) : Type := ∀ v, (P.comp v).C ≌ (Q.comp v).C

/-- **Isomorphisms of `F`-prime-strips** (Definition 5.2 (iii)): constituentwise isomorphisms of
Frobenioids. -/
def FStripNon.Iso (P Q : FStripNon D) : Type := ∀ v, (P.comp v).F.Iso (Q.comp v).F

/-- **Isomorphisms of `F^⊢`-prime-strips** (Definition 5.2 (iii)). -/
def FVdashStripNon.Iso (P Q : FVdashStripNon D) : Type := ∀ v, (P.comp v).F.Iso (Q.comp v).F

namespace FStripNon

/-- The identity. -/
def Iso.refl (P : FStripNon D) : P.Iso P := fun _ => FrobCat.Iso.refl _

/-- The inverse. -/
def Iso.symm {P Q : FStripNon D} (f : P.Iso Q) : Q.Iso P := fun v => (f v).symm

/-- The composite. -/
def Iso.trans {P Q R : FStripNon D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  fun v => (f v).trans (g v)

/-- **`F ↦ D`** (IUT I, Remark 5.2.1 (i)). -/
def toD (P : FStripNon D) : DStripNon D := ⟨fun v => (P.comp v).toD⟩

/-- `F ↦ D` on isomorphisms. -/
def isoToD {P Q : FStripNon D} (f : P.Iso Q) : P.toD.Iso Q.toD := fun v => (f v).D

lemma isoToD_trans {P Q R : FStripNon D} (f : P.Iso Q) (g : Q.Iso R) (v : Vnon D) :
    isoToD (Iso.trans f g) v = (isoToD f v).trans (isoToD g v) := rfl

lemma isoToD_symm {P Q : FStripNon D} (f : P.Iso Q) (v : Vnon D) :
    isoToD (Iso.symm f) v = (isoToD f v).symm := rfl

end FStripNon

namespace FVdashStripNon

/-- The identity. -/
def Iso.refl (P : FVdashStripNon D) : P.Iso P := fun _ => SplitFrobCat.Iso.refl _

/-- The inverse. -/
def Iso.symm {P Q : FVdashStripNon D} (f : P.Iso Q) : Q.Iso P := fun v => (f v).symm

/-- The composite. -/
def Iso.trans {P Q R : FVdashStripNon D} (f : P.Iso Q) (g : Q.Iso R) : P.Iso R :=
  fun v => (f v).trans (g v)

/-- **`F^⊢ ↦ D^⊢`** (IUT I, Remark 5.2.1 (i)). -/
def toD (P : FVdashStripNon D) : DVdashStripNon D := ⟨fun v => (P.comp v).toD⟩

/-- `F^⊢ ↦ D^⊢` on isomorphisms. -/
def isoToD {P Q : FVdashStripNon D} (f : P.Iso Q) : P.toD.Iso Q.toD := fun v => (f v).iso.D

end FVdashStripNon

variable (D)

/-- **The tautological `D`-prime-strip** `{D_v}` (IUT I, Example 4.3 (iv)), non-archimedean
part. -/
def DStripNon.ofThetaData : DStripNon D :=
  ⟨fun v => ⟨Cat.of (Dv D v), ⟨CategoryTheory.Equivalence.refl⟩⟩⟩

/-- **The tautological `D^⊢`-prime-strip** `{D^⊢_v}`, non-archimedean part. -/
def DVdashStripNon.ofThetaData : DVdashStripNon D :=
  ⟨fun v => ⟨Cat.of (DVdash D v), ⟨CategoryTheory.Equivalence.refl⟩⟩⟩

/-- **The tautological `F`-prime-strip** `{C_v}`, non-archimedean part. -/
def FStripNon.ofThetaData : FStripNon D := ⟨fun v => ⟨cvFrob D v, ⟨FrobCat.Iso.refl _⟩⟩⟩

/-- **The tautological `F^⊢`-prime-strip** `{F^⊢_v}`, non-archimedean part. -/
def FVdashStripNon.ofThetaData : FVdashStripNon D :=
  ⟨fun v => ⟨fVdashModel D v, ⟨SplitFrobCat.Iso.refl _⟩⟩⟩

/-- The `D`-prime-strip of the tautological `F`-prime-strip is the tautological one. -/
theorem FStripNon.toD_ofThetaData (v : Vnon D) :
    ((FStripNon.ofThetaData D).toD.comp v).C = ((DStripNon.ofThetaData D).comp v).C := rfl

end Strips

end PrimeStrip

end Multiradial

end Iut
