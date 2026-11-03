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

* A Frobenioid constituent is recorded **with its base category, divisor monoid and structure
  functor** (`FrobCat`: `P : C ⥤ F_Φ` over `D`), as in [FrdI], Definition 1.3 (a Frobenioid is a
  category with a functor to `D × F_Φ`), and an isomorphism of Frobenioids (`FrobCat.Iso`) is an
  equivalence `C ≌ C'` with an equivalence of base categories `D ≌ D'` and isomorphisms of the
  divisor monoids `Φ(A) ≅ Φ'(A')` (both directions) compatible with the pull-backs, such that
  the structure functors commute up to natural isomorphism with the induced functor of
  elementary Frobenioids `F_Φ ⥤ F_{Φ'}` (`elemMap`, `(f, Z, n) ↦ (D(f), φ(Z), n)`; a
  `CatCommSq` for the functor and one for the inverse). The square of base functors
  (`FrobCat.Iso.comm`) follows. The `Φ`-isomorphisms are what the isomorphisms `ρ_v` of
  `F^⊩`-prime-strips are compared through (IUT I, Definition 5.2 (iv)).
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

/-- **A Frobenioid with its base category, divisor monoid and structure functor**
`P : C ⥤ F_Φ` ([FrdI], Definition 1.3: a Frobenioid is a category with a functor to
`D × F_Φ`, recorded through `F_Φ = Elem Φ`, whose objects lie over `D`). -/
structure FrobCat : Type 1 where
  /-- The Frobenioid (a category). -/
  C : Cat.{0, 0}
  /-- The base category. -/
  D : Cat.{0, 0}
  /-- The divisor monoid `Φ` on the base. -/
  Φ : DivMonoid.{0} D
  /-- The structure functor `C ⥤ F_Φ`. -/
  P : C ⥤ Elem Φ

namespace FrobCat

/-- The base functor `C ⥤ D`. -/
def base (X : FrobCat) : X.C ⥤ X.D := X.P ⋙ Elem.proj

/-- **The functor `F_Φ ⥤ F_Ψ` induced by a functor of bases** `E : D ⥤ D'` and isomorphisms
`φ_A : Φ^gp(A) ≅ Ψ^gp(E(A))` preserving the effective parts and compatible with the pull-backs:
`(f, Z_f, n_f) ↦ (E(f), φ(Z_f), n_f)`. -/
def elemMap {D₁ D₂ : Type} [Category.{0} D₁] [Category.{0} D₂] {Φ : DivMonoid.{0} D₁}
    {Ψ : DivMonoid.{0} D₂} (E : D₁ ⥤ D₂) (φ : ∀ A, Φ.obj A ≃+ Ψ.obj (E.obj A))
    (hpos : ∀ A x, x ∈ Φ.pos A ↔ φ A x ∈ Ψ.pos (E.obj A))
    (hpb : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ A (Φ.pb g x) = Ψ.pb (E.map g) (φ B x)) :
    Elem Φ ⥤ Elem Ψ where
  obj A := ⟨E.obj A.base⟩
  map f := ⟨E.map f.base, φ _ f.div, (hpos _ _).mp f.div_mem, f.deg⟩
  map_id A := Elem.hom_ext (E.map_id _) (map_zero _) rfl
  map_comp f g := Elem.hom_ext (E.map_comp _ _)
    (by simp only [Elem.comp_div, map_add, map_nsmul, hpb]) rfl

/-- `elemMap` lies over `E`: `elemMap ⋙ proj = proj ⋙ E`. -/
def elemMapProj {D₁ D₂ : Type} [Category.{0} D₁] [Category.{0} D₂] {Φ : DivMonoid.{0} D₁}
    {Ψ : DivMonoid.{0} D₂} (E : D₁ ⥤ D₂) (φ : ∀ A, Φ.obj A ≃+ Ψ.obj (E.obj A))
    (hpos : ∀ A x, x ∈ Φ.pos A ↔ φ A x ∈ Ψ.pos (E.obj A))
    (hpb : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ A (Φ.pb g x) = Ψ.pb (E.map g) (φ B x)) :
    elemMap E φ hpos hpb ⋙ Elem.proj ≅ Elem.proj ⋙ E :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `elemMap` of the identity is the identity. -/
def elemMapId {D₁ : Type} [Category.{0} D₁] (Φ : DivMonoid.{0} D₁) :
    𝟭 (Elem Φ) ≅ elemMap (𝟭 D₁) (fun A => AddEquiv.refl (Φ.obj A)) (fun _ _ => Iff.rfl)
      (fun _ _ => rfl) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- `elemMap` of a composite is the composite. -/
def elemMapComp {D₁ D₂ D₃ : Type} [Category.{0} D₁] [Category.{0} D₂] [Category.{0} D₃]
    {Φ : DivMonoid.{0} D₁} {Ψ : DivMonoid.{0} D₂} {Χ : DivMonoid.{0} D₃} (E : D₁ ⥤ D₂)
    (E' : D₂ ⥤ D₃) (φ : ∀ A, Φ.obj A ≃+ Ψ.obj (E.obj A))
    (hpos : ∀ A x, x ∈ Φ.pos A ↔ φ A x ∈ Ψ.pos (E.obj A))
    (hpb : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ A (Φ.pb g x) = Ψ.pb (E.map g) (φ B x))
    (φ' : ∀ A, Ψ.obj A ≃+ Χ.obj (E'.obj A))
    (hpos' : ∀ A x, x ∈ Ψ.pos A ↔ φ' A x ∈ Χ.pos (E'.obj A))
    (hpb' : ∀ {A B : D₂} (g : A ⟶ B) (x : Ψ.obj B), φ' A (Ψ.pb g x) = Χ.pb (E'.map g) (φ' B x)) :
    elemMap E φ hpos hpb ⋙ elemMap E' φ' hpos' hpb' ≅
      elemMap (E ⋙ E') (fun A => (φ A).trans (φ' (E.obj A)))
        (fun A x => (hpos A x).trans (hpos' _ _))
        (fun g x => by simp only [AddEquiv.trans_apply, hpb]; exact hpb' _ _) :=
  NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The isomorphism `T ⋙ R ≅ L ⋙ B` of an explicitly given square. -/
abbrev sqIso {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (h : CatCommSq T L R B) :
    T ⋙ R ≅ L ⋙ B :=
  letI := h
  CatCommSq.iso T L R B

/-- **An isomorphism of Frobenioids**: equivalences of the Frobenioids and of the bases, and
isomorphisms of the divisor monoids `Φ^gp(A) ≅ Φ'^gp(A')` (in both directions) preserving the
effective parts and compatible with the pull-backs, such that the equivalence of Frobenioids
is compatible with the structure functors `P : C ⥤ F_Φ`, `P' : C' ⥤ F_{Φ'}` through the induced
functors of elementary Frobenioids (`elemMap`; both directions). The compatibility with the base
functors (`Iso.comm`) follows. -/
structure Iso (X Y : FrobCat) where
  /-- The equivalence of Frobenioids. -/
  C : X.C ≌ Y.C
  /-- The equivalence of base categories. -/
  D : X.D ≌ Y.D
  /-- `Φ^gp(A) ≅ Φ'^gp(D(A))`. -/
  phi : ∀ A : X.D, X.Φ.obj A ≃+ Y.Φ.obj (D.functor.obj A)
  /-- `phi` identifies `Φ(A)` with `Φ'(D(A))`. -/
  phi_pos : ∀ (A : X.D) (x : X.Φ.obj A), x ∈ X.Φ.pos A ↔ phi A x ∈ Y.Φ.pos (D.functor.obj A)
  /-- `phi` is compatible with the pull-backs. -/
  phi_pb : ∀ {A B : X.D} (g : A ⟶ B) (x : X.Φ.obj B),
    phi A (X.Φ.pb g x) = Y.Φ.pb (D.functor.map g) (phi B x)
  /-- `Φ'^gp(B) ≅ Φ^gp(D⁻¹(B))`. -/
  phiInv : ∀ B : Y.D, Y.Φ.obj B ≃+ X.Φ.obj (D.inverse.obj B)
  /-- `phiInv` identifies `Φ'(B)` with `Φ(D⁻¹(B))`. -/
  phiInv_pos : ∀ (B : Y.D) (y : Y.Φ.obj B),
    y ∈ Y.Φ.pos B ↔ phiInv B y ∈ X.Φ.pos (D.inverse.obj B)
  /-- `phiInv` is compatible with the pull-backs. -/
  phiInv_pb : ∀ {A B : Y.D} (g : A ⟶ B) (y : Y.Φ.obj B),
    phiInv A (Y.Φ.pb g y) = X.Φ.pb (D.inverse.map g) (phiInv B y)
  /-- Compatibility with the structure functors: `C ⋙ P' ≅ P ⋙ F_{(D, phi)}`. -/
  commP : CatCommSq C.functor X.P Y.P (elemMap D.functor phi phi_pos phi_pb)
  /-- Compatibility of the inverse with the structure functors. -/
  commPInv : CatCommSq C.inverse Y.P X.P (elemMap D.inverse phiInv phiInv_pos phiInv_pb)

namespace Iso

/-- Compatibility with the base functors: `C ⋙ base' ≅ base ⋙ D`. -/
@[implicit_reducible]
def comm {X Y : FrobCat} (f : X.Iso Y) : CatCommSq f.C.functor X.base Y.base f.D.functor :=
  ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (sqIso f.commP) Elem.proj ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft X.P (elemMapProj _ _ _ _) ≪≫
    (Functor.associator _ _ _).symm⟩

/-- The identity. -/
def refl (X : FrobCat) : X.Iso X where
  C := CategoryTheory.Equivalence.refl
  D := CategoryTheory.Equivalence.refl
  phi _ := AddEquiv.refl _
  phi_pos _ _ := Iff.rfl
  phi_pb _ _ := rfl
  phiInv _ := AddEquiv.refl _
  phiInv_pos _ _ := Iff.rfl
  phiInv_pb _ _ := rfl
  commP := ⟨Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft X.P (elemMapId X.Φ)⟩
  commPInv := ⟨Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft X.P (elemMapId X.Φ)⟩

/-- The inverse. -/
def symm {X Y : FrobCat} (f : X.Iso Y) : Y.Iso X where
  C := f.C.symm
  D := f.D.symm
  phi := f.phiInv
  phi_pos := f.phiInv_pos
  phi_pb := f.phiInv_pb
  phiInv := f.phi
  phiInv_pos := f.phi_pos
  phiInv_pb := f.phi_pb
  commP := f.commPInv
  commPInv := f.commP

/-- The composite. -/
def trans {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z where
  C := f.C.trans g.C
  D := f.D.trans g.D
  phi A := (f.phi A).trans (g.phi (f.D.functor.obj A))
  phi_pos A x := (f.phi_pos A x).trans (g.phi_pos _ _)
  phi_pb _ _ := by simp only [AddEquiv.trans_apply, f.phi_pb]; exact g.phi_pb _ _
  phiInv B := (g.phiInv B).trans (f.phiInv (g.D.inverse.obj B))
  phiInv_pos B y := (g.phiInv_pos B y).trans (f.phiInv_pos _ _)
  phiInv_pb _ _ := by simp only [AddEquiv.trans_apply, g.phiInv_pb]; exact f.phiInv_pb _ _
  commP := ⟨sqIso (CatCommSq.hComp' f.commP g.commP) ≪≫
    Functor.isoWhiskerLeft X.P (elemMapComp _ _ _ _ _ _ _ _)⟩
  commPInv := ⟨sqIso (CatCommSq.hComp' g.commPInv f.commPInv) ≪≫
    Functor.isoWhiskerLeft Z.P (elemMapComp _ _ _ _ _ _ _ _)⟩

end Iso

/-- The Frobenioid with base of a model Frobenioid `P : C ⥤ F_Φ`. -/
def ofModel {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} (C : Type) [Category.{0} C]
    (P : C ⥤ Elem Φ) : FrobCat where
  C := Cat.of C
  D := Cat.of D
  Φ := Φ
  P := P

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
