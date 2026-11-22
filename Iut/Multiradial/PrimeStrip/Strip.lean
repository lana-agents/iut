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
  divisor monoids `Φ(A) ≅ Φ'(A')` (both directions) compatible with the pull-backs and, through
  the unit and counit of the base equivalence, inverse to each other (`phi_unit`, `phi_counit`;
  so they induce an equivalence `F_Φ ≌ F_{Φ'}`, `FrobCat.Iso.elemEquiv`), such that
  the structure functors commute up to natural isomorphism with the induced functor of
  elementary Frobenioids `F_Φ ⥤ F_{Φ'}` (`elemMap`, `(f, Z, n) ↦ (D(f), φ(Z), n)`; a
  `CatCommSq` for the functor and one for the inverse), the two squares being coherent through
  the units and counits of the equivalences (`commP_counit`, `commP_unit`). The square of base
  functors (`FrobCat.Iso.comm`) follows. The `Φ`-isomorphisms are what the isomorphisms `ρ_v` of
  `F^⊩`-prime-strips are compared through (IUT I, Definition 5.2 (iv)).
  For the models every equivalence of the categories admits such a base equivalence when the base
  is slim ([FrdI], Theorem 3.4 (v); `Frobenioid.thm34_galois_preservesBase`, MR16), so this is the
  isomorphism notion of Definition 5.2 (iii); recording the base equivalence makes the passage
  `F ↦ D` of Remark 5.2.1 (i) a functor on isomorphisms (`FComp.toD`, `FComp.isoToD`) without the
  slimness of `Π_v` (not available, MR13).
* A split Frobenioid (`SplitFrobCat`) is a `FrobCat` with a collection of splittings (IUT I,
  Example 3.2 (v), l.4743: "a Frobenioid equipped with a collection of characteristic
  splittings"), each a family `τ(A) ⊆ End(A)` of base-identity linear endomorphisms ([FrdI],
  Definition 2.3; for the models `Model.splitEnd τ`, the endomorphisms with `u ∈ τ(A_D)`). For
  `F^⊢_v` the collection is the `μ_{2l}`-orbit of `q̲_v^ℕ` at `V^bad` (Example 3.2 (iv)) and the
  single splitting `p^ℕ` at `V^good` (`tauOrbit`). An isomorphism of split Frobenioids is an
  isomorphism of Frobenioids whose functor and inverse map each splitting of the collection into
  one of the other collection (`SplitFrobCat.MapsSplit`).
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

/-- If a functor maps the morphism of an isomorphism `i` to that of `κ`, it maps the inverse
of `i` to the inverse of `κ`. -/
lemma map_inv_of_map_hom {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] (P : C₁ ⥤ C₂)
    {a b : C₁} (i : a ≅ b) (κ : P.obj a ≅ P.obj b) (h : P.map i.hom = κ.hom) :
    P.map i.inv = κ.inv :=
  congrArg CategoryTheory.Iso.inv (CategoryTheory.Iso.ext h : P.mapIso i = κ)

/-- The isomorphism of `F_Φ` with divisor `0` and degree `1` over an isomorphism of bases. -/
def elemIsoOfBase {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {A B : Elem Φ}
    (e : A.base ≅ B.base) : A ≅ B where
  hom := ⟨e.hom, 0, (Φ.pos _).zero_mem, 1⟩
  inv := ⟨e.inv, 0, (Φ.pos _).zero_mem, 1⟩
  hom_inv_id := Elem.hom_ext (by simp) (by simp) rfl
  inv_hom_id := Elem.hom_ext (by simp) (by simp) rfl

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
  /-- `phiInv ∘ phi` is the pull-back along the unit `A ⟶ D⁻¹(D(A))` of the base equivalence. -/
  phi_unit : ∀ (A : X.D) (x : X.Φ.obj A),
    X.Φ.pb (D.unit.app A) (phiInv (D.functor.obj A) (phi A x)) = x
  /-- `phi ∘ phiInv` is the pull-back along the inverse counit `B ⟶ D(D⁻¹(B))`. -/
  phi_counit : ∀ (B : Y.D) (y : Y.Φ.obj B),
    Y.Φ.pb (D.counitInv.app B) (phi (D.inverse.obj B) (phiInv B y)) = y
  /-- Compatibility with the structure functors: `C ⋙ P' ≅ P ⋙ F_{(D, phi)}`. -/
  commP : CatCommSq C.functor X.P Y.P (elemMap D.functor phi phi_pos phi_pb)
  /-- Compatibility of the inverse with the structure functors. -/
  commPInv : CatCommSq C.inverse Y.P X.P (elemMap D.inverse phiInv phiInv_pos phiInv_pb)
  /-- `commP` and `commPInv` are compatible through the counits of `C` and `D`:
  `P'(C C⁻¹ B) ≅ E P(C⁻¹ B) ≅ E E⁻¹ P'(B) ≅ P'(B)` is `P'` of the counit. -/
  commP_counit : ∀ B : Y.C,
    (sqIso commP).hom.app (C.inverse.obj B) ≫
      (elemMap D.functor phi phi_pos phi_pb).map ((sqIso commPInv).hom.app B) ≫
        (elemIsoOfBase (A := (elemMap D.functor phi phi_pos phi_pb).obj
          ((elemMap D.inverse phiInv phiInv_pos phiInv_pb).obj (Y.P.obj B))) (B := Y.P.obj B)
          (D.counitIso.app (Y.P.obj B).base)).hom = Y.P.map (C.counit.app B)
  /-- `commP` and `commPInv` are compatible through the units of `C` and `D`:
  `P(C⁻¹ C A) ≅ E⁻¹ P'(C A) ≅ E⁻¹ E P(A) ≅ P(A)` is `P` of the inverse unit. -/
  commP_unit : ∀ A : X.C,
    (sqIso commPInv).hom.app (C.functor.obj A) ≫
      (elemMap D.inverse phiInv phiInv_pos phiInv_pb).map ((sqIso commP).hom.app A) ≫
        (elemIsoOfBase (A := X.P.obj A) (B := (elemMap D.inverse phiInv phiInv_pos phiInv_pb).obj
          ((elemMap D.functor phi phi_pos phi_pb).obj (X.P.obj A)))
          (D.unitIso.app (X.P.obj A).base)).inv = X.P.map (C.unitInv.app A)

namespace Iso

/-- Compatibility with the base functors: `C ⋙ base' ≅ base ⋙ D`. -/
@[implicit_reducible]
def comm {X Y : FrobCat} (f : X.Iso Y) : CatCommSq f.C.functor X.base Y.base f.D.functor :=
  ⟨(Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (sqIso f.commP) Elem.proj ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft X.P (elemMapProj _ _ _ _) ≪≫
    (Functor.associator _ _ _).symm⟩

/-- The square `commP` of the identity (identity components). -/
@[implicit_reducible]
def reflCommP (X : FrobCat) :
    CatCommSq (𝟭 X.C) X.P X.P
      (elemMap (𝟭 X.D) (fun A => AddEquiv.refl (X.Φ.obj A)) (fun _ _ => Iff.rfl)
        (fun _ _ => rfl)) :=
  ⟨NatIso.ofComponents (fun _ => CategoryTheory.Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)⟩

lemma refl_coh_counit (X : FrobCat) (B : X.C) :
    𝟙 (X.P.obj B) ≫
      (elemMap (𝟭 X.D) (fun A => AddEquiv.refl (X.Φ.obj A)) (fun _ _ => Iff.rfl)
        (fun _ _ => rfl)).map (𝟙 (X.P.obj B)) ≫
      (elemIsoOfBase (A := X.P.obj B) (B := X.P.obj B) (CategoryTheory.Iso.refl _)).hom =
    X.P.map (𝟙 B) :=
  (Category.id_comp _).trans (((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
    (Category.id_comp _)).trans ((Elem.hom_ext rfl rfl rfl).trans (X.P.map_id B).symm))

lemma refl_coh_unit (X : FrobCat) (A : X.C) :
    𝟙 (X.P.obj A) ≫
      (elemMap (𝟭 X.D) (fun A => AddEquiv.refl (X.Φ.obj A)) (fun _ _ => Iff.rfl)
        (fun _ _ => rfl)).map (𝟙 (X.P.obj A)) ≫
      (elemIsoOfBase (A := X.P.obj A) (B := X.P.obj A) (CategoryTheory.Iso.refl _)).inv =
    X.P.map (𝟙 A) :=
  (Category.id_comp _).trans (((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
    (Category.id_comp _)).trans ((Elem.hom_ext rfl rfl rfl).trans (X.P.map_id A).symm))

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
  phi_unit A x := X.Φ.pb_id A x
  phi_counit B y := X.Φ.pb_id B y
  commP := reflCommP X
  commPInv := reflCommP X
  commP_counit B := refl_coh_counit X B
  commP_unit A := refl_coh_unit X A

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
  phi_unit := f.phi_counit
  phi_counit := f.phi_unit
  commP := f.commPInv
  commPInv := f.commP
  commP_counit := f.commP_unit
  commP_unit := f.commP_counit

/-- The unit of a composite equivalence. -/
lemma trans_unit_app {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (e : C₁ ≌ C₂) (e' : C₂ ≌ C₃) (A : C₁) :
    (e.trans e').unit.app A = e.unit.app A ≫ e.inverse.map (e'.unit.app (e.functor.obj A)) := by
  have h1 : e.inverse.map (𝟙 (e.functor.obj A)) = 𝟙 _ := e.inverse.map_id _
  have h2 : e.inverse.map (𝟙 (e'.inverse.obj (e'.functor.obj (e.functor.obj A)))) = 𝟙 _ :=
    e.inverse.map_id _
  simp only [Functor.id_obj, CategoryTheory.Equivalence.trans, Equivalence.Equivalence_mk'_unit,
    Functor.isoWhiskerRight_trans, Iso.trans_assoc, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.associator_hom_app]
  erw [h1, h2]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]; rfl

/-- The inverse counit of a composite equivalence. -/
lemma trans_counitInv_app {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (e : C₁ ≌ C₂) (e' : C₂ ≌ C₃) (B : C₃) :
    (e.trans e').counitInv.app B =
      e'.counitInv.app B ≫ e'.functor.map (e.counitInv.app (e'.inverse.obj B)) := by
  have h1 : e'.functor.map (𝟙 (e'.inverse.obj B)) = 𝟙 _ := e'.functor.map_id _
  have h2 : e'.functor.map (𝟙 (e.functor.obj (e.inverse.obj (e'.inverse.obj B)))) = 𝟙 _ :=
    e'.functor.map_id _
  simp only [Functor.id_obj, CategoryTheory.Equivalence.trans,
    Equivalence.Equivalence_mk'_counitInv, Functor.isoWhiskerRight_trans, Iso.trans_assoc,
    Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Category.assoc,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app]
  erw [h1, h2]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]; rfl

/-- `phi ∘ phiInv` is the pull-back along the counit `D(D⁻¹(B)) ⟶ B`. -/
lemma phi_phiInv {X Y : FrobCat} (f : X.Iso Y) (B : Y.D) (y : Y.Φ.obj B) :
    f.phi (f.D.inverse.obj B) (f.phiInv B y) = Y.Φ.pb (f.D.counit.app B) y := by
  have h := congrArg (Y.Φ.pb (f.D.counit.app B)) (f.phi_counit B y)
  refine Eq.trans ?_ h
  refine Eq.trans ?_ (Y.Φ.pb_comp _ _ _)
  have e : f.D.counit.app B ≫ f.D.counitInv.app B = 𝟙 _ := f.D.counitIso.hom_inv_id_app B
  exact ((congrArg (fun g => Y.Φ.pb g (f.phi (f.D.inverse.obj B) (f.phiInv B y))) e).trans
    (Y.Φ.pb_id _ _)).symm

/-- `phiInv ∘ phi` is the pull-back along the inverse unit `D⁻¹(D(A)) ⟶ A`. -/
lemma phiInv_phi {X Y : FrobCat} (f : X.Iso Y) (A : X.D) (x : X.Φ.obj A) :
    f.phiInv (f.D.functor.obj A) (f.phi A x) = X.Φ.pb (f.D.unitInv.app A) x := by
  have h := congrArg (X.Φ.pb (f.D.unitInv.app A)) (f.phi_unit A x)
  refine Eq.trans ?_ h
  refine Eq.trans ?_ (X.Φ.pb_comp _ _ _)
  have e : f.D.unitInv.app A ≫ f.D.unit.app A = 𝟙 _ := f.D.unitIso.inv_hom_id_app A
  exact ((congrArg (fun g => X.Φ.pb g (f.phiInv (f.D.functor.obj A) (f.phi A x))) e).trans
    (X.Φ.pb_id _ _)).symm

/-- The unit of `elemEquiv`. -/
def elemUnit {X Y : FrobCat} (f : X.Iso Y) :
    𝟭 (Elem X.Φ) ≅ elemMap f.D.functor f.phi f.phi_pos f.phi_pb ⋙
      elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb :=
  NatIso.ofComponents (fun A => elemIsoOfBase (f.D.unitIso.app A.base)) fun {A B} φ =>
    Elem.hom_ext (f.D.unit.naturality φ.base)
      ((congrArg₂ (· + ·) (X.Φ.pb φ.base).map_zero
        ((congrArg (· • φ.div) PNat.one_coe).trans (one_smul ℕ _))).trans
        ((zero_add _).trans ((f.phi_unit A.base φ.div).symm.trans
          ((add_zero _).symm.trans (congrArg _ (smul_zero _).symm)))))
      (by simp [elemIsoOfBase, elemMap, mul_comm])

/-- The counit of `elemEquiv`. -/
def elemCounit {X Y : FrobCat} (f : X.Iso Y) :
    elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb ⋙
      elemMap f.D.functor f.phi f.phi_pos f.phi_pb ≅ 𝟭 (Elem Y.Φ) :=
  NatIso.ofComponents (fun B => elemIsoOfBase (f.D.counitIso.app B.base)) fun {A B} φ =>
    Elem.hom_ext (f.D.counit.naturality φ.base)
      ((congrArg₂ (fun a b : Y.Φ.obj (f.D.functor.obj (f.D.inverse.obj A.base)) => a + b)
        (Y.Φ.pb _).map_zero
        ((congrArg (· • _) PNat.one_coe).trans ((one_smul ℕ _).trans (phi_phiInv f _ φ.div)))).trans
        ((zero_add _).trans ((add_zero _).symm.trans (congrArg _ (smul_zero _).symm))))
      (by simp [elemIsoOfBase, elemMap, mul_comm])

/-- **The equivalence of elementary Frobenioids `F_Φ ≌ F_{Φ'}`** induced by an isomorphism of
Frobenioids: its functor is `elemMap D phi`, its inverse `elemMap D⁻¹ phiInv` (the coherences
`phi_unit`, `phi_counit` make the units of `D` natural in `F_Φ`). -/
def elemEquiv {X Y : FrobCat} (f : X.Iso Y) : Elem X.Φ ≌ Elem Y.Φ :=
  CategoryTheory.Equivalence.mk _ _ (elemUnit f) (elemCounit f)

lemma elemEquiv_functor {X Y : FrobCat} (f : X.Iso Y) :
    (elemEquiv f).functor = elemMap f.D.functor f.phi f.phi_pos f.phi_pb := rfl

lemma elemEquiv_inverse {X Y : FrobCat} (f : X.Iso Y) :
    (elemEquiv f).inverse = elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb := rfl

/-- The counit of a composite equivalence. -/
lemma trans_counit_app {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (e : C₁ ≌ C₂) (e' : C₂ ≌ C₃) (B : C₃) :
    (e.trans e').counit.app B =
      e'.functor.map (e.counit.app (e'.inverse.obj B)) ≫ e'.counit.app B :=
  (CategoryTheory.Iso.inv_eq_inv ((e.trans e').counitIso.app B)
    (e'.functor.mapIso (e.counitIso.app (e'.inverse.obj B)) ≪≫ e'.counitIso.app B)).1
      (trans_counitInv_app e e' B)

/-- The inverse unit of a composite equivalence. -/
lemma trans_unitInv_app {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (e : C₁ ≌ C₂) (e' : C₂ ≌ C₃) (A : C₁) :
    (e.trans e').unitInv.app A =
      e.inverse.map (e'.unitInv.app (e.functor.obj A)) ≫ e.unitInv.app A :=
  congrArg CategoryTheory.Iso.inv (CategoryTheory.Iso.ext (trans_unit_app e e' A) :
    (e.trans e').unitIso.app A =
      e.unitIso.app A ≪≫ e.inverse.mapIso (e'.unitIso.app (e.functor.obj A)))

/-- `elemIsoOfBase` is compatible with composition. -/
lemma elemIsoOfBase_comp {D₁ : Type} [Category.{0} D₁] {Φ : DivMonoid.{0} D₁} {A B E : Elem Φ}
    (e : A.base ≅ B.base) (e' : B.base ≅ E.base) :
    (elemIsoOfBase e).hom ≫ (elemIsoOfBase e').hom = (elemIsoOfBase (e ≪≫ e')).hom :=
  Elem.hom_ext rfl (by simp [elemIsoOfBase]) rfl

/-- The divisor of `elemMap(x) ≫ y` for `x`, `y` with zero divisor and `y` of degree `1`. -/
lemma elemMap_comp_div_eq_zero {D₁ D₂ : Type} [Category.{0} D₁] [Category.{0} D₂]
    {Φ : DivMonoid.{0} D₁} {Ψ : DivMonoid.{0} D₂} (E : D₁ ⥤ D₂)
    (φ : ∀ A, Φ.obj A ≃+ Ψ.obj (E.obj A))
    (hpos : ∀ A x, x ∈ Φ.pos A ↔ φ A x ∈ Ψ.pos (E.obj A))
    (hpb : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ A (Φ.pb g x) = Ψ.pb (E.map g) (φ B x))
    {a b : Elem Φ} {c : Elem Ψ} (x : a ⟶ b) (y : (elemMap E φ hpos hpb).obj b ⟶ c)
    (hx : x.div = 0) (hy : y.div = 0) (hyd : y.deg = 1) :
    ((elemMap E φ hpos hpb).map x ≫ y).div = 0 := by
  change Ψ.pb (E.map x.base) y.div + (y.deg : ℕ) • φ a.base x.div = 0
  rw [hy, hyd, hx, PNat.one_coe, one_smul, map_zero (φ a.base)]
  exact (add_zero _).trans (map_zero _)

/-- **Pasting of the coherences `commP_counit` (resp. `commP_unit`) of a composite**, in an
arbitrary category (the objects are left implicit, so it applies up to definitional equality). -/
lemma paste_coh {C₀ : Type*} [Category* C₀] {o1 o2 o3 o4 o5 o6 o7 o8 o9 : C₀}
    {L1 : o1 ⟶ o3} {P1 : o1 ⟶ o2} {a : o2 ⟶ o3} (h1 : L1 = P1 ≫ a)
    {L2 : o3 ⟶ o5} {b : o3 ⟶ o4} {c : o4 ⟶ o5} (h2 : L2 = b ≫ c)
    {L3 : o5 ⟶ o7} {d : o5 ⟶ o6} {κ : o6 ⟶ o7} (h3 : L3 = d ≫ κ)
    {R : o1 ⟶ o7} {Q1 : o1 ⟶ o9} {Q2 : o9 ⟶ o7} (hR : R = Q1 ≫ Q2)
    {d2 : o4 ⟶ o8} {e2 : o8 ⟶ o6} {y : o2 ⟶ o8} {P2 : o9 ⟶ o8}
    (hnat : c ≫ d = d2 ≫ e2) (hf : a ≫ b ≫ d2 = y) (hP : Q1 ≫ P2 = P1 ≫ y)
    (hg : P2 ≫ e2 ≫ κ = Q2) : L1 ≫ L2 ≫ L3 = R := by
  subst h1 h2 h3 hR
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hf, ← reassoc_of% hP, hg]

/-- Naturality of a composite of squares, in an arbitrary category. -/
lemma paste_nat {C₀ : Type*} [Category* C₀] {o1 o2 o3 o4 o5 o6 : C₀}
    {m1 : o1 ⟶ o2} {p : o2 ⟶ o3} {q : o3 ⟶ o5} {p' : o1 ⟶ o4} {n : o4 ⟶ o3} {q' : o4 ⟶ o6}
    {m2 : o6 ⟶ o5}
    (h1 : m1 ≫ p = p' ≫ n) (h2 : n ≫ q = q' ≫ m2) : m1 ≫ (p ≫ q) = (p' ≫ q') ≫ m2 := by
  rw [reassoc_of% h1, h2, Category.assoc]

/-- The square `commP` of a composite. -/
@[implicit_reducible]
def transCommP {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) :
    CatCommSq (f.C.trans g.C).functor X.P Z.P
      (elemMap (f.D.trans g.D).functor (fun A => (f.phi A).trans (g.phi (f.D.functor.obj A)))
        (fun A x => (f.phi_pos A x).trans (g.phi_pos _ _))
        (fun _ _ => by simp only [AddEquiv.trans_apply, f.phi_pb]; exact g.phi_pb _ _)) :=
  ⟨NatIso.ofComponents (fun A => (sqIso g.commP).app (f.C.functor.obj A) ≪≫
      (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).mapIso ((sqIso f.commP).app A))
    (fun {_ _} m => paste_nat ((sqIso g.commP).hom.naturality (f.C.functor.map m))
      (((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _).symm.trans
        ((congrArg (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map
          ((sqIso f.commP).hom.naturality m)).trans
          ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _))))⟩

lemma transCommP_app {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) (A : X.C) :
    (sqIso (transCommP f g)).hom.app A = (sqIso g.commP).hom.app (f.C.functor.obj A) ≫
      (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map ((sqIso f.commP).hom.app A) := rfl

/-- The square `commPInv` of a composite. -/
@[implicit_reducible]
def transCommPInv {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) :
    CatCommSq (f.C.trans g.C).inverse Z.P X.P
      (elemMap (f.D.trans g.D).inverse (fun B => (g.phiInv B).trans (f.phiInv (g.D.inverse.obj B)))
        (fun B y => (g.phiInv_pos B y).trans (f.phiInv_pos _ _))
        (fun _ _ => by simp only [AddEquiv.trans_apply, g.phiInv_pb]; exact f.phiInv_pb _ _)) :=
  ⟨NatIso.ofComponents (fun B => (sqIso f.commPInv).app (g.C.inverse.obj B) ≪≫
      (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).mapIso ((sqIso g.commPInv).app B))
    (fun {_ _} m => paste_nat ((sqIso f.commPInv).hom.naturality (g.C.inverse.map m))
      (((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _).symm.trans
        ((congrArg (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
          ((sqIso g.commPInv).hom.naturality m)).trans
          ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _))))⟩

lemma transCommPInv_app {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) (B : Z.C) :
    (sqIso (transCommPInv f g)).hom.app B = (sqIso f.commPInv).hom.app (g.C.inverse.obj B) ≫
      (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
        ((sqIso g.commPInv).hom.app B) := rfl

/-- The counit isomorphism of `F_Φ` of a composite. -/
lemma trans_elemCounit {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) (b : Elem Z.Φ) :
    (elemIsoOfBase (A := ⟨(f.D.trans g.D).functor.obj ((f.D.trans g.D).inverse.obj b.base)⟩)
      (B := b) ((f.D.trans g.D).counitIso.app b.base)).hom =
    (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj
          ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).obj
            ((elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b)))
        (B := (elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b)
        (f.D.counitIso.app (g.D.inverse.obj b.base))).hom ≫
    (elemIsoOfBase (A := (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
        ((elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b))
      (B := b) (g.D.counitIso.app b.base)).hom :=
  Elem.hom_ext (trans_counit_app f.D g.D b.base)
    (elemMap_comp_div_eq_zero (E := g.D.functor) (φ := g.phi) (hpos := g.phi_pos)
      (hpb := g.phi_pb)
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj
          ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).obj
            ((elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b)))
        (B := (elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b)
        (f.D.counitIso.app (g.D.inverse.obj b.base))).hom
      (elemIsoOfBase (A := (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
        ((elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj b))
        (B := b) (g.D.counitIso.app b.base)).hom rfl rfl rfl).symm rfl

/-- The inverse unit isomorphism of `F_Φ` of a composite. -/
lemma trans_elemUnitInv {X Y Z : FrobCat} (f : X.Iso Y) (g : Y.Iso Z) (a : Elem X.Φ) :
    (elemIsoOfBase (A := a)
      (B := ⟨(f.D.trans g.D).inverse.obj ((f.D.trans g.D).functor.obj a.base)⟩)
      ((f.D.trans g.D).unitIso.app a.base)).inv =
    (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a)
        (B := (elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj
          ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
            ((elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a)))
        (g.D.unitIso.app (f.D.functor.obj a.base))).inv ≫
    (elemIsoOfBase (A := a) (B := (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).obj
        ((elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a))
      (f.D.unitIso.app a.base)).inv :=
  Elem.hom_ext (trans_unitInv_app f.D g.D a.base)
    (elemMap_comp_div_eq_zero (E := f.D.inverse) (φ := f.phiInv) (hpos := f.phiInv_pos)
      (hpb := f.phiInv_pb)
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a)
        (B := (elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).obj
          ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
            ((elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a)))
        (g.D.unitIso.app (f.D.functor.obj a.base))).inv
      (elemIsoOfBase (A := a) (B := (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).obj
        ((elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj a))
        (f.D.unitIso.app a.base)).inv rfl rfl rfl).symm rfl

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
  phi_unit A x := by
    rw [trans_unit_app]
    refine (X.Φ.pb_comp _ _ _).trans ?_
    refine (congrArg (X.Φ.pb (f.D.unit.app A))
      (f.phiInv_pb (g.D.unit.app (f.D.functor.obj A)) _).symm).trans ?_
    refine (congrArg (fun z => X.Φ.pb (f.D.unit.app A) (f.phiInv _ z))
      (g.phi_unit _ _)).trans ?_
    exact f.phi_unit A x
  phi_counit B y := by
    rw [trans_counitInv_app]
    refine (Z.Φ.pb_comp _ _ _).trans ?_
    refine (congrArg (Z.Φ.pb (g.D.counitInv.app B))
      (g.phi_pb (f.D.counitInv.app (g.D.inverse.obj B)) _).symm).trans ?_
    refine (congrArg (fun z => Z.Φ.pb (g.D.counitInv.app B) (g.phi _ z))
      (f.phi_counit _ _)).trans ?_
    exact g.phi_counit B y
  commP := transCommP f g
  commPInv := transCommPInv f g
  commP_counit B := paste_coh (transCommP_app f g _)
    ((congrArg (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map
      ((elemMap f.D.functor f.phi f.phi_pos f.phi_pb).map_comp _ _)).trans
      ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _))
    (trans_elemCounit f g (Z.P.obj B))
    ((congrArg Z.P.map (trans_counit_app f.C g.C B)).trans (Z.P.map_comp _ _))
    (((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _).symm.trans
      ((congrArg (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map
        ((elemCounit f).hom.naturality ((sqIso g.commPInv).hom.app B))).trans
        ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _)))
    ((congrArg (_ ≫ ·) ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _).symm).trans
      (((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _).symm.trans
        (congrArg (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map
          (f.commP_counit (g.C.inverse.obj B)))))
    ((sqIso g.commP).hom.naturality (f.C.counit.app (g.C.inverse.obj B)))
    (g.commP_counit B)
  commP_unit A := paste_coh (transCommPInv_app f g _)
    ((congrArg (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
      ((elemMap g.D.inverse g.phiInv g.phiInv_pos g.phiInv_pb).map_comp _ _)).trans
      ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _))
    (trans_elemUnitInv f g (X.P.obj A))
    ((congrArg X.P.map (trans_unitInv_app f.C g.C A)).trans (X.P.map_comp _ _))
    (((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _).symm.trans
      ((congrArg (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
        ((elemUnit g).inv.naturality ((sqIso f.commP).hom.app A))).trans
        ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _)))
    ((congrArg (_ ≫ ·)
      ((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _).symm).trans
      (((elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map_comp _ _).symm.trans
        (congrArg (elemMap f.D.inverse f.phiInv f.phiInv_pos f.phiInv_pb).map
          (g.commP_unit (f.C.functor.obj A)))))
    ((sqIso f.commPInv).hom.naturality (g.C.unitInv.app (f.C.functor.obj A)))
    (f.commP_unit A)

end Iso

/-- The Frobenioid with base of a model Frobenioid `P : C ⥤ F_Φ`. -/
def ofModel {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} (C : Type) [Category.{0} C]
    (P : C ⥤ Elem Φ) : FrobCat where
  C := Cat.of C
  D := Cat.of D
  Φ := Φ
  P := P

end FrobCat

/-- **A split Frobenioid** ([FrdI], Definition 2.3; IUT I, Example 3.2 (iv), (v), l.4743: "a
Frobenioid equipped with a collection of characteristic splittings"): a Frobenioid with a
collection of splittings, each recorded by the endomorphisms `τ(A) ⊆ O^▷(A) ⊆ End(A)`. -/
structure SplitFrobCat : Type 1 where
  /-- The Frobenioid. -/
  F : FrobCat
  /-- The collection of splittings. -/
  tau : Set (∀ A : F.C, Set (A ⟶ A))

namespace SplitFrobCat

/-- A functor maps the splitting `s` into the splitting `s'`. -/
def MapsSplit {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] (F : C₁ ⥤ C₂)
    (s : ∀ A : C₁, Set (A ⟶ A)) (s' : ∀ B : C₂, Set (B ⟶ B)) : Prop :=
  ∀ (A : C₁) (e : A ⟶ A), e ∈ s A → F.map e ∈ s' (F.obj A)

/-- **An isomorphism of split Frobenioids**: an isomorphism of Frobenioids whose functor and
inverse map every splitting of the collection into a splitting of the other collection. -/
structure Iso (X Y : SplitFrobCat) where
  /-- The isomorphism of Frobenioids. -/
  iso : X.F.Iso Y.F
  /-- The functor preserves the collections of splittings. -/
  map_tau : ∀ s ∈ X.tau, ∃ s' ∈ Y.tau, MapsSplit iso.C.functor s s'
  /-- The inverse preserves the collections of splittings. -/
  inv_tau : ∀ s ∈ Y.tau, ∃ s' ∈ X.tau, MapsSplit iso.C.inverse s s'

namespace Iso

/-- The identity. -/
def refl (X : SplitFrobCat) : X.Iso X :=
  ⟨FrobCat.Iso.refl _, fun s hs => ⟨s, hs, fun _ _ h => h⟩, fun s hs => ⟨s, hs, fun _ _ h => h⟩⟩

/-- The inverse. -/
def symm {X Y : SplitFrobCat} (f : X.Iso Y) : Y.Iso X := ⟨f.iso.symm, f.inv_tau, f.map_tau⟩

/-- The composite. -/
def trans {X Y Z : SplitFrobCat} (f : X.Iso Y) (g : Y.Iso Z) : X.Iso Z :=
  ⟨f.iso.trans g.iso,
    fun s hs => by
      obtain ⟨s₁, hs₁, h₁⟩ := f.map_tau s hs
      obtain ⟨s₂, hs₂, h₂⟩ := g.map_tau s₁ hs₁
      exact ⟨s₂, hs₂, fun A e he => h₂ _ _ (h₁ A e he)⟩,
    fun s hs => by
      obtain ⟨s₁, hs₁, h₁⟩ := g.inv_tau s hs
      obtain ⟨s₂, hs₂, h₂⟩ := f.inv_tau s₁ hs₁
      exact ⟨s₂, hs₂, fun A e he => h₂ _ _ (h₁ A e he)⟩⟩

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

/-- **A collection of splittings of a model Frobenioid**: the splittings `Model.splitEnd (τ i)`
for `i ∈ S`. -/
def Model.orbitSplitEnd {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} {B : GrpOn.{0} D}
    {divB : DivHom B Φ.toGrpOn} {ι : Type} (τ : ι → ∀ A : D, AddSubmonoid (B.obj A)) (S : Set ι) :
    Set (∀ X : Model Φ B divB, Set (X ⟶ X)) :=
  {s | ∃ i ∈ S, s = Model.splitEnd (τ i)}

/-! ### The models at `v ∈ V^non` -/

section Models

variable (D : InitialThetaData.{0}) (v : FinitePlace ↥(fieldOfModuli D.F D.E))

/-- **`C_v` with its base `D_v`**. -/
def cvFrob : FrobCat := FrobCat.ofModel (Cv D v) (cvElem D v)

/-- **`C^⊢_v` with its base `D^⊢_v`**. -/
def cvdFrob : FrobCat := FrobCat.ofModel (CVdash D v) (cvdElem D v)

/-- **`F^⊢_v = (C^⊢_v, τ^⊢_v)`** (IUT I, Examples 3.2 (iv), 3.3 (i)): `τ^⊢_v` the
`μ_{2l}`-orbit of the splitting `q̲_v^ℕ` at `V^bad`, the splitting `p^ℕ` at `V^good`
(`tauOrbit`). -/
def fVdashModel : SplitFrobCat where
  F := cvdFrob D v
  tau := Model.orbitSplitEnd
    (GaloisModel.piSplit (PAdicGalois.ord (pv D v)) (PAdicGalois.ord_smul (pv D v) (Lv D v))
      (gammaVdash D v)) (tauOrbit D v)

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
