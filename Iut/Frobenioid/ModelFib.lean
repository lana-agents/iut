/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34Base

/-!
# Fibres of model Frobenioids and the restriction of base-preserving functors

For a model Frobenioid `C = Model Φ B divB` over `D` and an object `A` of `D`, the **fibre**
`Fib Φ B divB A` is the category of objects `(A, α)` of `C` over `A` with the base-identity
morphisms between them ([FrdI], Theorem 6.4 is stated objectwise over the objects of `D`).

If a functor `Ψ : C₁ ⥤ C₂` lies over `G : D₁ ⥤ D₂` (`η : Base ∘ Ψ ≅ G ∘ Base`, the conclusion
`PreservesBase` of [FrdI], Theorem 3.4(v) / Corollary 4.11(ii)), then transporting `Ψ(A, α)`
along `η` to an object over `G(A)` gives the **restriction** `Model.resFib Ψ G η A :
Fib₁ A ⥤ Fib₂ (G A)`, with `resFib ⋙ incl ≅ incl ⋙ Ψ` (`Model.resFibIncl`). If `Ψ` is an
equivalence and `G` is fully faithful, the restriction is an equivalence
(`Model.resFib_isEquivalence`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Model

section Fib

variable {D : Type u₁} [Category.{v₁} D]
/-- **The fibre of a model Frobenioid over `A`**: objects `(A, α)`. -/
structure Fib (Φ : DivMonoid.{w₁} D) (B : GrpOn.{w₁} D) (divB : DivHom B Φ.toGrpOn) (A : D) where
  /-- The divisor `α ∈ Φ^gp(A)`. -/
  α : Φ.obj A

variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn} {A : D}

/-- The underlying object `(A, α)` of the model Frobenioid. -/
abbrev Fib.toModel (X : Fib Φ B divB A) : Model Φ B divB := ⟨A, X.α⟩

instance : Category (Fib Φ B divB A) where
  Hom X Y := {φ : X.toModel ⟶ Y.toModel // φ.base = 𝟙 A}
  id X := ⟨𝟙 _, rfl⟩
  comp f g := ⟨f.1 ≫ g.1, by rw [comp_base, f.2, g.2, Category.comp_id]⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[ext] lemma Fib.hom_ext {X Y : Fib Φ B divB A} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] lemma Fib.id_val (X : Fib Φ B divB A) : (𝟙 X : X ⟶ X).1 = 𝟙 X.toModel := rfl

@[simp] lemma Fib.comp_val {X Y Z : Fib Φ B divB A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

variable (Φ B divB A) in
/-- The inclusion of the fibre. -/
@[simps]
def Fib.incl : Fib Φ B divB A ⥤ Model Φ B divB where
  obj X := X.toModel
  map f := f.1

instance : (Fib.incl Φ B divB A).Faithful where
  map_injective h := Subtype.ext h

/-- An isomorphism of the model with identity base is an isomorphism of the fibre. -/
@[simps]
def Fib.isoMk {X Y : Fib Φ B divB A} (i : X.toModel ≅ Y.toModel) (h : i.hom.base = 𝟙 A) :
    X ≅ Y where
  hom := ⟨i.hom, h⟩
  inv := ⟨i.inv, by
    have := congrArg Hom.base i.inv_hom_id
    rw [comp_base, h, Category.comp_id] at this
    exact this⟩
  hom_inv_id := Subtype.ext i.hom_inv_id
  inv_hom_id := Subtype.ext i.inv_hom_id

lemma inv_base {X Y : Model Φ B divB} (φ : X ⟶ Y) [IsIso φ] [IsIso φ.base] :
    (inv φ).base = inv φ.base := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← comp_base, IsIso.hom_inv_id]
  rfl

end Fib

/-! ### Restriction of base-preserving functors -/

section Res

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

variable (Ψ : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) (G : D₁ ⥤ D₂)
  (η : Ψ ⋙ toElem Φ₂ B₂ divB₂ ⋙ Elem.proj ≅ (toElem Φ₁ B₁ divB₁ ⋙ Elem.proj) ⋙ G)

/-- The component `Base(Ψ X) ≅ G(Base X)`. -/
abbrev ηb (X : Model Φ₁ B₁ divB₁) : (Ψ.obj X).base ≅ G.obj X.base := η.app X

lemma ηb_natural {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) :
    (Ψ.map φ).base ≫ (ηb Ψ G η Y).hom = (ηb Ψ G η X).hom ≫ G.map φ.base :=
  η.hom.naturality φ

variable {A : D₁}

/-- The object `(G A, η^* α_{Ψ X})` over `G A`. -/
abbrev resObj (X : Fib Φ₁ B₁ divB₁ A) : Fib Φ₂ B₂ divB₂ (G.obj A) :=
  ⟨Φ₂.pb (ηb Ψ G η X.toModel).inv (Ψ.obj X.toModel).α⟩

/-- The pull-back isomorphism `ρ_X : (G A, η^* α) → Ψ(A, α)`. -/
def resRho (X : Fib Φ₁ B₁ divB₁ A) : (resObj Ψ G η X).toModel ⟶ Ψ.obj X.toModel :=
  mk1 (ηb Ψ G η X.toModel).inv 0 (Φ₂.pos _).zero_mem 0 (by simp)

@[simp] lemma resRho_base (X : Fib Φ₁ B₁ divB₁ A) :
    (resRho Ψ G η X).base = (ηb Ψ G η X.toModel).inv := rfl

lemma isIso_resRho (X : Fib Φ₁ B₁ divB₁ A) : IsIso (resRho Ψ G η X) :=
  isIso_of _ rfl (by rw [resRho_base]; infer_instance) rfl

attribute [instance] isIso_resRho

lemma inv_resRho_base (X : Fib Φ₁ B₁ divB₁ A) :
    (inv (resRho Ψ G η X)).base = (ηb Ψ G η X.toModel).hom := by
  have h := congrArg Hom.base (IsIso.hom_inv_id (resRho Ψ G η X))
  rw [comp_base, resRho_base] at h
  have h' := (Iso.inv_comp_eq _).mp h
  rw [h']
  exact Category.comp_id _

/-- **The restriction of `Ψ` to the fibres** over `A` and `G A`. -/
@[simps]
noncomputable def resFib : Fib Φ₁ B₁ divB₁ A ⥤ Fib Φ₂ B₂ divB₂ (G.obj A) where
  obj X := resObj Ψ G η X
  map {X Y} f := ⟨resRho Ψ G η X ≫ Ψ.map f.1 ≫ inv (resRho Ψ G η Y), by
    rw [comp_base, comp_base, inv_resRho_base, resRho_base, ηb_natural, f.2, G.map_id,
      Category.comp_id, Iso.inv_hom_id]⟩
  map_id X := Fib.hom_ext (by simp)
  map_comp f g := Fib.hom_ext (by simp)

/-- **`resFib ⋙ incl ≅ incl ⋙ Ψ`.** -/
noncomputable def resFibIncl :
    resFib Ψ G η (A := A) ⋙ Fib.incl Φ₂ B₂ divB₂ (G.obj A) ≅ Fib.incl Φ₁ B₁ divB₁ A ⋙ Ψ :=
  NatIso.ofComponents (fun X => @asIso _ _ _ _ (resRho Ψ G η X) (isIso_resRho Ψ G η X))
    (fun {X Y} f => by
      change (resRho Ψ G η X ≫ Ψ.map f.1 ≫ inv (resRho Ψ G η Y)) ≫ resRho Ψ G η Y =
        resRho Ψ G η X ≫ Ψ.map f.1
      simp)

instance [Ψ.Faithful] : (resFib Ψ G η (A := A)).Faithful where
  map_injective {X Y} f g h := by
    have h1 := congrArg Subtype.val h
    simp only [resFib_map_coe] at h1
    exact Fib.hom_ext (Ψ.map_injective ((cancel_mono _).mp ((cancel_epi _).mp h1)))

instance [Ψ.Full] [G.Faithful] : (resFib Ψ G η (A := A)).Full where
  map_surjective {X Y} ψ := by
    let φ := Ψ.preimage (inv (resRho Ψ G η X) ≫ ψ.1 ≫ resRho Ψ G η Y)
    have hφ : Ψ.map φ = inv (resRho Ψ G η X) ≫ ψ.1 ≫ resRho Ψ G η Y := Ψ.map_preimage _
    have hb : φ.base = 𝟙 A := by
      apply G.map_injective
      have := ηb_natural Ψ G η φ
      rw [hφ, comp_base, comp_base, inv_resRho_base, resRho_base, ψ.2, Category.id_comp,
        Category.assoc, Iso.inv_hom_id, Category.comp_id] at this
      have h2 := congrArg (fun k => (ηb Ψ G η X.toModel).inv ≫ k) this
      simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id] at h2
      rw [G.map_id]
      exact h2.symm
    refine ⟨⟨φ, hb⟩, Fib.hom_ext ?_⟩
    change resRho Ψ G η X ≫ Ψ.map φ ≫ inv (resRho Ψ G η Y) =
      (ψ.1 : (resObj Ψ G η X).toModel ⟶ (resObj Ψ G η Y).toModel)
    simp only [hφ, Category.assoc, IsIso.hom_inv_id_assoc]
    exact (congrArg (fun k => (ψ.1 : (resObj Ψ G η X).toModel ⟶ (resObj Ψ G η Y).toModel) ≫ k)
      (IsIso.hom_inv_id (resRho Ψ G η Y))).trans (Category.comp_id _)

instance [Ψ.EssSurj] [G.Full] [G.Faithful] : (resFib Ψ G η (A := A)).EssSurj where
  mem_essImage Z := by
    let W := Ψ.objPreimage Z.toModel
    let e : Ψ.obj W ≅ Z.toModel := Ψ.objObjPreimageIso Z.toModel
    haveI : IsIso e.hom.base := isIso_Base (P := toElem Φ₂ B₂ divB₂) e.hom
    let κ' : G.obj W.base ⟶ G.obj A := (ηb Ψ G η W).inv ≫ e.hom.base
    let κ : W.base ⟶ A := G.preimage κ'
    have hκ : G.map κ = κ' := G.map_preimage _
    haveI : IsIso κ := by
      haveI : IsIso (G.map κ) := by rw [hκ]; infer_instance
      exact isIso_of_fully_faithful G κ
    let X : Fib Φ₁ B₁ divB₁ A := ⟨Φ₁.pb (inv κ) W.α⟩
    let ι : X.toModel ⟶ W := mk1 (inv κ) 0 (Φ₁.pos _).zero_mem 0 (by simp [X])
    haveI : IsIso ι := isIso_of _ rfl (by simp only [ι, mk1_base]; infer_instance) rfl
    let i : (resObj Ψ G η X).toModel ≅ Z.toModel :=
      asIso (resRho Ψ G η X) ≪≫ Ψ.mapIso (asIso ι) ≪≫ e
    refine ⟨X, ⟨Fib.isoMk i ?_⟩⟩
    have hn := ηb_natural Ψ G η ι
    simp only [i, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, comp_base, resRho_base]
    have hι : ι.base = inv κ := rfl
    rw [hι, Functor.map_inv] at hn
    have h3 : (Ψ.map ι).base = (ηb Ψ G η X.toModel).hom ≫ inv (G.map κ) ≫ (ηb Ψ G η W).inv := by
      rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h3]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [show (ηb Ψ G η W).inv ≫ e.hom.base = κ' from rfl, ← hκ, IsIso.inv_hom_id]

/-- **The restriction of an equivalence lying over a fully faithful base functor is an
equivalence.** -/
instance resFib_isEquivalence [Ψ.IsEquivalence] [G.Full] [G.Faithful] :
    (resFib Ψ G η (A := A)).IsEquivalence where

end Res

end Model

end Frobenioid

end Iut
