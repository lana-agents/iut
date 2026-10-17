/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Defs

/-!
# Base equivalences of equivalences of Frobenioids

[FrdII], Theorem 2.4: an equivalence `Ψ : C₁ ≌ C₂` of `p`-adic Frobenioids "necessarily induces a
1-compatible equivalence of categories `Ψ_Base : D₁ ≌ D₂`, hence an outer isomorphism of
topological groups". This file supplies the two missing links between `PreservesBase`
(`Model.thm34_galois_preservesBase`, [FrdI] Theorem 3.4(v)) and
`OrbitObj.exists_continuousMulEquiv` (`GaloisRecon.lean`):

* `Frobenioid.natural_of_whisker`, `Frobenioid.isoOfWhisker`: for a Frobenioid `P : C → F_Φ` with
  base functor `L : C → D`, a natural transformation `L ⋙ H ⟶ L ⋙ K` is natural with respect to
  *every* morphism of `D` between bases, and a natural isomorphism `L ⋙ H ≅ L ⋙ K` descends to
  `H ≅ K` ([FrdI], Definition 1.3(i)(a)–(c): every object of `D` is a base, pre-step spans, and
  pull-backs);
* `Frobenioid.isEquivalence_base`: if an equivalence `F` and its inverse both preserve the base
  (`F ⋙ L₂ ≅ L₁ ⋙ G`, `F⁻¹ ⋙ L₁ ≅ L₂ ⋙ G'`), then `G` is an equivalence;

Application: `PAdicRecon.lean` (`G_E ≅ G_{E'}` from `C^⊢(E) ≌ C^⊢(E')`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u v' u'

section Descent

variable {D : Type u} [Category.{v} D] {Φ : DivMonoid.{w} D}
variable {C : Type u'} [Category.{v'} C] {P : C ⥤ Elem Φ}

/-- The component `H(Base A) → K(Base A)` of a transformation `L ⋙ H ⟶ L ⋙ K`. -/
def etaApp {E : Type*} [Category E] {H K : D ⥤ E}
    (η : (P ⋙ Elem.proj) ⋙ H ⟶ (P ⋙ Elem.proj) ⋙ K) (A : C) :
    H.obj ((P ⋙ Elem.proj).obj A) ⟶ K.obj ((P ⋙ Elem.proj).obj A) :=
  η.app A

/-- The component `H(Base A) ≅ K(Base A)` of an isomorphism `L ⋙ H ≅ L ⋙ K`. -/
def etaIso {E : Type*} [Category E] {H K : D ⥤ E}
    (η : (P ⋙ Elem.proj) ⋙ H ≅ (P ⋙ Elem.proj) ⋙ K) (A : C) :
    H.obj ((P ⋙ Elem.proj).obj A) ≅ K.obj ((P ⋙ Elem.proj).obj A) :=
  η.app A

lemma etaIso_hom {E : Type*} [Category E] {H K : D ⥤ E}
    (η : (P ⋙ Elem.proj) ⋙ H ≅ (P ⋙ Elem.proj) ⋙ K) (A : C) :
    (etaIso η A).hom = etaApp η.hom A := rfl

/-- **Naturality along arbitrary base morphisms**: a natural transformation `L ⋙ H ⟶ L ⋙ K`
(`L = Base`) commutes with every morphism `f : Base(A) → Base(A')` of `D`. -/
lemma natural_of_whisker (hP : IsFrobenioid P) {E : Type*} [Category E] {H K : D ⥤ E}
    (η : (P ⋙ Elem.proj) ⋙ H ⟶ (P ⋙ Elem.proj) ⋙ K) {A A' : C}
    (f : (P ⋙ Elem.proj).obj A ⟶ (P ⋙ Elem.proj).obj A') :
    H.map f ≫ etaApp η A' = etaApp η A ≫ K.map f := by
  obtain ⟨B, φ, e, -, he⟩ := hP.pullback_surj A' (base P A) f
  obtain ⟨E', φ₁, ψ₁, -, hψ₁, hb⟩ := hP.preStep_span B A e
  haveI : IsIso ((P ⋙ Elem.proj).map ψ₁) := hψ₁.2
  have n1 : H.map ((P ⋙ Elem.proj).map ψ₁) ≫ etaApp η A =
      etaApp η E' ≫ K.map ((P ⋙ Elem.proj).map ψ₁) := η.naturality ψ₁
  have n2 : H.map ((P ⋙ Elem.proj).map (φ₁ ≫ φ)) ≫ etaApp η A' =
      etaApp η E' ≫ K.map ((P ⋙ Elem.proj).map (φ₁ ≫ φ)) := η.naturality (φ₁ ≫ φ)
  have hb2 : (P ⋙ Elem.proj).map (φ₁ ≫ φ) = (P ⋙ Elem.proj).map ψ₁ ≫ f := by
    change Base P (φ₁ ≫ φ) = Base P ψ₁ ≫ f
    rw [Base_comp, ← he, ← Category.assoc, hb]
    rfl
  rw [hb2, H.map_comp, K.map_comp, Category.assoc] at n2
  rw [← cancel_epi (H.map ((P ⋙ Elem.proj).map ψ₁)), n2, ← Category.assoc, ← n1,
    Category.assoc]

/-- A chosen base `A_X` over `X` with `e_X : Base(A_X) ≅ X` (Definition 1.3(i)(a)). -/
noncomputable def baseIso (hP : IsFrobenioid P) (X : D) :
    (P ⋙ Elem.proj).obj (hP.base_surj X).choose ≅ X :=
  (hP.base_surj X).choose_spec.2.some

/-- **Descent of natural isomorphisms along the base functor** of a Frobenioid. -/
noncomputable def isoOfWhisker (hP : IsFrobenioid P) {E : Type*} [Category E] {H K : D ⥤ E}
    (η : (P ⋙ Elem.proj) ⋙ H ≅ (P ⋙ Elem.proj) ⋙ K) : H ≅ K :=
  NatIso.ofComponents
    (fun X => H.mapIso (baseIso hP X).symm ≪≫ etaIso η (hP.base_surj X).choose ≪≫
      K.mapIso (baseIso hP X))
    (fun {X Y} f => by
      have hn := natural_of_whisker hP η.hom ((baseIso hP X).hom ≫ f ≫ (baseIso hP Y).inv)
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, etaIso_hom, Category.assoc]
      have h1 : H.map f ≫ H.map (baseIso hP Y).inv = H.map (baseIso hP X).inv ≫
          H.map ((baseIso hP X).hom ≫ f ≫ (baseIso hP Y).inv) := by
        rw [← H.map_comp, ← H.map_comp, Iso.inv_hom_id_assoc]
      rw [← Category.assoc (H.map f), h1, Category.assoc, reassoc_of% hn]
      simp only [Category.assoc, ← K.map_comp, Iso.inv_hom_id, Category.comp_id])

variable {D₂ : Type*} [Category D₂] {Φ₂ : DivMonoid D₂}
variable {C₂ : Type*} [Category C₂] {P₂ : C₂ ⥤ Elem Φ₂}

/-- **The base functor of an equivalence of Frobenioids is an equivalence**, provided the
equivalence and its inverse preserve the base. -/
theorem isEquivalence_base (hP : IsFrobenioid P) (hP₂ : IsFrobenioid P₂) (F : C ⥤ C₂)
    [F.IsEquivalence] (G : D ⥤ D₂) (G' : D₂ ⥤ D)
    (hG : F ⋙ P₂ ⋙ Elem.proj ≅ (P ⋙ Elem.proj) ⋙ G)
    (hG' : F.inv ⋙ P ⋙ Elem.proj ≅ (P₂ ⋙ Elem.proj) ⋙ G') : G.IsEquivalence := by
  let L := P ⋙ Elem.proj
  let L₂ := P₂ ⋙ Elem.proj
  -- `L ⋙ G ⋙ G' ≅ L` and `L₂ ⋙ G' ⋙ G ≅ L₂`
  let u : L ⋙ (G ⋙ G') ≅ L ⋙ 𝟭 D :=
    (Functor.associator L G G').symm ≪≫ Functor.isoWhiskerRight hG.symm G' ≪≫
      Functor.associator F L₂ G' ≪≫ Functor.isoWhiskerLeft F hG'.symm ≪≫
      (Functor.associator F F.inv L).symm ≪≫
      Functor.isoWhiskerRight F.asEquivalence.unitIso.symm L ≪≫ Functor.leftUnitor L ≪≫
      (Functor.rightUnitor L).symm
  -- for the other composite, `F⁻¹` preserves the base via `G'`, and `F` via `G`
  let c : L₂ ⋙ (G' ⋙ G) ≅ L₂ ⋙ 𝟭 D₂ :=
    (Functor.associator L₂ G' G).symm ≪≫ Functor.isoWhiskerRight hG'.symm G ≪≫
      Functor.associator F.inv L G ≪≫ Functor.isoWhiskerLeft F.inv hG.symm ≪≫
      (Functor.associator F.inv F L₂).symm ≪≫
      Functor.isoWhiskerRight F.asEquivalence.counitIso L₂ ≪≫ Functor.leftUnitor L₂ ≪≫
      (Functor.rightUnitor L₂).symm
  exact (CategoryTheory.Equivalence.mk G G' (isoOfWhisker hP u).symm
    (isoOfWhisker hP₂ c)).isEquivalence_functor

end Descent


end Frobenioid

end Iut
