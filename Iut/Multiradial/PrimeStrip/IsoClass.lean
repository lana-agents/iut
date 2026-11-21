/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.Strip

/-!
# Isomorphism classes of isomorphisms of Frobenioids and prime-strips (MR21 R1)

IUT I, §0 (l.1965 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`):
"If `C` and `D` are categories, then we shall refer to as an isomorphism `C → D` any
isomorphism class of equivalences of categories `C → D`." The bijectivity statements of IUT I,
Corollary 5.3 (ii), (iii) (l.9891–9898) are about these classes. This file sets up the classes:

* `CatIsom C D`: equivalences `C ≌ D` modulo natural isomorphism of their functors, with
  identity, inverse and composite (`CatIsom.refl`, `CatIsom.symm`, `CatIsom.trans`);
* `FrobCat.Iso.Hom2 f g`: a **2-isomorphism** of isomorphisms of Frobenioids
  `f g : X.Iso Y` (`FrobCat.Iso` of `Strip.lean`): natural isomorphisms of the functors of
  Frobenioids and of the functors of base categories such that the isomorphisms of divisor
  monoids correspond through the pull-back along the base component
  (`φ_f(x) = β^*(φ_g(x))`). The base equivalence and the divisor-monoid isomorphisms are data of
  `FrobCat.Iso` (they are determined by the equivalence of Frobenioids only through the
  category-theoretic reconstruction of the base, which needs the slimness of `Π_v`, not available);
  a 2-isomorphism therefore relates all three components;
* `FrobCat.IsoClass X Y`: isomorphisms modulo 2-isomorphism; the groupoid laws hold up to
  2-isomorphism (`Hom2.assoc`, `Hom2.reflTrans`, `Hom2.transRefl`, `Hom2.transSymm`,
  `Hom2.symmTrans`, the horizontal composite `Hom2.hcomp`), so the classes form a groupoid
  (`IsoClass.refl`, `IsoClass.symm`, `IsoClass.trans`);
* **`F ↦ D` on classes** (`FrobCat.IsoClass.toD`, the map of Corollary 5.3 (ii) at one
  constituent), compatible with identities, inverses and composites, and the **reduction of
  injectivity to automorphisms** (`FrobCat.IsoClass.toD_injective_of_aut`): if every
  automorphism of `X` whose base functor is isomorphic to the identity is 2-isomorphic to the
  identity, then `toD` is injective on `IsoClass X Y` for every `Y`; and its invariance under
  isomorphism (`FrobCat.autRigid_of_iso`), so that the condition need only be checked on the
  models `C_v`;
* the same for split Frobenioids (`SplitFrobCat.IsoClass`) and for the non-archimedean parts of
  `D`-, `D^⊢`-, `F`-, `F^⊢`-prime-strips (`DStripNon.IsoClass`, `FStripNon.IsoClass`,
  `FStripNon.isoClassToD` etc.: constituentwise classes, Definition 4.1 (iv), 5.2 (iii)).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory NumberField Iut.Frobenioid

universe u v u' v'

/-! ### Isomorphisms of categories in the sense of IUT I, §0 -/

section CatIsom

variable (C : Type u) [Category.{v} C] (E : Type u') [Category.{v'} E]

/-- Two equivalences are identified if their functors are naturally isomorphic. -/
def equivSetoid : Setoid (C ≌ E) where
  r e e' := Nonempty (e.functor ≅ e'.functor)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨a⟩ => ⟨a.symm⟩, fun ⟨a⟩ ⟨b⟩ => ⟨a ≪≫ b⟩⟩

/-- **An isomorphism `C → E` in the sense of IUT I, §0**: an isomorphism class of equivalences
of categories `C ≌ E`. -/
def CatIsom : Type _ := Quotient (equivSetoid C E)

variable {C E}

/-- The class of an equivalence. -/
def CatIsom.mk (e : C ≌ E) : CatIsom C E := Quotient.mk (equivSetoid C E) e

lemma CatIsom.mk_eq_mk {e e' : C ≌ E} : CatIsom.mk e = CatIsom.mk e' ↔
    Nonempty (e.functor ≅ e'.functor) :=
  Quotient.eq (r := equivSetoid C E)

lemma CatIsom.mk_surjective : Function.Surjective (CatIsom.mk : (C ≌ E) → CatIsom C E) :=
  Quotient.mk_surjective

/-- The identity. -/
def CatIsom.refl (C : Type u) [Category.{v} C] : CatIsom C C :=
  CatIsom.mk CategoryTheory.Equivalence.refl

/-- The inverse. -/
def CatIsom.symm : CatIsom C E → CatIsom E C :=
  Quotient.map (sa := equivSetoid C E) (sb := equivSetoid E C) (fun e => e.symm)
    fun _ _ ⟨a⟩ => ⟨CategoryTheory.Iso.isoInverseOfIsoFunctor a⟩

/-- The composite. -/
def CatIsom.trans {F : Type*} [Category* F] : CatIsom C E → CatIsom E F → CatIsom C F :=
  Quotient.map₂ (sa := equivSetoid C E) (sb := equivSetoid E F) (sc := equivSetoid C F)
    (fun e e' => e.trans e') fun _ _ ⟨a⟩ _ _ ⟨b⟩ => ⟨Functor.isoWhiskerRight a _ ≪≫
      Functor.isoWhiskerLeft _ b⟩

@[simp] lemma CatIsom.symm_mk (e : C ≌ E) : (CatIsom.mk e).symm = CatIsom.mk e.symm := rfl

@[simp] lemma CatIsom.trans_mk {F : Type*} [Category* F] (e : C ≌ E) (e' : E ≌ F) :
    (CatIsom.mk e).trans (CatIsom.mk e') = CatIsom.mk (e.trans e') := rfl

end CatIsom

/-! ### 2-isomorphisms of isomorphisms of Frobenioids -/

namespace FrobCat

/-- **Naturality of `elemIsoOfBase (β_A) : F_E(A) ≅ F_{E'}(A)`** for a natural isomorphism
`β : E ≅ E'` of base functors with `β^* ∘ φ' = φ`. -/
lemma elemIsoOfBase_nat {D₁ D₂ : Type} [Category.{0} D₁] [Category.{0} D₂]
    {Φ : DivMonoid.{0} D₁} {Ψ : DivMonoid.{0} D₂} {E E' : D₁ ⥤ D₂}
    {φ : ∀ A, Φ.obj A ≃+ Ψ.obj (E.obj A)} {φ' : ∀ A, Φ.obj A ≃+ Ψ.obj (E'.obj A)}
    {hpos : ∀ A x, x ∈ Φ.pos A ↔ φ A x ∈ Ψ.pos (E.obj A)}
    {hpos' : ∀ A x, x ∈ Φ.pos A ↔ φ' A x ∈ Ψ.pos (E'.obj A)}
    {hpb : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ A (Φ.pb g x) = Ψ.pb (E.map g) (φ B x)}
    {hpb' : ∀ {A B : D₁} (g : A ⟶ B) (x : Φ.obj B), φ' A (Φ.pb g x) = Ψ.pb (E'.map g) (φ' B x)}
    (β : E ≅ E') (hφ : ∀ (A : D₁) (x : Φ.obj A), Ψ.pb (β.hom.app A) (φ' A x) = φ A x)
    {b c : Elem Φ} (x : b ⟶ c) :
    (elemMap E φ hpos hpb).map x ≫
      (elemIsoOfBase (A := (elemMap E φ hpos hpb).obj c)
        (B := (elemMap E' φ' hpos' hpb').obj c) (β.app c.base)).hom =
    (elemIsoOfBase (A := (elemMap E φ hpos hpb).obj b)
        (B := (elemMap E' φ' hpos' hpb').obj b) (β.app b.base)).hom ≫
      (elemMap E' φ' hpos' hpb').map x :=
  Elem.hom_ext (β.hom.naturality x.base) (by
      change Ψ.pb (E.map x.base) (0 : Ψ.obj (E.obj c.base)) + ((1 : ℕ+) : ℕ) • φ b.base x.div =
        Ψ.pb (β.hom.app b.base) (φ' b.base x.div) + (x.deg : ℕ) • (0 : Ψ.obj (E.obj b.base))
      rw [map_zero, zero_add, PNat.one_coe, one_smul, smul_zero, add_zero, hφ])
    (by simp [elemIsoOfBase, elemMap, mul_comm])

section Squares

variable {C₀ : Type*} [Category* C₀]

lemma sq_inv {a b c d : C₀} (I : a ≅ b) (K : c ≅ d) {cf : a ⟶ c} {cg : b ⟶ d}
    (h : I.hom ≫ cg = cf ≫ K.hom) : I.inv ≫ cf = cg ≫ K.inv := by
  rw [CategoryTheory.Iso.inv_comp_eq, ← Category.assoc, CategoryTheory.Iso.eq_comp_inv]
  exact h.symm

lemma sq_vcomp {o1 o2 o3 o4 o5 o6 : C₀} {I : o1 ⟶ o3} {I1 : o1 ⟶ o2} {I2 : o2 ⟶ o3}
    {ch : o3 ⟶ o6} {cg : o2 ⟶ o5} {cf : o1 ⟶ o4} {K : o4 ⟶ o6} {Ka : o4 ⟶ o5} {Kb : o5 ⟶ o6}
    (hI : I = I1 ≫ I2) (hK : K = Ka ≫ Kb) (ha : I1 ≫ cg = cf ≫ Ka) (hb : I2 ≫ ch = cg ≫ Kb) :
    I ≫ ch = cf ≫ K := by
  subst hI hK
  rw [Category.assoc, hb, reassoc_of% ha]

lemma sq_hcomp {o1 o2 o3 o4 o5 o6 o7 o8 o9 : C₀}
    {R0 : o1 ⟶ o3} {r1 : o1 ⟶ o2} {r2 : o2 ⟶ o3} (hR : R0 = r1 ≫ r2)
    {L : o3 ⟶ o7} {c' : o3 ⟶ o4} {x : o4 ⟶ o7} (hL : L = c' ≫ x)
    {M : o1 ⟶ o6} {p : o1 ⟶ o5} {q : o5 ⟶ o6} (hM : M = p ≫ q)
    {K : o6 ⟶ o7} {k1 : o6 ⟶ o8} {k2 : o8 ⟶ o7} (hK : K = k1 ≫ k2)
    {P2 : o2 ⟶ o9} {Kb : o9 ⟶ o4} {y : o5 ⟶ o9} {z : o9 ⟶ o8}
    (hb : r2 ≫ c' = P2 ≫ Kb) (hP : r1 ≫ P2 = p ≫ y) (hz : z ≫ k2 = Kb ≫ x)
    (ha : y ≫ z = q ≫ k1) : R0 ≫ L = M ≫ K := by
  subst hR hL hM hK
  simp only [Category.assoc]
  rw [reassoc_of% hb, reassoc_of% hP, ← hz, reassoc_of% ha]

lemma sq_id_assoc {o1 o2 o3 o4 : C₀} {i1 : o1 ⟶ o1} {i2 : o4 ⟶ o4} {a : o1 ⟶ o2}
    {b : o2 ⟶ o3} {c : o3 ⟶ o4} {m : o2 ⟶ o4} (hi1 : i1 = 𝟙 _) (hi2 : i2 = 𝟙 _)
    (hm : m = b ≫ c) : i1 ≫ ((a ≫ b) ≫ c) = (a ≫ m) ≫ i2 := by
  subst hi1 hi2 hm
  simp

lemma sq_id_r {o1 o2 : C₀} {i1 : o1 ⟶ o1} {i2 : o2 ⟶ o2} {x : o1 ⟶ o2} {y : o2 ⟶ o2}
    (hi1 : i1 = 𝟙 _) (hi2 : i2 = 𝟙 _) (hy : y = 𝟙 _) : i1 ≫ x = (x ≫ y) ≫ i2 := by
  subst hi1 hi2 hy
  simp

lemma sq_id_l {o1 o2 : C₀} {i1 : o1 ⟶ o1} {i2 : o2 ⟶ o2} {i0 : o1 ⟶ o1} {x : o1 ⟶ o2}
    (hi1 : i1 = 𝟙 _) (hi2 : i2 = 𝟙 _) (hi0 : i0 = 𝟙 _) : i1 ≫ x = (i0 ≫ x) ≫ i2 := by
  subst hi1 hi2 hi0
  simp

lemma sq_coh {a b c d : C₀} {p : a ⟶ b} {q : b ⟶ c} {r : c ⟶ d} {s : a ⟶ d} {i : d ⟶ d}
    (hi : i = 𝟙 _) (h : p ≫ q ≫ r = s) : s ≫ i = (p ≫ q) ≫ r := by
  subst hi
  rw [Category.comp_id, ← h, Category.assoc]

end Squares

namespace Iso

/-- **A 2-isomorphism `f ⟹ g` of isomorphisms of Frobenioids**: natural isomorphisms of the
functors of Frobenioids and of base categories, such that the isomorphisms of divisor monoids
correspond through the pull-back along the base component (`φ_f(x) = β_A^*(φ_g(x))`) and the
squares `commP` correspond through `α` and `β`
(`P'(α_A) ≫ commP_g(A) = commP_f(A) ≫ (β_{A_D}, 0, 1)`). -/
structure Hom2 {X Y : FrobCat} (f g : X.Iso Y) where
  /-- The natural isomorphism of the functors of Frobenioids. -/
  α : f.C.functor ≅ g.C.functor
  /-- The natural isomorphism of the functors of base categories. -/
  β : f.D.functor ≅ g.D.functor
  /-- The divisor-monoid isomorphisms correspond through `β`. -/
  phi_compat : ∀ (A : X.D) (x : X.Φ.obj A), Y.Φ.pb (β.hom.app A) (g.phi A x) = f.phi A x
  /-- The squares `commP` correspond through `α` and `β`. -/
  commP_compat : ∀ A : X.C, Y.P.map (α.hom.app A) ≫ (sqIso g.commP).hom.app A =
    (sqIso f.commP).hom.app A ≫
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj (X.P.obj A))
        (B := (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj (X.P.obj A))
        (β.app (X.P.obj A).base)).hom

namespace Hom2

variable {X Y Z W : FrobCat}

/-- The identity 2-isomorphism. -/
def id (f : X.Iso Y) : Hom2 f f :=
  ⟨CategoryTheory.Iso.refl _, CategoryTheory.Iso.refl _, fun _ _ => Y.Φ.pb_id _ _,
    fun _ => ((congrArg (· ≫ _) (Y.P.map_id _)).trans (Category.id_comp _)).trans
      (Category.comp_id _).symm⟩

/-- The inverse 2-isomorphism. -/
def symm {f g : X.Iso Y} (a : Hom2 f g) : Hom2 g f where
  α := a.α.symm
  β := a.β.symm
  phi_compat A x := by
    rw [← a.phi_compat A x, ← GrpOn.pb_comp']
    exact ((congrArg (fun h => Y.Φ.pb h (g.phi A x)) (a.β.inv_hom_id_app A)).trans
      (Y.Φ.pb_id _ _))
  commP_compat A := sq_inv (Y.P.mapIso (a.α.app A))
    (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj (X.P.obj A))
      (B := (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj (X.P.obj A))
      (a.β.app (X.P.obj A).base)) (a.commP_compat A)

/-- The vertical composite. -/
def vcomp {f g h : X.Iso Y} (a : Hom2 f g) (b : Hom2 g h) : Hom2 f h where
  α := a.α ≪≫ b.α
  β := a.β ≪≫ b.β
  phi_compat A x := by
    simp only [Iso.trans_hom, NatTrans.comp_app, GrpOn.pb_comp', b.phi_compat, a.phi_compat]
  commP_compat A := sq_vcomp (Y.P.map_comp (a.α.hom.app A) (b.α.hom.app A))
    (elemIsoOfBase_comp (a.β.app (X.P.obj A).base) (b.β.app (X.P.obj A).base)).symm
    (a.commP_compat A) (b.commP_compat A)

/-- The horizontal composite. -/
def hcomp {f f' : X.Iso Y} {g g' : Y.Iso Z} (a : Hom2 f f') (b : Hom2 g g') :
    Hom2 (f.trans g) (f'.trans g') where
  α := Functor.isoWhiskerRight a.α g.C.functor ≪≫ Functor.isoWhiskerLeft f'.C.functor b.α
  β := Functor.isoWhiskerRight a.β g.D.functor ≪≫ Functor.isoWhiskerLeft f'.D.functor b.β
  phi_compat A x := by
    change Z.Φ.pb (g.D.functor.map (a.β.hom.app A) ≫ b.β.hom.app (f'.D.functor.obj A))
      (g'.phi _ (f'.phi A x)) = g.phi _ (f.phi A x)
    rw [GrpOn.pb_comp', b.phi_compat, ← g.phi_pb, a.phi_compat]
  commP_compat A := sq_hcomp
    (Z.P.map_comp (g.C.functor.map (a.α.hom.app A)) (b.α.hom.app (f'.C.functor.obj A)))
    (transCommP_app f' g' A) (transCommP_app f g A)
    (Elem.hom_ext rfl (elemMap_comp_div_eq_zero (E := g.D.functor) (φ := g.phi)
      (hpos := g.phi_pos) (hpb := g.phi_pb)
      (elemIsoOfBase (A := (elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj (X.P.obj A))
        (B := (elemMap f'.D.functor f'.phi f'.phi_pos f'.phi_pb).obj (X.P.obj A))
        (a.β.app (X.P.obj A).base)).hom
      (elemIsoOfBase (A := (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
          ((elemMap f'.D.functor f'.phi f'.phi_pos f'.phi_pb).obj (X.P.obj A)))
        (B := (elemMap g'.D.functor g'.phi g'.phi_pos g'.phi_pb).obj
          ((elemMap f'.D.functor f'.phi f'.phi_pos f'.phi_pb).obj (X.P.obj A)))
        (b.β.app (f'.D.functor.obj (X.P.obj A).base))).hom rfl rfl rfl).symm rfl)
    (b.commP_compat (f'.C.functor.obj A))
    ((sqIso g.commP).hom.naturality (a.α.hom.app A))
    (elemIsoOfBase_nat b.β b.phi_compat ((sqIso f'.commP).hom.app A))
    (((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _).symm.trans
      ((congrArg (elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map (a.commP_compat A)).trans
        ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map_comp _ _)))

/-- Associativity of composites. -/
def assoc (f : X.Iso Y) (g : Y.Iso Z) (h : Z.Iso W) :
    Hom2 ((f.trans g).trans h) (f.trans (g.trans h)) where
  α := Functor.associator _ _ _
  β := Functor.associator _ _ _
  phi_compat _ _ := W.Φ.pb_id _ _
  commP_compat A := sq_id_assoc (W.P.map_id _) rfl
    (CategoryTheory.Functor.map_comp (elemMap h.D.functor h.phi h.phi_pos h.phi_pb)
      ((sqIso g.commP).hom.app (f.C.functor.obj A))
      ((elemMap g.D.functor g.phi g.phi_pos g.phi_pb).map ((sqIso f.commP).hom.app A)))

/-- The identity is a left unit. -/
def reflTrans (f : X.Iso Y) : Hom2 ((FrobCat.Iso.refl X).trans f) f where
  α := Functor.leftUnitor _
  β := Functor.leftUnitor _
  phi_compat _ _ := Y.Φ.pb_id _ _
  commP_compat A := sq_id_r (Y.P.map_id _) rfl
    (CategoryTheory.Functor.map_id (elemMap f.D.functor f.phi f.phi_pos f.phi_pb) (X.P.obj A))

/-- The identity is a right unit. -/
def transRefl (f : X.Iso Y) : Hom2 (f.trans (FrobCat.Iso.refl Y)) f where
  α := Functor.rightUnitor _
  β := Functor.rightUnitor _
  phi_compat _ _ := Y.Φ.pb_id _ _
  commP_compat _ := sq_id_l (Y.P.map_id _) rfl rfl

/-- `f⁻¹ ∘ f` is the identity, through the unit of the equivalences. -/
def transSymm (f : X.Iso Y) : Hom2 (f.trans f.symm) (FrobCat.Iso.refl X) where
  α := f.C.unitIso.symm
  β := f.D.unitIso.symm
  phi_compat A x := (phiInv_phi f A x).symm
  commP_compat A := sq_coh rfl (f.commP_unit A)

/-- `f ∘ f⁻¹` is the identity, through the counit of the equivalences. -/
def symmTrans (f : X.Iso Y) : Hom2 (f.symm.trans f) (FrobCat.Iso.refl Y) where
  α := f.C.counitIso
  β := f.D.counitIso
  phi_compat B y := (phi_phiInv f B y).symm
  commP_compat B := sq_coh rfl (f.commP_counit B)

end Hom2

/-- The relation "2-isomorphic". -/
def Rel {X Y : FrobCat} (f g : X.Iso Y) : Prop := Nonempty (Hom2 f g)

namespace Rel

variable {X Y Z W : FrobCat}

lemma refl (f : X.Iso Y) : Rel f f := ⟨Hom2.id f⟩

lemma symm {f g : X.Iso Y} (h : Rel f g) : Rel g f := h.map Hom2.symm

lemma trans {f g h : X.Iso Y} (a : Rel f g) (b : Rel g h) : Rel f h :=
  a.elim fun a => b.elim fun b => ⟨a.vcomp b⟩

lemma hcomp {f f' : X.Iso Y} {g g' : Y.Iso Z} (a : Rel f f') (b : Rel g g') :
    Rel (f.trans g) (f'.trans g') :=
  a.elim fun a => b.elim fun b => ⟨a.hcomp b⟩

lemma assoc (f : X.Iso Y) (g : Y.Iso Z) (h : Z.Iso W) :
    Rel ((f.trans g).trans h) (f.trans (g.trans h)) := ⟨Hom2.assoc f g h⟩

lemma reflTrans (f : X.Iso Y) : Rel ((FrobCat.Iso.refl X).trans f) f := ⟨Hom2.reflTrans f⟩

lemma transRefl (f : X.Iso Y) : Rel (f.trans (FrobCat.Iso.refl Y)) f := ⟨Hom2.transRefl f⟩

lemma transSymm (f : X.Iso Y) : Rel (f.trans f.symm) (FrobCat.Iso.refl X) :=
  ⟨Hom2.transSymm f⟩

lemma symmTrans (f : X.Iso Y) : Rel (f.symm.trans f) (FrobCat.Iso.refl Y) :=
  ⟨Hom2.symmTrans f⟩

/-- 2-isomorphic isomorphisms have 2-isomorphic inverses (from the groupoid laws). -/
lemma symm_iso {f g : X.Iso Y} (a : Rel f g) : Rel f.symm g.symm := by
  -- `f⁻¹ ≈ f⁻¹ (g g⁻¹) ≈ (f⁻¹ g) g⁻¹ ≈ (f⁻¹ f) g⁻¹ ≈ g⁻¹`
  refine ((transRefl f.symm).symm.trans ((Rel.refl f.symm).hcomp (transSymm g).symm)).trans ?_
  refine (assoc _ _ _).symm.trans ?_
  refine (((Rel.refl f.symm).hcomp a.symm).hcomp (Rel.refl g.symm)).trans ?_
  exact ((symmTrans f).hcomp (Rel.refl g.symm)).trans (reflTrans g.symm)

/-- `f ≈ g` as soon as `g⁻¹ ∘ f ≈ id` (from the groupoid laws). -/
lemma of_trans_symm {f g : X.Iso Y} (h : Rel (f.trans g.symm) (FrobCat.Iso.refl X)) :
    Rel f g := by
  -- `f ≈ f (g⁻¹ g) ≈ (f g⁻¹) g ≈ id g ≈ g`
  refine (transRefl f).symm.trans ?_
  refine ((Rel.refl f).hcomp (symmTrans g).symm).trans ?_
  refine (assoc _ _ _).symm.trans ?_
  exact (h.hcomp (Rel.refl g)).trans (reflTrans g)

end Rel

/-- The setoid of 2-isomorphism. -/
def setoid (X Y : FrobCat) : Setoid (X.Iso Y) where
  r := Rel
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

end Iso

/-- **Isomorphisms of Frobenioids in the sense of IUT I, §0**: isomorphisms of Frobenioids
(`FrobCat.Iso`) modulo 2-isomorphism. -/
def IsoClass (X Y : FrobCat) : Type := Quotient (Iso.setoid X Y)

namespace IsoClass

variable {X Y Z : FrobCat}

/-- The class of an isomorphism. -/
def mk (f : X.Iso Y) : IsoClass X Y := Quotient.mk (Iso.setoid X Y) f

lemma mk_eq_mk {f g : X.Iso Y} : mk f = mk g ↔ Iso.Rel f g :=
  Quotient.eq (r := Iso.setoid X Y)

lemma mk_surjective : Function.Surjective (mk : X.Iso Y → IsoClass X Y) :=
  Quotient.mk_surjective

/-- The identity. -/
def refl (X : FrobCat) : IsoClass X X := mk (Iso.refl X)

/-- The inverse. -/
def symm : IsoClass X Y → IsoClass Y X :=
  Quotient.map (sa := Iso.setoid X Y) (sb := Iso.setoid Y X) Iso.symm
    fun _ _ h => Iso.Rel.symm_iso h

/-- The composite. -/
def trans : IsoClass X Y → IsoClass Y Z → IsoClass X Z :=
  Quotient.map₂ (sa := Iso.setoid X Y) (sb := Iso.setoid Y Z) (sc := Iso.setoid X Z) Iso.trans
    fun _ _ a _ _ b => Iso.Rel.hcomp a b

@[simp] lemma symm_mk (f : X.Iso Y) : (mk f).symm = mk f.symm := rfl

@[simp] lemma trans_mk (f : X.Iso Y) (g : Y.Iso Z) : (mk f).trans (mk g) = mk (f.trans g) := rfl

lemma trans_assoc {W : FrobCat} (a : IsoClass X Y) (b : IsoClass Y Z) (c : IsoClass Z W) :
    (a.trans b).trans c = a.trans (b.trans c) := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  obtain ⟨h, rfl⟩ := mk_surjective c
  exact mk_eq_mk.2 (Iso.Rel.assoc f g h)

lemma refl_trans (a : IsoClass X Y) : (refl X).trans a = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (Iso.Rel.reflTrans f)

lemma trans_refl (a : IsoClass X Y) : a.trans (refl Y) = a := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (Iso.Rel.transRefl f)

lemma trans_symm (a : IsoClass X Y) : a.trans a.symm = refl X := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (Iso.Rel.transSymm f)

lemma symm_trans (a : IsoClass X Y) : a.symm.trans a = refl Y := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  exact mk_eq_mk.2 (Iso.Rel.symmTrans f)

/-- **`F ↦ D` on isomorphism classes** (IUT I, Remark 5.2.1 (i); the map of Corollary 5.3 (ii)
at one constituent): the class of the base equivalence. -/
def toD : IsoClass X Y → CatIsom X.D Y.D :=
  Quotient.map (sa := Iso.setoid X Y) (sb := equivSetoid X.D Y.D) (fun f => f.D)
    fun _ _ h => h.elim fun a => ⟨a.β⟩

@[simp] lemma toD_mk (f : X.Iso Y) : (mk f).toD = CatIsom.mk f.D := rfl

lemma toD_refl : (refl X).toD = CatIsom.refl X.D := rfl

lemma toD_symm (a : IsoClass X Y) : a.symm.toD = a.toD.symm := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  rfl

lemma toD_trans (a : IsoClass X Y) (b : IsoClass Y Z) : (a.trans b).toD = a.toD.trans b.toD := by
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  rfl

/-- **Reduction of the injectivity of `F ↦ D` to automorphisms**: if every automorphism of `X`
whose base functor is isomorphic to the identity is 2-isomorphic to the identity, then `F ↦ D`
is injective on `IsoClass X Y`. -/
theorem toD_injective_of_aut
    (haut : ∀ h : X.Iso X, Nonempty (h.D.functor ≅ 𝟭 X.D) → Iso.Rel h (Iso.refl X)) :
    Function.Injective (toD : IsoClass X Y → CatIsom X.D Y.D) := by
  intro a b hab
  obtain ⟨f, rfl⟩ := mk_surjective a
  obtain ⟨g, rfl⟩ := mk_surjective b
  obtain ⟨β⟩ := CatIsom.mk_eq_mk.1 hab
  refine mk_eq_mk.2 (Iso.Rel.of_trans_symm (haut _ ⟨?_⟩))
  exact Functor.isoWhiskerRight β g.D.inverse ≪≫ g.D.unitIso.symm

end IsoClass

/-- **Rigidity of automorphisms over the identity of the base**: every automorphism of `X` whose
base functor is isomorphic to the identity is 2-isomorphic to the identity. -/
def AutRigid (X : FrobCat) : Prop :=
  ∀ h : X.Iso X, Nonempty (h.D.functor ≅ 𝟭 X.D) → Iso.Rel h (Iso.refl X)

/-- `AutRigid` is invariant under isomorphism (conjugation), so it need only be checked on a
model. -/
theorem autRigid_of_iso {X Y : FrobCat} (m : X.Iso Y) (hY : AutRigid Y) : AutRigid X := by
  intro h ⟨β⟩
  -- the conjugate `m⁻¹ h m` of `h` lies over a functor isomorphic to the identity
  have hc : Iso.Rel ((m.symm.trans h).trans m) (Iso.refl Y) := hY _ ⟨Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft m.D.inverse β ≪≫ Functor.rightUnitor _) m.D.functor ≪≫
      m.D.counitIso⟩
  -- `h ≈ m (m⁻¹ h m) m⁻¹ ≈ m m⁻¹ ≈ id`
  have e1 : Iso.Rel h ((m.trans ((m.symm.trans h).trans m)).trans m.symm) := by
    refine (Iso.Rel.reflTrans h).symm.trans ?_
    refine ((Iso.Rel.transSymm m).symm.hcomp (Iso.Rel.refl h)).trans ?_
    refine (Iso.Rel.assoc _ _ _).trans ?_
    refine (Iso.Rel.transRefl _).symm.trans ?_
    refine ((Iso.Rel.refl _).hcomp (Iso.Rel.transSymm m).symm).trans ?_
    refine (Iso.Rel.assoc _ _ _).symm.trans ?_
    exact (Iso.Rel.assoc _ _ _).hcomp (Iso.Rel.refl _)
  refine e1.trans ?_
  refine (((Iso.Rel.refl m).hcomp hc).hcomp (Iso.Rel.refl m.symm)).trans ?_
  exact ((Iso.Rel.transRefl m).hcomp (Iso.Rel.refl m.symm)).trans (Iso.Rel.transSymm m)

theorem IsoClass.toD_injective {X Y : FrobCat} (hX : AutRigid X) :
    Function.Injective (IsoClass.toD : IsoClass X Y → CatIsom X.D Y.D) :=
  IsoClass.toD_injective_of_aut hX

end FrobCat

/-! ### Split Frobenioids -/

namespace SplitFrobCat

/-- The setoid of 2-isomorphism of the underlying isomorphisms of Frobenioids. -/
def setoid (X Y : SplitFrobCat) : Setoid (X.Iso Y) where
  r f g := FrobCat.Iso.Rel f.iso g.iso
  iseqv := ⟨fun _ => FrobCat.Iso.Rel.refl _, FrobCat.Iso.Rel.symm, FrobCat.Iso.Rel.trans⟩

/-- **Isomorphisms of split Frobenioids in the sense of IUT I, §0.** -/
def IsoClass (X Y : SplitFrobCat) : Type := Quotient (setoid X Y)

namespace IsoClass

variable {X Y Z : SplitFrobCat}

/-- The class of an isomorphism. -/
def mk (f : X.Iso Y) : IsoClass X Y := Quotient.mk (setoid X Y) f

lemma mk_surjective : Function.Surjective (mk : X.Iso Y → IsoClass X Y) :=
  Quotient.mk_surjective

/-- The inverse. -/
def symm : IsoClass X Y → IsoClass Y X :=
  Quotient.map (sa := setoid X Y) (sb := setoid Y X) Iso.symm
    fun _ _ h => FrobCat.Iso.Rel.symm_iso h

/-- The composite. -/
def trans : IsoClass X Y → IsoClass Y Z → IsoClass X Z :=
  Quotient.map₂ (sa := setoid X Y) (sb := setoid Y Z) (sc := setoid X Z) Iso.trans
    fun _ _ a _ _ b => FrobCat.Iso.Rel.hcomp a b

/-- **`F^⊢ ↦ D^⊢` on isomorphism classes** (the map of IUT I, Corollary 5.3 (iii) at one
constituent). -/
def toD : IsoClass X Y → CatIsom X.F.D Y.F.D :=
  Quotient.map (sa := setoid X Y) (sb := equivSetoid X.F.D Y.F.D) (fun f => f.iso.D)
    fun _ _ h => h.elim fun a => ⟨a.β⟩

@[simp] lemma toD_mk (f : X.Iso Y) : (mk f).toD = CatIsom.mk f.iso.D := rfl

end IsoClass

end SplitFrobCat

/-! ### Prime-strips -/

section Strips

variable {D : InitialThetaData.{0}}

/-- **Isomorphisms of `D`-prime-strips in the sense of IUT I, §0** (non-archimedean part):
constituentwise isomorphism classes of equivalences. -/
def DStripNon.IsoClass (P Q : DStripNon D) : Type := ∀ v, CatIsom (P.comp v).C (Q.comp v).C

/-- **Isomorphisms of `D^⊢`-prime-strips in the sense of IUT I, §0** (non-archimedean part). -/
def DVdashStripNon.IsoClass (P Q : DVdashStripNon D) : Type :=
  ∀ v, CatIsom (P.comp v).C (Q.comp v).C

/-- **Isomorphisms of `F`-prime-strips in the sense of IUT I, §0** (non-archimedean part):
constituentwise classes of isomorphisms of Frobenioids. -/
def FStripNon.IsoClass (P Q : FStripNon D) : Type := ∀ v, FrobCat.IsoClass (P.comp v).F (Q.comp v).F

/-- **Isomorphisms of `F^⊢`-prime-strips in the sense of IUT I, §0** (non-archimedean part). -/
def FVdashStripNon.IsoClass (P Q : FVdashStripNon D) : Type :=
  ∀ v, SplitFrobCat.IsoClass (P.comp v).F (Q.comp v).F

/-- The class of an isomorphism of `D`-prime-strips. -/
def DStripNon.Iso.cls {P Q : DStripNon D} (f : P.Iso Q) : P.IsoClass Q := fun v => CatIsom.mk (f v)

/-- The class of an isomorphism of `F`-prime-strips. -/
def FStripNon.Iso.cls {P Q : FStripNon D} (f : P.Iso Q) : P.IsoClass Q :=
  fun v => FrobCat.IsoClass.mk (f v)

/-- **The map `Isom(¹F, ²F) → Isom(¹D, ²D)` of IUT I, Corollary 5.3 (ii)** (non-archimedean
part). -/
def FStripNon.isoClassToD {P Q : FStripNon D} (a : P.IsoClass Q) : P.toD.IsoClass Q.toD :=
  fun v => (a v).toD

lemma FStripNon.isoClassToD_cls {P Q : FStripNon D} (f : P.Iso Q) :
    FStripNon.isoClassToD (FStripNon.Iso.cls f) = DStripNon.Iso.cls (FStripNon.isoToD f) := rfl

/-- **The map `Isom(¹F^⊢, ²F^⊢) → Isom(¹D^⊢, ²D^⊢)` of IUT I, Corollary 5.3 (iii)**
(non-archimedean part). -/
def FVdashStripNon.isoClassToD {P Q : FVdashStripNon D} (a : P.IsoClass Q) :
    P.toD.IsoClass Q.toD :=
  fun v => (a v).toD

/-- **Injectivity of `F ↦ D` on classes of isomorphisms of `F`-prime-strips from the rigidity of
the models**: if the model `C_v` (with base `D_v`) satisfies `AutRigid` at every `v ∈ V^non`,
then `Isom(¹F, ²F) → Isom(¹D, ²D)` is injective. -/
theorem FStripNon.isoClassToD_injective (hrig : ∀ v : Vnon D, (cvFrob D v).AutRigid)
    (P Q : FStripNon D) :
    Function.Injective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) := by
  intro a b hab
  funext v
  obtain ⟨m⟩ := (P.comp v).equiv_model
  exact FrobCat.IsoClass.toD_injective (FrobCat.autRigid_of_iso m (hrig v))
    (congrFun hab v)

end Strips

end PrimeStrip

end Multiradial

end Iut
