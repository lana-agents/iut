/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GaloisModel
import Iut.Frobenioid.ModelFrobenioid

/-!
# Changing the base category of a model Frobenioid along `B(Π)⁰ → B(G)⁰`

IUT I, Example 5.1 (i), (ii) (l.8234–8420 of `~/iut-scratch/papers/txt/Inter-universal
Teichmuller Theory I.txt`) builds the global Frobenioid `F^⊛` over `†D^⊛ = B(π₁(C_{F_mod}))⁰`:
to an object `A` it assigns the arithmetic divisors of the subfield of `F̄` corresponding to `A`,
through the action of `π₁(†D^⊛)` on `F̄` (which factors through `π₁(C_{F_mod}) ↠ Gal(F̄/F_mod)`).
This file provides the category-theoretic part:

* `OrbitObj.mapFunctor p hp : B(Π)⁰ ⥤ B(G)⁰`, `Π/U ↦ G/p(U)`, for a homomorphism `p : Π →* G`
  mapping open subgroups to open subgroups (e.g. a continuous surjection of a compact group onto a
  Hausdorff group, `isOpen_map_of_surjective`, or an open embedding);
* `GrpOn.comap`, `DivMonoid.comap`, `DivHom.comap`: monoids on `D` pulled back along a functor
  `P : D' ⥤ D` preserving FSM-morphisms (`isFSM_map_of_isIso`: on `B(Π)⁰` these are the
  isomorphisms);
* `Model.comapFunctor`: the model Frobenioid of the pulled-back data maps to the original one;
  the former is a Frobenioid over any connected, totally epimorphic base ([FrdI], Theorem
  5.2(ii), `Model.isFrobenioid`).
-/

noncomputable section

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v v' u u'

/-! ### Pulling back monoids along a functor -/

section Comap

variable {D' : Type u'} [Category.{v'} D'] {D : Type u} [Category.{v} D] (P : D' ⥤ D)
  (hP : ∀ {A B : D'} (f : A ⟶ B), IsFSM f → IsFSM (P.map f))

/-- The group-like monoid `B ∘ P` on `D'`. -/
def GrpOn.comap (B : GrpOn.{w} D) : GrpOn.{w} D' where
  obj A := B.obj (P.obj A)
  inst A := B.inst (P.obj A)
  pb f := B.pb (P.map f)
  pb_id A x := by rw [P.map_id]; exact B.pb_id _ x
  pb_comp f g x := by rw [P.map_comp]; exact B.pb_comp _ _ x
  pb_injective f := B.pb_injective _
  pb_bijective_of_fsm f hf := B.pb_bijective_of_fsm _ (hP f hf)

/-- The divisorial monoid `Φ ∘ P` on `D'`. -/
def DivMonoid.comap (Φ : DivMonoid.{w} D) : DivMonoid.{w} D' where
  toGrpOn := Φ.toGrpOn.comap P hP
  pos A := Φ.pos (P.obj A)
  pb_mem f _ hx := Φ.pb_mem (P.map f) hx
  sharp := Φ.sharp
  saturated n hn := Φ.saturated n hn
  generating x := Φ.generating x
  pos_surj_of_fsm f hf := Φ.pos_surj_of_fsm _ (hP f hf)

/-- The homomorphism `Div_B ∘ P`. -/
def DivHom.comap {B Φ : GrpOn.{w} D} (d : DivHom B Φ) : DivHom (B.comap P hP) (Φ.comap P hP) where
  app A := d.app (P.obj A)
  natural f x := d.natural (P.map f) x

variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

/-- **The change of base functor** from the model Frobenioid over `D'` of the pulled-back data to
the model Frobenioid over `D`: `(A, α) ↦ (P(A), α)`, the same degrees, zero divisors and rational
functions. -/
def Model.comapFunctor :
    Model (Φ.comap P hP) (B.comap P hP) (divB.comap P hP) ⥤ Model Φ B divB where
  obj X := ⟨P.obj X.base, X.α⟩
  map φ := ⟨φ.deg, P.map φ.base, φ.div, φ.div_mem, φ.u, φ.rel⟩
  map_id _ := Model.hom_ext rfl (P.map_id _) rfl rfl
  map_comp _ _ := Model.hom_ext rfl (P.map_comp _ _) rfl rfl

@[simp] lemma Model.comapFunctor_obj_base
    (X : Model (Φ.comap P hP) (B.comap P hP) (divB.comap P hP)) :
    ((Model.comapFunctor P hP).obj X).base = P.obj X.base := rfl

/-- The objects of a model Frobenioid over a fixed object `T` of the base. -/
abbrev Model.over (T : D) : ObjectProperty (Model Φ B divB) := fun X => X.base = T

omit [Category.{v'} D'] in
/-- The objects over equal objects of the base. -/
def Model.overEquivOfEq {T₁ T₂ : D} (h : T₁ = T₂) :
    (Model.over (Φ := Φ) (B := B) (divB := divB) T₁).FullSubcategory ≌
      (Model.over (Φ := Φ) (B := B) (divB := divB) T₂).FullSubcategory where
  functor := ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.2.trans h
  inverse := ObjectProperty.lift _ (ObjectProperty.ι _) fun X => X.2.trans h.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := ObjectProperty.hom_ext _ (Category.comp_id _)

omit [Category.{v'} D'] in
@[simp] lemma Model.overEquivOfEq_functor_obj {T₁ T₂ : D} (h : T₁ = T₂)
    (X : (Model.over (Φ := Φ) (B := B) (divB := divB) T₁).FullSubcategory) :
    ((Model.overEquivOfEq h).functor.obj X).obj = X.obj := rfl

omit [Category.{v'} D'] in
@[simp] lemma Model.overEquivOfEq_functor_map {T₁ T₂ : D} (h : T₁ = T₂)
    {X Y : (Model.over (Φ := Φ) (B := B) (divB := divB) T₁).FullSubcategory} (f : X ⟶ Y) :
    ((Model.overEquivOfEq h).functor.map f).hom = f.hom := rfl

/-- `comapFunctor` on the objects over `T`. -/
def Model.comapOver (T : D') :
    (Model.over (Φ := Φ.comap P hP) (B := B.comap P hP) (divB := divB.comap P hP) T).FullSubcategory
      ⥤ (Model.over (Φ := Φ) (B := B) (divB := divB) (P.obj T)).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Model.comapFunctor P hP) fun X => congrArg P.obj X.2

variable (T : D') [Subsingleton (T ⟶ T)] [Subsingleton (P.obj T ⟶ P.obj T)]

instance : (Model.comapOver P hP (Φ := Φ) (B := B) (divB := divB) T).Faithful where
  map_injective {X Y} φ ψ h := by
    obtain ⟨⟨A, α⟩, hA⟩ := X
    obtain ⟨⟨A', α'⟩, hA'⟩ := Y
    change A = T at hA
    change A' = T at hA'
    subst hA hA'
    have h' := congrArg (fun f => f.hom) h
    refine ObjectProperty.hom_ext _ (Model.hom_ext ?_ (Subsingleton.elim _ _) ?_ ?_)
    · have := congrArg Model.Hom.deg h'; exact this
    · have := congrArg Model.Hom.div h'; exact this
    · have := congrArg Model.Hom.u h'; exact this

instance : (Model.comapOver P hP (Φ := Φ) (B := B) (divB := divB) T).Full where
  map_surjective {X Y} φ := by
    have hs : ∀ f g : P.obj T ⟶ P.obj T, f = g := fun f g => Subsingleton.elim f g
    obtain ⟨⟨A, α⟩, hA⟩ := X
    obtain ⟨⟨A', α'⟩, hA'⟩ := Y
    change A = T at hA
    change A' = T at hA'
    subst hA hA'
    have hb : φ.hom.base = P.map (𝟙 _) := hs _ _
    refine ⟨ObjectProperty.homMk ⟨φ.hom.deg, 𝟙 _, φ.hom.div, φ.hom.div_mem, φ.hom.u, ?_⟩, ?_⟩
    · have := φ.hom.rel
      rw [hb] at this
      exact this
    · refine ObjectProperty.hom_ext _ (Model.hom_ext rfl ?_ rfl rfl)
      exact (hb.symm)

instance : (Model.comapOver P hP (Φ := Φ) (B := B) (divB := divB) T).EssSurj where
  mem_essImage Y := by
    obtain ⟨⟨A, α⟩, hA⟩ := Y
    change A = P.obj T at hA
    subst hA
    exact ⟨⟨⟨T, α⟩, rfl⟩, ⟨Iso.refl _⟩⟩

instance : (Model.comapOver P hP (Φ := Φ) (B := B) (divB := divB) T).IsEquivalence where

/-- **Over an object `T` with only the identity endomorphism (e.g. a terminal object), the
pulled-back model Frobenioid is the original one over `P(T)`.** -/
def Model.comapOverEquiv :
    (Model.over (Φ := Φ.comap P hP) (B := B.comap P hP) (divB := divB.comap P hP) T).FullSubcategory
      ≌ (Model.over (Φ := Φ) (B := B) (divB := divB) (P.obj T)).FullSubcategory :=
  (Model.comapOver P hP T).asEquivalence

end Comap

/-! ### Functors of model Frobenioids over a fixed base -/

section MapData

variable {D' : Type u'} [Category.{v'} D'] {D : Type u} [Category.{v} D]
  {Φ Φ' : DivMonoid.{w} D} {B B' : GrpOn.{w} D}
  {divB : DivHom B Φ.toGrpOn} {divB' : DivHom B' Φ'.toGrpOn}
  (c : ∀ A, Φ.obj A →+ Φ'.obj A)
  (hc : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'), c A (Φ.pb f x) = Φ'.pb f (c A' x))
  (hpos : ∀ A (x : Φ.obj A), x ∈ Φ.pos A → c A x ∈ Φ'.pos A)
  (cb : ∀ A, B.obj A →+ B'.obj A)
  (hcb : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'), cb A (B.pb f u) = B'.pb f (cb A' u))
  (hdiv : ∀ A (u : B.obj A), divB'.app A (cb A u) = c A (divB.app A u))

/-- **The functor of model Frobenioids induced by maps of the data** `Φ → Φ'`, `B → B'`
(natural, positive, compatible with `Div_B`): the identity on the base, `c` on divisors and `cb`
on rational functions (e.g. the realification, [FrdI], Proposition 5.3). -/
def Model.mapFunctor : Model Φ B divB ⥤ Model Φ' B' divB' where
  obj X := ⟨X.base, c _ X.α⟩
  map {X Y} φ := Model.mk' φ.deg φ.base (c _ φ.div) (hpos _ _ φ.div_mem) (cb _ φ.u) (by
    change (φ.deg : ℕ) • c X.base X.α + c X.base φ.div =
      Φ'.pb φ.base (c Y.base Y.α) + divB'.app X.base (cb X.base φ.u)
    rw [hdiv, ← hc, ← map_nsmul, ← map_add, ← map_add, φ.rel])
  map_id X := Model.hom_ext rfl rfl (map_zero _) (map_zero _)
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · simp only [Model.mk'_div, Model.comp_div, Model.mk'_base, Model.mk'_deg, map_add,
        map_nsmul, hc]
    · simp only [Model.mk'_u, Model.comp_u, Model.mk'_base, Model.mk'_deg, map_add,
        map_nsmul, hcb]

variable (P : D' ⥤ D) (hP : ∀ {A B : D'} (f : A ⟶ B), IsFSM f → IsFSM (P.map f))

/-- **`mapFunctor` commutes with the change of base** `comapFunctor`. -/
theorem Model.mapFunctor_comapFunctor :
    Model.mapFunctor (Φ := Φ.comap P hP) (Φ' := Φ'.comap P hP) (B := B.comap P hP)
        (B' := B'.comap P hP) (divB := divB.comap P hP) (divB' := divB'.comap P hP)
        (fun A => c (P.obj A)) (fun f x => hc (P.map f) x) (fun A x hx => hpos (P.obj A) x hx)
        (fun A => cb (P.obj A)) (fun f u => hcb (P.map f) u) (fun A u => hdiv (P.obj A) u) ⋙
      Model.comapFunctor P hP =
    Model.comapFunctor P hP ⋙ Model.mapFunctor c hc hpos cb hcb hdiv :=
  rfl

end MapData

/-! ### `B(Γ)⁰ ⥤ B(G)⁰` -/

section OrbitMap

variable {Γ G : Type*} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G]
  (p : Γ →* G) (hp : ∀ U : Subgroup Γ, IsOpen (U : Set Γ) → IsOpen (U.map p : Set G))

/-- `Γ/U ↦ G/p(U)`. -/
def OrbitObj.map (A : OrbitObj Γ) : OrbitObj G := ⟨A.H.map p, hp _ A.isOpen⟩

namespace OrbitHom

variable {A B C : OrbitObj Γ}

/-- `f : Γ/U → Γ/V`, `xU ↦ x r V`, induces `G/p(U) → G/p(V)`, `y p(U) ↦ y p(r) p(V)`. -/
def map (f : A ⟶ B) : OrbitObj.map p hp A ⟶ OrbitObj.map p hp B where
  toFun := Quotient.lift (fun y : G => (QuotientGroup.mk (y * p (rep f)) : G ⧸ (B.H.map p)))
    (fun a b hab => by
      obtain ⟨h, hh, he⟩ := QuotientGroup.leftRel_apply.mp hab
      refine QuotientGroup.eq.2 ⟨(rep f)⁻¹ * (h * rep f), conj_mem f hh, ?_⟩
      rw [map_mul, map_mul, map_inv, he, mul_inv_rev]
      group)
  map_smul g y := by
    induction y using QuotientGroup.induction_on with
    | H a =>
      change (QuotientGroup.mk (g * a * p (rep f)) : G ⧸ (B.H.map p)) =
        g • (QuotientGroup.mk (a * p (rep f)) : G ⧸ (B.H.map p))
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_assoc]

lemma map_mk (f : A ⟶ B) (y : G) :
    (map p hp f).toFun (QuotientGroup.mk y) = QuotientGroup.mk (y * p (rep f)) := rfl

lemma rep_comp (f : A ⟶ B) (g : B ⟶ C) : ∃ c ∈ C.H, rep (f ≫ g) = rep f * rep g * c := by
  have h1 := mk_rep (f ≫ g)
  rw [comp_toFun, Function.comp_apply, ← mk_rep f, apply_mk_of_eq g (mk_rep g).symm] at h1
  refine ⟨(rep f * rep g)⁻¹ * rep (f ≫ g), QuotientGroup.eq.1 h1.symm, by group⟩

end OrbitHom

/-- **`B(Γ)⁰ ⥤ B(G)⁰`**, `Γ/U ↦ G/p(U)`. -/
def OrbitObj.mapFunctor : OrbitObj Γ ⥤ OrbitObj G where
  obj := OrbitObj.map p hp
  map f := OrbitHom.map p hp f
  map_id A := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H a =>
      rw [OrbitHom.map_mk]
      exact QuotientGroup.eq.2 (by
        rw [mul_inv_rev, inv_mul_cancel_right]
        exact (Subgroup.mem_map_of_mem p (OrbitHom.rep_id_mem A)) |> (A.H.map p).inv_mem)
  map_comp {A B C} f g := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨c, hc, he⟩ := OrbitHom.rep_comp f g
      rw [OrbitHom.comp_toFun, Function.comp_apply, OrbitHom.map_mk, OrbitHom.map_mk,
        OrbitHom.map_mk, he]
      refine QuotientGroup.eq.2 ?_
      change _ ∈ Subgroup.map p C.H
      have hc' : (p c)⁻¹ ∈ C.H.map p := (C.H.map p).inv_mem (Subgroup.mem_map_of_mem p hc)
      convert hc' using 1
      rw [map_mul, map_mul]
      group

omit [TopologicalSpace Γ] in
/-- Maps into `Γ/Γ` are unique. -/
instance (A : OrbitObj Γ) : Subsingleton (A ⟶ OrbitObj.top) :=
  ⟨fun _ _ => OrbitHom.hom_ext (funext fun _ =>
    @Subsingleton.elim _ QuotientGroup.subsingleton_quotient_top _ _)⟩

/-- For `p` surjective, `p(Γ) = G`: maps into the image of `Γ/Γ` are unique. -/
lemma subsingleton_hom_map_top (hs : Function.Surjective p) (A : OrbitObj G) :
    Subsingleton (A ⟶ OrbitObj.map p hp OrbitObj.top) := by
  have h : (OrbitObj.top : OrbitObj Γ).H.map p = ⊤ := Subgroup.map_top_of_surjective p hs
  haveI : Subsingleton (G ⧸ (OrbitObj.map p hp OrbitObj.top).H) := by
    change Subsingleton (G ⧸ (OrbitObj.top : OrbitObj Γ).H.map p)
    rw [h]
    exact QuotientGroup.subsingleton_quotient_top
  exact ⟨fun f g => OrbitHom.hom_ext (funext fun _ => Subsingleton.elim _ _)⟩

lemma map_top_eq (hs : Function.Surjective p) :
    OrbitObj.map p hp OrbitObj.top = OrbitObj.top := by
  have h : (OrbitObj.top : OrbitObj Γ).H.map p = ⊤ := Subgroup.map_top_of_surjective p hs
  change (⟨_, _⟩ : OrbitObj G) = ⟨⊤, _⟩
  congr

/-- **FSM-morphisms of `B(Γ)⁰` are isomorphisms**, hence go to FSM-morphisms under any functor. -/
lemma isFSM_map_of_orbit [IsTopologicalGroup Γ] {D : Type*} [Category D] (P : OrbitObj Γ ⥤ D)
    {A B : OrbitObj Γ} (f : A ⟶ B) (hf : IsFSM f) : IsFSM (P.map f) := by
  obtain ⟨hinj, hsurj⟩ := OrbitHom.bijective_of_isFSM hf
  let e := Equiv.ofBijective _ ⟨hinj, hsurj⟩
  let g : B ⟶ A := ⟨e.symm, fun h x => by
    apply hinj
    change e (e.symm (h • x)) = f.toFun (h • e.symm x)
    rw [f.map_smul, e.apply_symm_apply]
    change _ = h • e (e.symm x)
    rw [e.apply_symm_apply]⟩
  haveI : IsIso f := ⟨g, OrbitHom.hom_ext (funext fun x => e.symm_apply_apply x),
    OrbitHom.hom_ext (funext fun x => e.apply_symm_apply x)⟩
  exact isFSM_of_isIso _

/-- **Continuous surjections of compact groups onto Hausdorff groups map open subgroups to open
subgroups** (the image is closed of finite index). -/
lemma isOpen_map_of_surjective [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup G]
    [T2Space G] (hc : Continuous p) (hs : Function.Surjective p) (U : Subgroup Γ)
    (hU : IsOpen (U : Set Γ)) : IsOpen (U.map p : Set G) := by
  haveI : Finite (Γ ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : (U.map p).FiniteIndex :=
    ⟨Nat.pos_iff_ne_zero.mp (Nat.pos_of_dvd_of_pos (Subgroup.index_map_dvd U hs)
      (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero))⟩
  refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
  rw [Subgroup.coe_map]
  exact ((U.isClosed_of_isOpen hU).isCompact.image hc).isClosed

end OrbitMap

end Frobenioid

end Iut

end
