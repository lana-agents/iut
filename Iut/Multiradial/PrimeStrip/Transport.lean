/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.IsoClass

/-!
# Isomorphisms of Galois model Frobenioids from group and module isomorphisms (MR21 R2)

The surjectivity half of IUT I, Corollary 5.3 (ii), (iii) (l.9891–9898 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`) lifts an isomorphism of
base categories to an isomorphism of Frobenioids. For the `p`-adic Frobenioids `C_v`, `C^⊢_v`
(Galois model Frobenioids, [FrdII], Example 1.1 (ii); `Iut.Frobenioid.GaloisModel`) the lift is
built from an isomorphism of topological groups `σ : G ≅ G'` and a `σ`-equivariant isomorphism
`ψ : M ≅ M'` of the modules (`\bar{ℚ}_p^×`) preserving the valuations. This file makes this
construction, with no inputs:

* `Model.transport`: the functor of model Frobenioids induced by a functor of bases `E : D ⥤ D'`
  and natural maps of the divisor monoids and of the rational functions compatible with `Div`;
  `Model.transportEquiv`: an equivalence, for an equivalence `E` and maps in both directions that
  are inverse through the unit and counit of `E`;
* `FrobCat.Iso.ofTransport`: the resulting isomorphism of Frobenioids (`FrobCat.Iso`), with base
  equivalence `E`;
* `OrbitObj.equivOfIso σ : B(G)⁰ ≌ B(G')⁰`, `G/H ↦ G'/σ(H)` (`OrbitObj.mapFunctor`), for an
  isomorphism of topological groups `σ`;
* **`GaloisModel.isoOf σ ψ`**: the isomorphism of Frobenioids
  `GaloisModel G ℓ Γ ≅ GaloisModel G' ℓ' Γ` over `OrbitObj.equivOfIso σ` induced by a
  `σ`-equivariant `ψ : M ≃+ M'` with `ℓ' ∘ ψ = ℓ` (identity on `Φ = Γ_{≥0}`, `ψ` on rational
  functions);
* **surjectivity of `F ↦ D` on classes from lifts of automorphisms** (`FrobCat.AutLift`: every
  self-equivalence of the base is the base equivalence of an automorphism; invariant under
  isomorphism, `FrobCat.autLift_of_iso`): `FrobCat.IsoClass.toD_surjective` and, for the
  non-archimedean parts of `F`-prime-strips, `FStripNon.isoClassToD_surjective` (from `AutLift` of
  the models `C_v`; IUT I, Corollary 5.3 (ii), surjectivity).
-/

noncomputable section

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v v' u u'

/-! ### Model Frobenioids along a change of base -/

section Transport

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
  {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {Φ' : DivMonoid.{w} D'} {B' : GrpOn.{w} D'} {divB' : DivHom B' Φ'.toGrpOn}
  (E : D ⥤ D') (c : ∀ A, Φ.obj A →+ Φ'.obj (E.obj A))
  (hc : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'), c A (Φ.pb f x) = Φ'.pb (E.map f) (c A' x))
  (hpos : ∀ A (x : Φ.obj A), x ∈ Φ.pos A → c A x ∈ Φ'.pos (E.obj A))
  (cb : ∀ A, B.obj A →+ B'.obj (E.obj A))
  (hcb : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'), cb A (B.pb f u) = B'.pb (E.map f) (cb A' u))
  (hdiv : ∀ A (u : B.obj A), divB'.app (E.obj A) (cb A u) = c A (divB.app A u))

include hc hpos hcb hdiv

/-- **The functor of model Frobenioids along a change of base** `E : D ⥤ D'`, given natural maps
`c : Φ(A) → Φ'(E A)` (positive) and `cb : B(A) → B'(E A)` compatible with `Div_B`:
`(A, α) ↦ (E A, c α)`, `(n, f, Z, u) ↦ (n, E f, c Z, cb u)`. -/
def Model.transport : Model Φ B divB ⥤ Model Φ' B' divB' where
  obj X := ⟨E.obj X.base, c _ X.α⟩
  map {X Y} φ := Model.mk' φ.deg (E.map φ.base) (c _ φ.div) (hpos _ _ φ.div_mem) (cb _ φ.u) (by
    change (φ.deg : ℕ) • c X.base X.α + c X.base φ.div =
      Φ'.pb (E.map φ.base) (c Y.base Y.α) + divB'.app (E.obj X.base) (cb X.base φ.u)
    rw [hdiv, ← hc, ← map_nsmul, ← map_add, ← map_add, φ.rel])
  map_id X := Model.hom_ext rfl (E.map_id _) (map_zero _) (map_zero _)
  map_comp {X Y Z} φ ψ := by
    refine Model.hom_ext rfl (E.map_comp _ _) ?_ ?_
    · simp only [Model.mk'_div, Model.comp_div, Model.mk'_base, Model.mk'_deg, map_add,
        map_nsmul, hc]
    · simp only [Model.mk'_u, Model.comp_u, Model.mk'_base, Model.mk'_deg, map_add,
        map_nsmul, hcb]

@[simp] lemma Model.transport_obj_base (X : Model Φ B divB) :
    ((Model.transport E c hc hpos cb hcb hdiv).obj X).base = E.obj X.base := rfl

@[simp] lemma Model.transport_map_base {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((Model.transport E c hc hpos cb hcb hdiv).map φ).base = E.map φ.base := rfl

@[simp] lemma Model.transport_map_div {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((Model.transport E c hc hpos cb hcb hdiv).map φ).div = c _ φ.div := rfl

@[simp] lemma Model.transport_map_u {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((Model.transport E c hc hpos cb hcb hdiv).map φ).u = cb _ φ.u := rfl

@[simp] lemma Model.transport_map_deg {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((Model.transport E c hc hpos cb hcb hdiv).map φ).deg = φ.deg := rfl

end Transport

section TransportEquiv

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
  {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {Φ' : DivMonoid.{w} D'} {B' : GrpOn.{w} D'} {divB' : DivHom B' Φ'.toGrpOn}
  (E : D ≌ D')
  (c : ∀ A, Φ.obj A →+ Φ'.obj (E.functor.obj A))
  (hc : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'),
    c A (Φ.pb f x) = Φ'.pb (E.functor.map f) (c A' x))
  (hpos : ∀ A (x : Φ.obj A), x ∈ Φ.pos A → c A x ∈ Φ'.pos (E.functor.obj A))
  (cb : ∀ A, B.obj A →+ B'.obj (E.functor.obj A))
  (hcb : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'),
    cb A (B.pb f u) = B'.pb (E.functor.map f) (cb A' u))
  (hdiv : ∀ A (u : B.obj A), divB'.app (E.functor.obj A) (cb A u) = c A (divB.app A u))
  (c' : ∀ A, Φ'.obj A →+ Φ.obj (E.inverse.obj A))
  (hc' : ∀ {A A' : D'} (f : A ⟶ A') (x : Φ'.obj A'),
    c' A (Φ'.pb f x) = Φ.pb (E.inverse.map f) (c' A' x))
  (hpos' : ∀ A (x : Φ'.obj A), x ∈ Φ'.pos A → c' A x ∈ Φ.pos (E.inverse.obj A))
  (cb' : ∀ A, B'.obj A →+ B.obj (E.inverse.obj A))
  (hcb' : ∀ {A A' : D'} (f : A ⟶ A') (u : B'.obj A'),
    cb' A (B'.pb f u) = B.pb (E.inverse.map f) (cb' A' u))
  (hdiv' : ∀ A (u : B'.obj A), divB.app (E.inverse.obj A) (cb' A u) = c' A (divB'.app A u))
  (hcu : ∀ A (x : Φ.obj A), Φ.pb (E.unit.app A) (c' _ (c A x)) = x)
  (hcbu : ∀ A (u : B.obj A), B.pb (E.unit.app A) (cb' _ (cb A u)) = u)
  (hcc : ∀ A (x : Φ'.obj A), Φ'.pb (E.counitInv.app A) (c _ (c' A x)) = x)
  (hcbc : ∀ A (u : B'.obj A), B'.pb (E.counitInv.app A) (cb _ (cb' A u)) = u)

include hcu in
/-- The unit component `(1, η_A, 0, 0) : X ⟶ T'(T(X))`. -/
def Model.transportUnitHom (X : Model Φ B divB) :
    X ⟶ (Model.transport E.inverse c' hc' hpos' cb' hcb' hdiv').obj
      ((Model.transport E.functor c hc hpos cb hcb hdiv).obj X) :=
  Model.mk1 (E.unit.app X.base) 0 (Φ.pos _).zero_mem 0 (by
    rw [map_zero, add_zero, add_zero]
    exact (hcu X.base X.α).symm)

include hcc in
/-- The inverse counit component `(1, ε⁻¹_A, 0, 0) : Y ⟶ T(T'(Y))`. -/
def Model.transportCounitInvHom (Y : Model Φ' B' divB') :
    Y ⟶ (Model.transport E.functor c hc hpos cb hcb hdiv).obj
      ((Model.transport E.inverse c' hc' hpos' cb' hcb' hdiv').obj Y) :=
  Model.mk1 (E.counitInv.app Y.base) 0 (Φ'.pos _).zero_mem 0 (by
    rw [map_zero, add_zero, add_zero]
    exact (hcc Y.base Y.α).symm)

include hcbu in
lemma Model.transportUnit_naturality {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    φ ≫ Model.transportUnitHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcu Y =
      Model.transportUnitHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcu X ≫
        (Model.transport E.inverse c' hc' hpos' cb' hcb' hdiv').map
          ((Model.transport E.functor c hc hpos cb hcb hdiv).map φ) := by
  refine Model.hom_ext (mul_comm _ _) (E.unit.naturality φ.base) ?_ ?_
  · simp only [Model.comp_div, Model.transportUnitHom, Model.mk1_div, Model.mk1_deg,
      Model.mk1_base, Model.transport_map_div, map_zero, zero_add, smul_zero, add_zero,
      PNat.one_coe, one_smul]
    exact (hcu _ _).symm
  · simp only [Model.comp_u, Model.transportUnitHom, Model.mk1_u, Model.mk1_deg,
      Model.mk1_base, Model.transport_map_u, map_zero, zero_add, smul_zero, add_zero,
      PNat.one_coe, one_smul]
    exact (hcbu _ _).symm

include hcbc in
lemma Model.transportCounitInv_naturality {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    φ ≫ Model.transportCounitInvHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcc Y =
      Model.transportCounitInvHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcc X ≫
        (Model.transport E.functor c hc hpos cb hcb hdiv).map
          ((Model.transport E.inverse c' hc' hpos' cb' hcb' hdiv').map φ) := by
  refine Model.hom_ext (mul_comm _ _) (E.counitInv.naturality φ.base) ?_ ?_
  · simp only [Model.comp_div, Model.transportCounitInvHom, Model.mk1_div, Model.mk1_deg,
      Model.mk1_base, Model.transport_map_div, map_zero, zero_add, smul_zero, add_zero,
      PNat.one_coe, one_smul]
    exact (hcc _ _).symm
  · simp only [Model.comp_u, Model.transportCounitInvHom, Model.mk1_u, Model.mk1_deg,
      Model.mk1_base, Model.transport_map_u, map_zero, zero_add, smul_zero, add_zero,
      PNat.one_coe, one_smul]
    exact (hcbc _ _).symm

/-- **The equivalence of model Frobenioids along an equivalence of bases**, for maps of the data
in both directions inverse to each other through the unit and counit of `E`. -/
def Model.transportEquiv : Model Φ B divB ≌ Model Φ' B' divB' where
  functor := Model.transport E.functor c hc hpos cb hcb hdiv
  inverse := Model.transport E.inverse c' hc' hpos' cb' hcb' hdiv'
  unitIso := NatIso.ofComponents
      (fun X =>
        @asIso _ _ _ _ (Model.transportUnitHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb'
          hdiv' hcu X) (Model.isIso_of _ rfl (inferInstanceAs (IsIso (E.unit.app X.base))) rfl))
      (fun φ => Model.transportUnit_naturality E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb'
        hdiv' hcu hcbu φ)
  counitIso := (NatIso.ofComponents
      (fun Y =>
        @asIso _ _ _ _ (Model.transportCounitInvHom E c hc hpos cb hcb hdiv c' hc' hpos' cb'
          hcb' hdiv' hcc Y) (Model.isIso_of _ rfl
            (inferInstanceAs (IsIso (E.counitInv.app Y.base))) rfl))
      (fun φ => Model.transportCounitInv_naturality E c hc hpos cb hcb hdiv c' hc' hpos' cb'
        hcb' hdiv' hcc hcbc φ)).symm
  functor_unitIso_comp X := by
    -- `T(η_X) = ε⁻¹_{T X}` (both are `(1, E(η), 0, 0) = (1, ε⁻¹_E, 0, 0)`)
    have h : (Model.transport E.functor c hc hpos cb hcb hdiv).map
        (Model.transportUnitHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcu X) =
        Model.transportCounitInvHom E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcc
          ((Model.transport E.functor c hc hpos cb hcb hdiv).obj X) :=
      Model.hom_ext rfl (E.counitInv_app_functor X.base).symm (map_zero _) (map_zero _)
    erw [h]
    exact @IsIso.hom_inv_id _ _ _ _ _
      (Model.isIso_of _ rfl (inferInstanceAs (IsIso (E.counitInv.app _))) rfl)

lemma Model.transportEquiv_functor :
    (Model.transportEquiv E c hc hpos cb hcb hdiv c' hc' hpos' cb' hcb' hdiv' hcu hcbu hcc
      hcbc).functor = Model.transport E.functor c hc hpos cb hcb hdiv := rfl

end TransportEquiv

/-! ### `B(G)⁰ ≌ B(G')⁰` from an isomorphism of topological groups -/

section OrbitEquiv

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

lemma OrbitHom.rep_map (p : G →* G')
    (hp : ∀ U : Subgroup G, IsOpen (U : Set G) → IsOpen (U.map p : Set G'))
    {A B : OrbitObj G} (f : A ⟶ B) :
    ∃ b ∈ B.H.map p, OrbitHom.rep (OrbitHom.map p hp f) = p (OrbitHom.rep f) * b := by
  have h := OrbitHom.mk_rep (OrbitHom.map p hp f)
  rw [OrbitHom.map_mk, one_mul] at h
  exact ⟨(p (OrbitHom.rep f))⁻¹ * OrbitHom.rep (OrbitHom.map p hp f), QuotientGroup.eq.1 h.symm,
    by group⟩

/-- `σ` maps open subgroups to open subgroups. -/
lemma isOpen_map_of_continuousMulEquiv (σ : G ≃ₜ* G') (U : Subgroup G)
    (hU : IsOpen (U : Set G)) : IsOpen (U.map (σ : G →* G') : Set G') := by
  rw [Subgroup.coe_map]
  exact σ.toHomeomorph.isOpenMap _ hU

/-- `B(G)⁰ ⥤ B(G')⁰` along `σ`. -/
abbrev OrbitObj.isoFunctor (σ : G ≃ₜ* G') : OrbitObj G ⥤ OrbitObj G' :=
  OrbitObj.mapFunctor (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ)

lemma OrbitObj.mem_map_map_symm (σ : G ≃ₜ* G') (H : Subgroup G) {a : G} :
    a ∈ (H.map (σ : G →* G')).map (σ.symm : G' →* G) ↔ a ∈ H := by
  constructor
  · rintro ⟨b, ⟨c, hc, rfl⟩, rfl⟩
    simpa using hc
  · intro ha
    exact ⟨σ a, ⟨a, ha, rfl⟩, by simp⟩

/-- The unit `A ≅ σ⁻¹(σ(A))`. -/
def OrbitObj.isoUnitApp (σ : G ≃ₜ* G') (A : OrbitObj G) :
    A ≅ (OrbitObj.isoFunctor σ.symm).obj ((OrbitObj.isoFunctor σ).obj A) :=
  OrbitObj.isoOfConj _ _ 1
    (fun a ha => by
      rw [inv_one, one_mul, mul_one]
      exact (OrbitObj.mem_map_map_symm σ A.H).2 ha)
    (fun b hb => by
      rw [one_mul, inv_one, mul_one]
      exact (OrbitObj.mem_map_map_symm σ A.H).1 hb)

lemma OrbitObj.isoUnitApp_mk (σ : G ≃ₜ* G') (A : OrbitObj G) (x : G) :
    (OrbitObj.isoUnitApp σ A).hom.toFun (QuotientGroup.mk x) = QuotientGroup.mk x := by
  change (QuotientGroup.mk (x * 1) : G ⧸ _) = _
  rw [mul_one]

/-- Morphisms of `B(G)⁰` are determined by the image of the base coset. -/
lemma OrbitHom.ext_of_mk_one {A B : OrbitObj G} {f g : A ⟶ B}
    (h : f.toFun (QuotientGroup.mk 1) = g.toFun (QuotientGroup.mk 1)) : f = g :=
  OrbitHom.hom_ext <| funext fun x => by
    induction x using QuotientGroup.induction_on with
    | H a => rw [OrbitHom.apply_mk f a, OrbitHom.apply_mk g a, h]

/-- A morphism fixing the base coset has its representative in the target subgroup. -/
lemma OrbitHom.rep_mem_of_mk_one {A B : OrbitObj G} {f : A ⟶ B}
    (h : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1) : OrbitHom.rep f ∈ B.H := by
  have := OrbitHom.mk_rep f
  rw [h] at this
  exact mk_eq_one_iff.mp this

lemma OrbitHom.map_mk_one (p : G →* G')
    (hp : ∀ U : Subgroup G, IsOpen (U : Set G) → IsOpen (U.map p : Set G'))
    {A B : OrbitObj G} {f : A ⟶ B} (h : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1) :
    (OrbitHom.map p hp f).toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1 := by
  rw [OrbitHom.map_mk, one_mul]
  exact mk_eq_one_iff.mpr (Subgroup.mem_map_of_mem p (OrbitHom.rep_mem_of_mk_one h))

lemma OrbitObj.isoUnit_naturality (σ : G ≃ₜ* G') {A B : OrbitObj G} (f : A ⟶ B) :
    f ≫ (OrbitObj.isoUnitApp σ B).hom = (OrbitObj.isoUnitApp σ A).hom ≫
      OrbitHom.map (σ.symm : G' →* G) (isOpen_map_of_continuousMulEquiv σ.symm)
        (OrbitHom.map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ) f) := by
  obtain ⟨b, hb, he⟩ := OrbitHom.rep_map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ) f
  have h1 : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk (OrbitHom.rep f) :=
    (OrbitHom.mk_rep f).symm
  refine OrbitHom.ext_of_mk_one ?_
  rw [OrbitHom.comp_toFun, OrbitHom.comp_toFun, Function.comp_apply, Function.comp_apply, h1,
    OrbitObj.isoUnitApp_mk, OrbitObj.isoUnitApp_mk]
  change (QuotientGroup.mk (OrbitHom.rep f) : G ⧸ _) = QuotientGroup.mk (1 * (σ.symm : G' →* G)
    (OrbitHom.rep (OrbitHom.map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ) f)))
  rw [he]
  refine QuotientGroup.eq.2 ?_
  have e : (OrbitHom.rep f)⁻¹ * (1 * (σ.symm : G' →* G) ((σ : G →* G') (OrbitHom.rep f) * b)) =
      (σ.symm : G' →* G) b := by
    simp only [one_mul, map_mul, MonoidHom.coe_coe, ContinuousMulEquiv.symm_apply_apply,
      inv_mul_cancel_left]
  rw [e]
  exact Subgroup.mem_map_of_mem _ hb

/-- `σ⁻¹ ∘ σ` on `B(G)⁰` is isomorphic to the identity. -/
def OrbitObj.isoUnit (σ : G ≃ₜ* G') :
    𝟭 (OrbitObj G) ≅ OrbitObj.isoFunctor σ ⋙ OrbitObj.isoFunctor σ.symm :=
  NatIso.ofComponents (OrbitObj.isoUnitApp σ) fun f => OrbitObj.isoUnit_naturality σ f

/-- **`B(G)⁰ ≌ B(G')⁰` along an isomorphism of topological groups** `σ`: `G/H ↦ G'/σ(H)`, with
unit and counit the identity cosets. -/
def OrbitObj.equivOfIso (σ : G ≃ₜ* G') : OrbitObj G ≌ OrbitObj G' where
  functor := OrbitObj.isoFunctor σ
  inverse := OrbitObj.isoFunctor σ.symm
  unitIso := OrbitObj.isoUnit σ
  counitIso := (OrbitObj.isoUnit σ.symm).symm
  functor_unitIso_comp A := OrbitHom.ext_of_mk_one (by
    change (OrbitObj.isoUnitApp σ.symm ((OrbitObj.isoFunctor σ).obj A)).inv.toFun
      ((OrbitHom.map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ)
        (OrbitObj.isoUnitApp σ A).hom).toFun (QuotientGroup.mk 1)) = QuotientGroup.mk 1
    have h2 := OrbitHom.map_mk_one (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ)
      (OrbitObj.isoUnitApp_mk σ A 1)
    refine (congrArg (OrbitObj.isoUnitApp σ.symm ((OrbitObj.isoFunctor σ).obj A)).inv.toFun
      h2).trans ?_
    change (QuotientGroup.mk (1 * (1 : G')⁻¹) : G' ⧸ _) = _
    rw [inv_one, mul_one])

lemma OrbitObj.equivOfIso_unit_app (σ : G ≃ₜ* G') (A : OrbitObj G) :
    (OrbitObj.equivOfIso σ).unit.app A = (OrbitObj.isoUnitApp σ A).hom := rfl

lemma OrbitObj.equivOfIso_counitInv_app (σ : G ≃ₜ* G') (A : OrbitObj G') :
    (OrbitObj.equivOfIso σ).counitInv.app A = (OrbitObj.isoUnitApp σ.symm A).hom := rfl

end OrbitEquiv


/-! ### Galois model Frobenioids along a group and a module isomorphism -/

namespace GaloisModel

section Iso

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M M' : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M'] [DistribMulAction G' M']
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m}
  {ℓ' : M' →+ ℝ} {hℓ' : ∀ (g : G') (m : M'), ℓ' (g • m) = ℓ' m} {Γ : AddSubgroup ℝ}
  (σ : G ≃ₜ* G') (ψ : M ≃+ M') (hψ : ∀ (g : G) (m : M), ψ (g • m) = σ g • ψ m)
  (hψℓ : ∀ m, ℓ' (ψ m) = ℓ m)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψ hψℓ in
lemma mem_fixedSub_map {A : OrbitObj G} {m : M} (hm : m ∈ fixedSub (preSub G ℓ hℓ Γ) A) :
    ψ m ∈ fixedSub (preSub G' ℓ' hℓ' Γ) ((OrbitObj.isoFunctor σ).obj A) := by
  refine ⟨?_, fun h' hh' => ?_⟩
  · change ℓ' (ψ m) ∈ Γ
    rw [hψℓ]; exact hm.1
  · obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hh'
    change σ h • ψ m = ψ m
    rw [← hψ, hm.2 h hh]

/-- The map of rational functions `(ℓ⁻¹Γ)^H → (ℓ'⁻¹Γ)^{σ(H)}`, `u ↦ ψ(u)`. -/
def bMap (A : OrbitObj G) :
    (bGal G ℓ hℓ Γ).obj A →+ (bGal G' ℓ' hℓ' Γ).obj ((OrbitObj.isoFunctor σ).obj A) where
  toFun u := (⟨ψ (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from u).1,
    mem_fixedSub_map σ ψ hψ hψℓ (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from u).2⟩ :
      ↥(fixedSub (preSub G' ℓ' hℓ' Γ) ((OrbitObj.isoFunctor σ).obj A)))
  map_zero' := Subtype.ext (map_zero ψ)
  map_add' _ _ := Subtype.ext (map_add ψ _ _)

lemma bMap_val (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) :
    (show ↥(fixedSub (preSub G' ℓ' hℓ' Γ) ((OrbitObj.isoFunctor σ).obj A)) from
      bMap σ ψ hψ hψℓ A u).1 = ψ (show ↥(fixedSub (preSub G ℓ hℓ Γ) A) from u).1 := rfl

lemma bMap_pb {A A' : OrbitObj G} (f : A ⟶ A') (u : (bGal G ℓ hℓ Γ).obj A') :
    bMap σ ψ hψ hψℓ A ((bGal G ℓ hℓ Γ).pb f u) =
      (bGal G' ℓ' hℓ' Γ).pb ((OrbitObj.isoFunctor σ).map f) (bMap σ ψ hψ hψℓ A' u) := by
  obtain ⟨b, hb, he⟩ := OrbitHom.rep_map (σ : G →* G') (isOpen_map_of_continuousMulEquiv σ) f
  apply Subtype.ext
  change ψ (OrbitHom.rep f • (show ↥(fixedSub (preSub G ℓ hℓ Γ) A') from u).1) =
    OrbitHom.rep (OrbitHom.map _ _ f) • ψ (show ↥(fixedSub (preSub G ℓ hℓ Γ) A') from u).1
  rw [he, mul_smul, (mem_fixedSub_map (hℓ' := hℓ') σ ψ hψ hψℓ
    (show ↥(fixedSub (preSub G ℓ hℓ Γ) A') from u).2).2 b hb, hψ]
  rfl

lemma bMap_div (A : OrbitObj G) (u : (bGal G ℓ hℓ Γ).obj A) :
    (divGal G' ℓ' hℓ' Γ).app _ (bMap σ ψ hψ hψℓ A u) = (divGal G ℓ hℓ Γ).app A u :=
  Subtype.ext (hψℓ _)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψ in
/-- The inverse module isomorphism is `σ⁻¹`-equivariant. -/
lemma symm_equivariant (g : G') (m : M') : ψ.symm (g • m) = σ.symm g • ψ.symm m := by
  apply ψ.injective
  rw [hψ, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply]

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hψℓ in
lemma symm_ell (m : M') : ℓ (ψ.symm m) = ℓ' m := by
  rw [← hψℓ, AddEquiv.apply_symm_apply]

/-- Pull-backs along morphisms fixing the base coset are the identity. -/
lemma pb_eq_of_mk_one {G₀ : Type} [Group G₀] [TopologicalSpace G₀] [IsTopologicalGroup G₀]
    {M₀ : Type} [AddCommGroup M₀] [DistribMulAction G₀ M₀] {ℓ₀ : M₀ →+ ℝ}
    {hℓ₀ : ∀ (g : G₀) (m : M₀), ℓ₀ (g • m) = ℓ₀ m} {A B : OrbitObj G₀} (f : A ⟶ B)
    (h : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk 1) (u : (bGal G₀ ℓ₀ hℓ₀ Γ).obj B)
    (v : (bGal G₀ ℓ₀ hℓ₀ Γ).obj A)
    (huv : (show ↥(fixedSub (preSub G₀ ℓ₀ hℓ₀ Γ) B) from u).1 =
      (show ↥(fixedSub (preSub G₀ ℓ₀ hℓ₀ Γ) A) from v).1) :
    (bGal G₀ ℓ₀ hℓ₀ Γ).pb f u = v := by
  apply Subtype.ext
  change OrbitHom.rep f • (show ↥(fixedSub (preSub G₀ ℓ₀ hℓ₀ Γ) B) from u).1 = _
  rw [(show ↥(fixedSub (preSub G₀ ℓ₀ hℓ₀ Γ) B) from u).2.2 _ (OrbitHom.rep_mem_of_mk_one h), huv]

end Iso

end GaloisModel

end Frobenioid

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid

/-! ### Isomorphisms of Frobenioids along a change of base -/

section OfTransport

variable {D D' : Type} [Category.{0} D] [Category.{0} D']
  {Φ : DivMonoid.{0} D} {B : GrpOn.{0} D} {divB : DivHom B Φ.toGrpOn}
  {Φ' : DivMonoid.{0} D'} {B' : GrpOn.{0} D'} {divB' : DivHom B' Φ'.toGrpOn}
  (E : D ≌ D')
  (c : ∀ A, Φ.obj A ≃+ Φ'.obj (E.functor.obj A))
  (hpos : ∀ A (x : Φ.obj A), x ∈ Φ.pos A ↔ c A x ∈ Φ'.pos (E.functor.obj A))
  (hc : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'),
    c A (Φ.pb f x) = Φ'.pb (E.functor.map f) (c A' x))
  (cb : ∀ A, B.obj A →+ B'.obj (E.functor.obj A))
  (hcb : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'),
    cb A (B.pb f u) = B'.pb (E.functor.map f) (cb A' u))
  (hdiv : ∀ A (u : B.obj A), divB'.app (E.functor.obj A) (cb A u) = c A (divB.app A u))
  (c' : ∀ A, Φ'.obj A ≃+ Φ.obj (E.inverse.obj A))
  (hpos' : ∀ A (x : Φ'.obj A), x ∈ Φ'.pos A ↔ c' A x ∈ Φ.pos (E.inverse.obj A))
  (hc' : ∀ {A A' : D'} (f : A ⟶ A') (x : Φ'.obj A'),
    c' A (Φ'.pb f x) = Φ.pb (E.inverse.map f) (c' A' x))
  (cb' : ∀ A, B'.obj A →+ B.obj (E.inverse.obj A))
  (hcb' : ∀ {A A' : D'} (f : A ⟶ A') (u : B'.obj A'),
    cb' A (B'.pb f u) = B.pb (E.inverse.map f) (cb' A' u))
  (hdiv' : ∀ A (u : B'.obj A), divB.app (E.inverse.obj A) (cb' A u) = c' A (divB'.app A u))
  (hcu : ∀ A (x : Φ.obj A), Φ.pb (E.unit.app A) (c' _ (c A x)) = x)
  (hcbu : ∀ A (u : B.obj A), B.pb (E.unit.app A) (cb' _ (cb A u)) = u)
  (hcc : ∀ A (x : Φ'.obj A), Φ'.pb (E.counitInv.app A) (c _ (c' A x)) = x)
  (hcbc : ∀ A (u : B'.obj A), B'.pb (E.counitInv.app A) (cb _ (cb' A u)) = u)

include hcbu hcbc

/-- `Model.transportEquiv` for divisor-monoid isomorphisms `c`, `c'`. -/
abbrev Model.transportEquiv' : Model Φ B divB ≌ Model Φ' B' divB' :=
  Model.transportEquiv E (fun A => (c A).toAddMonoidHom) (fun f x => hc f x)
    (fun A x hx => (hpos A x).1 hx) cb hcb hdiv (fun A => (c' A).toAddMonoidHom)
    (fun f x => hc' f x) (fun A x hx => (hpos' A x).1 hx) cb' hcb' hdiv' hcu hcbu hcc hcbc

set_option quotPrecheck false in
local notation "𝐓" =>
  Model.transportEquiv' E c hpos hc cb hcb hdiv c' hpos' hc' cb' hcb' hdiv' hcu hcbu hcc hcbc

/-- The counit of `Model.transportEquiv'` in `F_Φ`: `(1, ε_E, 0)`. -/
lemma Model.toElem_transportEquiv'_counit (Y : Model Φ' B' divB') :
    (Model.toElem Φ' B' divB').map (𝐓.counit.app Y) =
      (FrobCat.elemIsoOfBase
        (A := (Model.toElem Φ' B' divB').obj (𝐓.functor.obj
          (𝐓.inverse.obj Y)))
        (B := (Model.toElem Φ' B' divB').obj Y) (E.counitIso.app Y.base)).hom :=
  FrobCat.map_inv_of_map_hom (Model.toElem Φ' B' divB')
    (𝐓.counitIso.app Y).symm
    (FrobCat.elemIsoOfBase
        (A := (Model.toElem Φ' B' divB').obj (𝐓.functor.obj
          (𝐓.inverse.obj Y)))
        (B := (Model.toElem Φ' B' divB').obj Y) (E.counitIso.app Y.base)).symm
    (Elem.hom_ext rfl rfl rfl)

/-- The inverse unit of `Model.transportEquiv'` in `F_Φ`: `(1, η_E⁻¹, 0)`. -/
lemma Model.toElem_transportEquiv'_unitInv (X : Model Φ B divB) :
    (Model.toElem Φ B divB).map (𝐓.unitInv.app X) =
      (FrobCat.elemIsoOfBase (A := (Model.toElem Φ B divB).obj X)
        (B := (Model.toElem Φ B divB).obj (𝐓.inverse.obj
          (𝐓.functor.obj X)))
        (E.unitIso.app X.base)).inv :=
  FrobCat.map_inv_of_map_hom (Model.toElem Φ B divB)
    (𝐓.unitIso.app X)
    (FrobCat.elemIsoOfBase (A := (Model.toElem Φ B divB).obj X)
        (B := (Model.toElem Φ B divB).obj (𝐓.inverse.obj
          (𝐓.functor.obj X)))
        (E.unitIso.app X.base))
    (Elem.hom_ext rfl rfl rfl)

/-- **The isomorphism of model Frobenioids along an equivalence of bases** `E` (with
`Model.transportEquiv` as the equivalence of Frobenioids, `E` as base equivalence and `c`, `c'`
as divisor-monoid isomorphisms). -/
def FrobCat.Iso.ofTransport :
    (FrobCat.ofModel (Model Φ B divB) (Model.toElem Φ B divB)).Iso
      (FrobCat.ofModel (Model Φ' B' divB') (Model.toElem Φ' B' divB')) where
  C := 𝐓
  D := E
  phi := c
  phi_pos := hpos
  phi_pb := hc
  phiInv := c'
  phiInv_pos := hpos'
  phiInv_pb := hc'
  phi_unit := hcu
  phi_counit := hcc
  commP := ⟨NatIso.ofComponents (fun _ => CategoryTheory.Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)⟩
  commPInv := ⟨NatIso.ofComponents (fun _ => CategoryTheory.Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)⟩
  commP_counit B := by
    refine ((Category.id_comp _).trans ((congrArg (· ≫ _)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))).trans ?_
    exact (Model.toElem_transportEquiv'_counit E c hpos hc cb hcb hdiv c' hpos' hc' cb' hcb'
      hdiv' hcu hcbu hcc hcbc B).symm
  commP_unit A := by
    refine ((Category.id_comp _).trans ((congrArg (· ≫ _)
      (CategoryTheory.Functor.map_id _ _)).trans (Category.id_comp _))).trans ?_
    exact (Model.toElem_transportEquiv'_unitInv E c hpos hc cb hcb hdiv c' hpos' hc' cb' hcb'
      hdiv' hcu hcbu hcc hcbc A).symm

lemma FrobCat.Iso.ofTransport_D :
    (FrobCat.Iso.ofTransport E c hpos hc cb hcb hdiv c' hpos' hc' cb' hcb' hdiv' hcu hcbu hcc
      hcbc).D = E := rfl

end OfTransport

/-! ### Galois model Frobenioids -/

section Galois

variable {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
  {M M' : Type} [AddCommGroup M] [DistribMulAction G M] [AddCommGroup M'] [DistribMulAction G' M']
  {ℓ : M →+ ℝ} {hℓ : ∀ (g : G) (m : M), ℓ (g • m) = ℓ m}
  {ℓ' : M' →+ ℝ} {hℓ' : ∀ (g : G') (m : M'), ℓ' (g • m) = ℓ' m} {Γ : AddSubgroup ℝ}
  (σ : G ≃ₜ* G') (ψ : M ≃+ M') (hψ : ∀ (g : G) (m : M), ψ (g • m) = σ g • ψ m)
  (hψℓ : ∀ m, ℓ' (ψ m) = ℓ m)

/-- **The isomorphism of Galois model Frobenioids induced by `σ : G ≅ G'` and a `σ`-equivariant
`ψ : M ≅ M'` with `ℓ' ∘ ψ = ℓ`** (`FrobCat.Iso`): base equivalence `B(G)⁰ ≌ B(G')⁰` along `σ`,
the identity on `Φ = Γ_{≥0}`, `ψ` on rational functions. -/
def GaloisModel.isoOf :
    (FrobCat.ofModel (GaloisModel G ℓ hℓ Γ)
      (Model.toElem (constPhi (OrbitObj G) Γ) (bGal G ℓ hℓ Γ) (divGal G ℓ hℓ Γ))).Iso
    (FrobCat.ofModel (GaloisModel G' ℓ' hℓ' Γ)
      (Model.toElem (constPhi (OrbitObj G') Γ) (bGal G' ℓ' hℓ' Γ) (divGal G' ℓ' hℓ' Γ))) :=
  FrobCat.Iso.ofTransport (OrbitObj.equivOfIso σ) (fun _ => AddEquiv.refl Γ)
    (fun _ _ => Iff.rfl) (fun _ _ => rfl) (GaloisModel.bMap σ ψ hψ hψℓ)
    (fun f u => GaloisModel.bMap_pb σ ψ hψ hψℓ f u)
    (fun A u => GaloisModel.bMap_div σ ψ hψ hψℓ A u)
    (fun _ => AddEquiv.refl Γ) (fun _ _ => Iff.rfl) (fun _ _ => rfl)
    (GaloisModel.bMap σ.symm ψ.symm (GaloisModel.symm_equivariant σ ψ hψ)
      (GaloisModel.symm_ell ψ hψℓ))
    (fun f u => GaloisModel.bMap_pb σ.symm ψ.symm (GaloisModel.symm_equivariant σ ψ hψ)
      (GaloisModel.symm_ell ψ hψℓ) f u)
    (fun A u => GaloisModel.bMap_div σ.symm ψ.symm (GaloisModel.symm_equivariant σ ψ hψ)
      (GaloisModel.symm_ell ψ hψℓ) A u)
    (fun _ _ => rfl)
    (fun A _ => GaloisModel.pb_eq_of_mk_one _ (OrbitObj.isoUnitApp_mk σ A 1) _ _
      (ψ.symm_apply_apply _))
    (fun _ _ => rfl)
    (fun A _ => GaloisModel.pb_eq_of_mk_one _ (OrbitObj.isoUnitApp_mk σ.symm A 1) _ _
      (ψ.apply_symm_apply _))

/-- The base equivalence of `GaloisModel.isoOf σ ψ` is `B(G)⁰ ≌ B(G')⁰` along `σ`. -/
lemma GaloisModel.isoOf_D :
    (GaloisModel.isoOf (hℓ := hℓ) (hℓ' := hℓ') σ ψ hψ hψℓ (Γ := Γ)).D = OrbitObj.equivOfIso σ :=
  rfl

end Galois

/-! ### Surjectivity of `F ↦ D` from lifts of automorphisms -/

namespace FrobCat

/-- **Lifting of automorphisms of the base**: every self-equivalence of the base category of `X`
is (up to natural isomorphism) the base equivalence of an automorphism of `X`. -/
def AutLift (X : FrobCat) : Prop :=
  ∀ e : X.D ≌ X.D, ∃ h : X.Iso X, Nonempty (h.D.functor ≅ e.functor)

/-- `AutLift` is invariant under isomorphism (conjugation), so it need only be checked on a
model. -/
theorem autLift_of_iso {X Y : FrobCat} (m : X.Iso Y) (hY : AutLift Y) : AutLift X := by
  intro e
  obtain ⟨h, ⟨β⟩⟩ := hY ((m.D.symm.trans e).trans m.D)
  refine ⟨(m.trans h).trans m.symm, ⟨?_⟩⟩
  -- `m ⋙ h ⋙ m⁻¹ ≅ m ⋙ (m⁻¹ ⋙ e ⋙ m) ⋙ m⁻¹ ≅ e`
  exact Functor.isoWhiskerRight (Functor.isoWhiskerLeft m.D.functor β) m.D.inverse ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerRight (Functor.isoWhiskerRight m.D.unitIso.symm
      e.functor) m.D.functor ≪≫ Functor.isoWhiskerRight (Functor.leftUnitor e.functor)
        m.D.functor) m.D.inverse ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.functor m.D.unitIso.symm ≪≫ Functor.rightUnitor e.functor

/-- **Surjectivity of `F ↦ D` on isomorphism classes from `AutLift`**, when `X ≅ Y`. -/
theorem IsoClass.toD_surjective {X Y : FrobCat} (hX : AutLift X) (m : X.Iso Y) :
    Function.Surjective (IsoClass.toD : IsoClass X Y → CatIsom X.D Y.D) := by
  intro a
  obtain ⟨e, rfl⟩ := CatIsom.mk_surjective a
  obtain ⟨h, ⟨β⟩⟩ := hX (e.trans m.D.symm)
  refine ⟨IsoClass.mk (h.trans m), ?_⟩
  rw [IsoClass.toD_mk]
  refine CatIsom.mk_eq_mk.2 ⟨?_⟩
  -- `h ⋙ m ≅ (e ⋙ m⁻¹) ⋙ m ≅ e`
  exact Functor.isoWhiskerRight β m.D.functor ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e.functor m.D.counitIso ≪≫ Functor.rightUnitor e.functor

end FrobCat

section StripSurj

variable {D : InitialThetaData.{0}}

/-- **Surjectivity of `Isom(¹F, ²F) → Isom(¹D, ²D)` from lifts of automorphisms of the models**
(the surjectivity half of IUT I, Corollary 5.3 (ii), non-archimedean part). -/
theorem FStripNon.isoClassToD_surjective (hlift : ∀ v : Vnon D, (cvFrob D v).AutLift)
    (P Q : FStripNon D) :
    Function.Surjective (FStripNon.isoClassToD : P.IsoClass Q → P.toD.IsoClass Q.toD) := by
  intro a
  have h : ∀ v, ∃ b : FrobCat.IsoClass (P.comp v).F (Q.comp v).F, b.toD = a v := fun v => by
    obtain ⟨m⟩ := (P.comp v).equiv_model
    obtain ⟨m'⟩ := (Q.comp v).equiv_model
    exact FrobCat.IsoClass.toD_surjective (FrobCat.autLift_of_iso m (hlift v)) (m.trans m'.symm)
      (a v)
  choose b hb using h
  exact ⟨b, funext hb⟩

end StripSurj

end PrimeStrip

end Multiradial

end Iut
