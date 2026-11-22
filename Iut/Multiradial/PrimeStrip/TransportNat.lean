/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.AutRigid

/-!
# Natural isomorphisms of transported model Frobenioids, and 2-isomorphisms from bases

* `Model.transportNatIso`: a natural isomorphism `β : E ≅ E'` of base functors, compatible with
  the maps `c, c'` of divisor monoids and `cb, cb'` of rational functions through the pull-back
  along `β`, induces `Model.transport E c cb ≅ Model.transport E' c' cb'`
  (components `(1, β_A, 0, 0)`);
* `FrobCat.Iso.hom2OfBase`: a 2-isomorphism of isomorphisms of Frobenioids from natural
  isomorphisms `α`, `β` and the divisor compatibility, when the `commP` squares agree on base
  morphisms (isomorphisms of `F_Φ` are determined by their base, `FrobCat.elem_hom_ext_of_isIso`).
-/

noncomputable section

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v v' u u'

section TransportNat

variable {D : Type u} [Category.{v} D] {D' : Type u'} [Category.{v'} D']
  {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {Φ' : DivMonoid.{w} D'} {B' : GrpOn.{w} D'} {divB' : DivHom B' Φ'.toGrpOn}
  {E E' : D ⥤ D'} (β : E ≅ E')
  {c : ∀ A, Φ.obj A →+ Φ'.obj (E.obj A)}
  {hc : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'), c A (Φ.pb f x) = Φ'.pb (E.map f) (c A' x)}
  {hpos : ∀ A (x : Φ.obj A), x ∈ Φ.pos A → c A x ∈ Φ'.pos (E.obj A)}
  {cb : ∀ A, B.obj A →+ B'.obj (E.obj A)}
  {hcb : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'), cb A (B.pb f u) = B'.pb (E.map f) (cb A' u)}
  {hdiv : ∀ A (u : B.obj A), divB'.app (E.obj A) (cb A u) = c A (divB.app A u)}
  {c' : ∀ A, Φ.obj A →+ Φ'.obj (E'.obj A)}
  {hc' : ∀ {A A' : D} (f : A ⟶ A') (x : Φ.obj A'),
    c' A (Φ.pb f x) = Φ'.pb (E'.map f) (c' A' x)}
  {hpos' : ∀ A (x : Φ.obj A), x ∈ Φ.pos A → c' A x ∈ Φ'.pos (E'.obj A)}
  {cb' : ∀ A, B.obj A →+ B'.obj (E'.obj A)}
  {hcb' : ∀ {A A' : D} (f : A ⟶ A') (u : B.obj A'),
    cb' A (B.pb f u) = B'.pb (E'.map f) (cb' A' u)}
  {hdiv' : ∀ A (u : B.obj A), divB'.app (E'.obj A) (cb' A u) = c' A (divB.app A u)}
  (hβc : ∀ A (x : Φ.obj A), Φ'.pb (β.hom.app A) (c' A x) = c A x)
  (hβb : ∀ A (u : B.obj A), B'.pb (β.hom.app A) (cb' A u) = cb A u)

include hβc in
/-- The component `(1, β_A, 0, 0)`. -/
def Model.transportNatApp (X : Model Φ B divB) :
    (Model.transport E c hc hpos cb hcb hdiv).obj X ⟶
      (Model.transport E' c' hc' hpos' cb' hcb' hdiv').obj X :=
  Model.mk1 (β.hom.app X.base) 0 (Φ'.pos _).zero_mem 0 (by
    simp only [map_zero, add_zero]
    exact (hβc X.base X.α).symm)

lemma Model.transportNatApp_base (X : Model Φ B divB) :
    (Model.transportNatApp β (hc := hc) (hpos := hpos) (hcb := hcb) (hdiv := hdiv)
      (hc' := hc') (hpos' := hpos') (hcb' := hcb') (hdiv' := hdiv') hβc X).base =
      β.hom.app X.base := rfl

instance (X : Model Φ B divB) :
    IsIso (Model.transportNatApp β (hc := hc) (hpos := hpos) (hcb := hcb) (hdiv := hdiv)
      (hc' := hc') (hpos' := hpos') (hcb' := hcb') (hdiv' := hdiv') hβc X) :=
  Model.isIso_of _ rfl (inferInstanceAs (IsIso (β.hom.app X.base))) rfl

include hβb in
/-- **`Model.transport E ≅ Model.transport E'`** from `β : E ≅ E'` compatible with `c`, `cb`. -/
def Model.transportNatIso :
    Model.transport E c hc hpos cb hcb hdiv ≅ Model.transport E' c' hc' hpos' cb' hcb' hdiv' :=
  NatIso.ofComponents
    (fun X => asIso (Model.transportNatApp β (hc := hc) (hpos := hpos) (hcb := hcb)
      (hdiv := hdiv) (hc' := hc') (hpos' := hpos') (hcb' := hcb') (hdiv' := hdiv') hβc X))
    (fun {X Y} φ => by
      refine Model.hom_ext ?_ (β.hom.naturality φ.base) ?_ ?_
      · change (1 : ℕ+) * φ.deg = φ.deg * 1
        rw [one_mul, mul_one]
      · simp only [asIso_hom, Model.comp_div, Model.transportNatApp, Model.mk1_div,
          Model.mk1_deg, Model.transport_map_div, Model.transport_map_base, map_zero, zero_add,
          PNat.one_coe, one_smul, smul_zero, add_zero]
        exact (hβc _ _).symm
      · simp only [asIso_hom, Model.comp_u, Model.transportNatApp, Model.mk1_u,
          Model.mk1_deg, Model.transport_map_u, Model.transport_map_base, map_zero, zero_add,
          PNat.one_coe, one_smul, smul_zero, add_zero]
        exact (hβb _ _).symm)

lemma Model.transportNatIso_hom_app (X : Model Φ B divB) :
    ((Model.transportNatIso β hβc hβb (hc := hc) (hpos := hpos) (hcb := hcb) (hdiv := hdiv)
      (hc' := hc') (hpos' := hpos') (hcb' := hcb') (hdiv' := hdiv')).hom.app X).base =
      β.hom.app X.base := rfl

end TransportNat

end Frobenioid

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid

namespace FrobCat.Iso

/-- **A 2-isomorphism from natural isomorphisms `α`, `β`** compatible with the divisor
isomorphisms, when the `commP` squares agree on base morphisms. -/
def hom2OfBase {X Y : FrobCat} {f g : X.Iso Y} (α : f.C.functor ≅ g.C.functor)
    (β : f.D.functor ≅ g.D.functor)
    (hphi : ∀ (A : X.D) (x : X.Φ.obj A), Y.Φ.pb (β.hom.app A) (g.phi A x) = f.phi A x)
    (hbase : ∀ A : X.C, (Y.P.map (α.hom.app A) ≫ (FrobCat.sqIso g.commP).hom.app A).base =
      ((FrobCat.sqIso f.commP).hom.app A ≫
        (FrobCat.elemIsoOfBase (A := (FrobCat.elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj
          (X.P.obj A)) (B := (FrobCat.elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj
          (X.P.obj A)) (β.app (X.P.obj A).base)).hom).base) :
    FrobCat.Iso.Hom2 f g where
  α := α
  β := β
  phi_compat := hphi
  commP_compat A := FrobCat.elem_hom_ext_of_isIso
    (IsIso.comp_isIso' (inferInstanceAs (IsIso (Y.P.mapIso (α.app A)).hom))
      (inferInstanceAs (IsIso ((FrobCat.sqIso g.commP).app A).hom)))
    (IsIso.comp_isIso' (inferInstanceAs (IsIso ((FrobCat.sqIso f.commP).app A).hom))
      (inferInstanceAs (IsIso (FrobCat.elemIsoOfBase
        (A := (FrobCat.elemMap f.D.functor f.phi f.phi_pos f.phi_pb).obj (X.P.obj A))
        (B := (FrobCat.elemMap g.D.functor g.phi g.phi_pos g.phi_pb).obj (X.P.obj A))
        (β.app (X.P.obj A).base)).hom))) (hbase A)

end FrobCat.Iso

end PrimeStrip

end Multiradial

end Iut
