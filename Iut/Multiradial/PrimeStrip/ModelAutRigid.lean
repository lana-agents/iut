/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.PrimeStrip.AutRigid

/-!
# Rigidity of automorphisms of model Frobenioids over the identity (MR18 T10)

IUT I, Corollary 5.3 (iv) (l.9899–9965 of
`~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`): for `v ∈ V^bad` the natural
homomorphism `Aut(F_v) → Aut(D_v)` is bijective. The proof of injectivity (l.9917–9965): for
`α` lying over the identity of `D_v`, "it suffices to verify that `α` induces the identity on the
rational function and divisor monoids of `F_v`" (then the units of [FrdI], Proposition 5.6 give
`α ≅ id`, as `F_v` is of model type); the rational functions are fixed by the naturality and
injectivity of the Kummer map ([EtTh], Theorem 5.6, Proposition 5.5, Proposition 3.2 (iii)); and
"by considering the non-cuspidal portion of the divisor of the Frobenioid-theoretic theta function
and its conjugates" and "the cuspidal portions of divisors of appropriate rational functions" (a
divisor of degree zero supported on torsion points has a principal positive multiple), the
divisor monoid is fixed as well, `α` preserving cuspidal and non-cuspidal elements ([EtTh],
Proposition 5.3 (i); IUT I, Remark 3.2.4 (vi)).

`AutRigid.lean` carries this out for the Galois model Frobenioids `C_v`. This file does the
formal part for an **arbitrary model Frobenioid** `Model Φ B divB` ([FrdI], Theorem 5.2) viewed as
a `FrobCat` (`modelFrob`), the shape of the tempered Frobenioid `F_v` ([EtTh], Definition 3.6):

* for an automorphism `h` with `β : h.D ≅ id`: the base isomorphisms `ε_X : X_D ≅ F(X)_D`
  (`ModelAut.eps`), `F = h.C.functor` lies over the identity through `ε` and preserves Frobenius
  degrees, and on zero divisors it is `h.phi` followed by a pull-back (`autF_map_div`);
* **`ModelAut.FixesDiv h β`** (`h` is the identity on `Φ^gp` through `β`) and
  **`ModelAut.FixesRat h β`** (`F^birat` is the identity on `B` through `ε`): the two properties
  of the proof quoted above;
* **`ModelAut.rel_refl_of_fixes`**: both together give a 2-isomorphism `h ⟹ id`
  ([IUTchI], Corollary 5.3 (iv), formal core `Model.nonempty_iso_id_of_over_id`);
* **the divisor step** (`ModelAut.fixesDiv_divB`, `ModelAut.fixesDiv_of_fixesRat`): if `h` fixes
  the rational functions, it fixes every principal divisor `Div_B(b)` (write `Div_B(b) = p − q`
  with `p, q` effective, `DivMonoid.generating`, and compare the two pre-steps
  `(A, 0) → (A, q)` with zero divisors `p`, `q`); if moreover `h` commutes with given
  projections `π_c, π_n` of `Φ^gp` (cuspidal and non-cuspidal parts), `Φ^gp` is torsion-free and
  some positive multiple of every divisor is `π_c(Div_B b₁) + π_n(Div_B b₂)`, then `h` fixes
  `Φ^gp` (`Model.addHom_eq_id_of_fix`);
* **`modelFrob_autRigid`**: `FrobCat.AutRigid (modelFrob Φ B divB)` from `FixesRat` for all
  automorphisms over the identity, the cuspidal compatibility (`CuspCompat`), torsion-freeness
  and the generation property. For the tempered Frobenioid at `V^bad` these are the named inputs
  of IUT I, Corollary 5.3 (iv) (MR18 T10; `HodgeTheater/TempSlotModel.lean`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace PrimeStrip

open CategoryTheory Iut.Frobenioid

variable {D : Type} [Category.{0} D] {Φ : DivMonoid.{0} D} {B : GrpOn.{0} D}
  {divB : DivHom B Φ.toGrpOn}

variable (Φ B divB) in
/-- **A model Frobenioid `Model Φ B divB` with its base `D`** ([FrdI], Theorem 5.2). -/
abbrev modelFrob : FrobCat := FrobCat.ofModel (Model Φ B divB) (Model.toElem Φ B divB)

namespace ModelAut

variable (h : (modelFrob Φ B divB).Iso (modelFrob Φ B divB))
  (β : h.D.functor ≅ 𝟭 (modelFrob Φ B divB).D)

/-- The functor of model Frobenioids of `h`. -/
abbrev autF : Model Φ B divB ⥤ Model Φ B divB := h.C.functor

/-- The component of `commP` at `X`, `P(F X) ≅ (h.D(X_D), …)`. -/
abbrev cP (X : Model Φ B divB) :
    (modelFrob Φ B divB).P.obj ((autF h).obj X) ⟶
      (FrobCat.elemMap h.D.functor h.phi h.phi_pos h.phi_pb).obj ((modelFrob Φ B divB).P.obj X) :=
  (FrobCat.sqIso h.commP).hom.app X

instance cP_isIso (X : Model Φ B divB) : IsIso (cP h X) :=
  ⟨⟨(FrobCat.sqIso h.commP).inv.app X, (FrobCat.sqIso h.commP).hom_inv_id_app X,
    (FrobCat.sqIso h.commP).inv_hom_id_app X⟩⟩

/-- **`ε_X : X_D ≅ F(X)_D`**, from `commP` and `β`. -/
def eps (X : Model Φ B divB) : X.base ≅ ((autF h).obj X).base :=
  (Elem.proj.mapIso ((FrobCat.sqIso h.commP).app X) ≪≫ β.app X.base).symm

lemma eps_inv (X : Model Φ B divB) :
    (eps h β X).inv = (cP h X).base ≫ β.hom.app X.base := rfl

lemma cP_naturality {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    (modelFrob Φ B divB).P.map ((autF h).map φ) ≫ cP h Y =
      cP h X ≫ (FrobCat.elemMap h.D.functor h.phi h.phi_pos h.phi_pb).map
        ((modelFrob Φ B divB).P.map φ) :=
  (FrobCat.sqIso h.commP).hom.naturality φ

/-- **`F` lies over the identity through `ε`.** -/
lemma autF_map_base {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((autF h).map φ).base = (eps h β X).inv ≫ φ.base ≫ (eps h β Y).hom :=
  FrobCat.conj_of_sq (I1 := Elem.proj.mapIso ((FrobCat.sqIso h.commP).app X))
    (I2 := Elem.proj.mapIso ((FrobCat.sqIso h.commP).app Y)) (J1 := β.app X.base)
    (J2 := β.app Y.base) (congrArg Elem.Hom.base (cP_naturality h φ)) (β.hom.naturality φ.base)

/-- **`F` preserves Frobenius degrees.** -/
lemma autF_map_deg {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((autF h).map φ).deg = φ.deg :=
  FrobCat.elem_deg_conj (cP_naturality h φ)

/-- **On zero divisors `F` is `h.phi`** followed by the pull-back along `P(F X) ≅ h.D(X_D)`. -/
lemma autF_map_div {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((autF h).map φ).div = Φ.pb (cP h X).base (h.phi X.base φ.div) :=
  FrobCat.elem_div_conj (cP_naturality h φ)

include β in
/-- The hypotheses `hpre` of `Model.mapUnit`. -/
lemma autF_hpre : ∀ ⦃X Y : Model Φ B divB⦄ (φ : X ⟶ Y),
    IsPreStep (Model.toElem Φ B divB) φ ↔ IsPreStep (Model.toElem Φ B divB) ((autF h).map φ) :=
  Model.preStep_iff_of_over (autF h) (eps h β) (fun φ => autF_map_base h β φ)
    (fun φ => autF_map_deg h φ)

include β in
lemma autF_hbe : ∀ ⦃X Y : Model Φ B divB⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ ((autF h).map φ).base = ((autF h).map φ').base :=
  Model.baseEq_iff_of_over (autF h) (eps h β) (fun φ => autF_map_base h β φ)

/-- **`h` induces the identity on the divisor monoid** (through `β`): `φ_h(x) = β^* x`. -/
def FixesDiv : Prop :=
  ∀ (A : D) (x : Φ.obj A), h.phi A x = Φ.pb (β.hom.app A) x

/-- **`h` induces the identity on the rational function monoid** (through `ε`):
`F^birat(x) = (ε_X⁻¹)^* x` on `O^×(X^birat) = B(X_D)` ([FrdI], Corollary 4.10;
`Model.mapUnit`). -/
def FixesRat : Prop :=
  ∀ (X : Model Φ B divB) (x : B.obj X.base),
    Model.mapUnit (autF h) (autF_hpre h β) x = B.pb (eps h β X).inv x

variable {h β}

/-- `FixesDiv` in the form of the hypothesis `hdiv` of `Model.nonempty_iso_id_of_over_id`. -/
lemma map_div_of_fixesDiv (hphi : FixesDiv h β) {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((autF h).map φ).div = Φ.pb (eps h β X).inv φ.div := by
  rw [autF_map_div, hphi, eps_inv]
  exact (Φ.pb_comp _ _ _).symm

section Hom2

variable (hphi : FixesDiv h β) (hunit : FixesRat h β)

variable (h β) in
/-- **The isomorphism `F ≅ id`** of [IUTchI], Corollary 5.3 (iv), formal core
(`Model.nonempty_iso_id_of_over_id`), made explicit. -/
def autIso : autF h ≅ 𝟭 (Model Φ B divB) :=
  (Model.twistIsoOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) (fun φ => map_div_of_fixesDiv hphi φ)).symm ≪≫
    (Model.twistIso (Model.relOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) (fun φ => map_div_of_fixesDiv hphi φ))
      (Model.idOf (autF h) (eps h β))
      (Model.compOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ))
      (Model.cOf_preStep (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ) hunit)).symm

/-- The base of `F(X) ≅ X` is `ε_X⁻¹`. -/
lemma autIso_base (X : Model Φ B divB) :
    ((autIso h β hphi hunit).hom.app X).base = (eps h β X).inv := by
  have h1 := FrobCat.map_inv_of_map_hom (Model.forget Φ B divB)
    ((Model.twistIsoOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) (fun φ => map_div_of_fixesDiv hphi φ)).app X) (eps h β X) rfl
  have h2 := FrobCat.map_inv_of_map_hom (Model.forget Φ B divB)
    ((Model.twistIso (Model.relOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
      (fun φ => autF_map_deg h φ) (fun φ => map_div_of_fixesDiv hphi φ))
      (Model.idOf (autF h) (eps h β))
      (Model.compOf (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ))
      (Model.cOf_preStep (autF h) (eps h β) (fun φ => autF_map_base h β φ)
        (fun φ => autF_map_deg h φ) hunit)).app X) (CategoryTheory.Iso.refl _) rfl
  exact (congrArg₂ (· ≫ ·) h1 h2).trans (Category.comp_id _)

include hphi hunit in
/-- **IUT I, Corollary 5.3 (iv), injectivity (formal part)**: an automorphism of a model
Frobenioid over the identity of the base inducing the identity on the divisor and rational
function monoids is 2-isomorphic to the identity. -/
theorem rel_refl_of_fixes : FrobCat.Iso.Rel h (FrobCat.Iso.refl (modelFrob Φ B divB)) := by
  refine ⟨⟨autIso h β hphi hunit, β, fun A x => (hphi A x).symm, fun A => ?_⟩⟩
  have hb : ((modelFrob Φ B divB).P.map ((autIso h β hphi hunit).hom.app A) ≫
      (FrobCat.sqIso (FrobCat.Iso.refl (modelFrob Φ B divB)).commP).hom.app A).base =
      (eps h β A).inv ≫ 𝟙 _ :=
    congrArg (· ≫ 𝟙 _) (autIso_base hphi hunit A)
  exact FrobCat.elem_hom_ext_of_isIso
    (IsIso.comp_isIso' (CategoryTheory.Functor.map_isIso _ _) (inferInstanceAs (IsIso (𝟙 _))))
    (IsIso.comp_isIso' (cP_isIso h A) inferInstance) (hb.trans (Category.comp_id _))

end Hom2

/-! ### The divisor step -/

/-- **An automorphism fixing the rational functions fixes the principal divisors**: write
`Div_B(b) = p − q` with `p, q` effective and compare the pre-steps `(1, id, p, b)`, `(1, id, q, 0)`
from `(A, 0)` to `(A, q)` (`Model.mapUnit_u_sub`). -/
theorem fixesDiv_divB (hunit : FixesRat h β) (A : D) (b : B.obj A) :
    h.phi A (divB.app A b) = Φ.pb (β.hom.app A) (divB.app A b) := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Φ.generating (divB.app A b)
  let X : Model Φ B divB := ⟨A, 0⟩
  let Y : Model Φ B divB := ⟨A, q⟩
  let s : X ⟶ Y := Model.mk1 (𝟙 A) p hp b (by
    change (0 : Φ.obj A) + p = Φ.pb (𝟙 A) q + divB.app A b
    rw [GrpOn.pb_id', hpq]; abel)
  let t : X ⟶ Y := Model.mk1 (𝟙 A) q hq 0 (by
    change (0 : Φ.obj A) + q = Φ.pb (𝟙 A) q + divB.app A 0
    rw [GrpOn.pb_id', map_zero]; abel)
  have hs : IsPreStep (Model.toElem Φ B divB) s := ⟨rfl, inferInstanceAs (IsIso (𝟙 A))⟩
  have ht : IsPreStep (Model.toElem Φ B divB) t := ⟨rfl, inferInstanceAs (IsIso (𝟙 A))⟩
  have hu := Model.mapUnit_u_sub (autF h) (autF_hpre h β) (autF_hbe h β) hs ht rfl
  have hb : ((autF h).map s).base = ((autF h).map t).base := by
    rw [autF_map_base h β s, autF_map_base h β t]; rfl
  have r1 := ((autF h).map s).rel
  have r2 := ((autF h).map t).rel
  rw [autF_map_deg, autF_map_div, hb] at r1
  rw [autF_map_deg, autF_map_div] at r2
  change ((1 : ℕ+) : ℕ) • _ + Φ.pb (cP h X).base (h.phi A p) = _ + _ at r1
  change ((1 : ℕ+) : ℕ) • _ + Φ.pb (cP h X).base (h.phi A q) = _ + _ at r2
  have e1 : Φ.pb (cP h X).base (h.phi A (divB.app A b)) =
      divB.app _ (((autF h).map s).u - ((autF h).map t).u) := by
    have k1 : h.phi A (p - q) = h.phi A p - h.phi A q := map_sub _ _ _
    have k2 : Φ.pb (cP h X).base (h.phi A p - h.phi A q) =
        Φ.pb (cP h X).base (h.phi A p) - Φ.pb (cP h X).base (h.phi A q) := map_sub _ _ _
    have k3 : divB.app ((autF h).obj X).base (((autF h).map s).u - ((autF h).map t).u) =
        divB.app ((autF h).obj X).base ((autF h).map s).u -
          divB.app ((autF h).obj X).base ((autF h).map t).u := map_sub _ _ _
    rw [hpq, k1, k2, k3]
    exact (add_sub_add_left_eq_sub _ _ _).symm.trans
      ((congrArg₂ (· - ·) r1 r2).trans (add_sub_add_left_eq_sub _ _ _))
  have e2 : ((autF h).map s).u - ((autF h).map t).u = B.pb (eps h β X).inv b := by
    rw [← hu]
    change Model.mapUnit (autF h) (autF_hpre h β) (b - 0) = _
    rw [sub_zero, hunit]
  rw [e2, divB.natural, eps_inv] at e1
  exact Φ.pb_injective _ (e1.trans (Φ.pb_comp _ _ _))

/-- The endomorphism `x ↦ (β⁻¹)^* φ_h(x)` of `Φ^gp(A)` induced by `h`. -/
def rho (h : (modelFrob Φ B divB).Iso (modelFrob Φ B divB))
    (β : h.D.functor ≅ 𝟭 (modelFrob Φ B divB).D) (A : D) : Φ.obj A →+ Φ.obj A :=
  (Φ.pb (β.inv.app A)).comp (h.phi A).toAddMonoidHom

lemma rho_apply (A : D) (x : Φ.obj A) : rho h β A x = Φ.pb (β.inv.app A) (h.phi A x) := rfl

lemma fixesDiv_iff : FixesDiv h β ↔ ∀ A x, rho h β A x = x := by
  constructor
  · intro hphi A x
    rw [rho_apply, hphi, ← GrpOn.pb_comp']
    exact (congrArg (fun f => Φ.pb f x) (β.inv_hom_id_app A)).trans (Φ.pb_id' A x)
  · intro hr A x
    have e := congrArg (Φ.pb (β.hom.app A)) (hr A x)
    rw [rho_apply, ← GrpOn.pb_comp'] at e
    exact ((Φ.pb_id' _ _).symm.trans
      (congrArg (fun f => Φ.pb f (h.phi A x)) (β.hom_inv_id_app A).symm)).trans e

variable (Φ divB) in
/-- **Compatibility with the cuspidal and non-cuspidal parts** ([EtTh], Proposition 5.3 (i);
IUT I, Remark 3.2.4 (vi)): every automorphism over the identity commutes, through `β`, with the
projections `π_c`, `π_n` of `Φ^gp`. -/
def CuspCompat (πc πn : ∀ A : D, Φ.obj A →+ Φ.obj A) : Prop :=
  ∀ (h : (modelFrob Φ B divB).Iso (modelFrob Φ B divB))
    (β : h.D.functor ≅ 𝟭 (modelFrob Φ B divB).D) (A : D) (x : Φ.obj A),
    rho h β A (πc A x) = πc A (rho h β A x) ∧ rho h β A (πn A x) = πn A (rho h β A x)

variable (divB) in
/-- **Divisors are generated by cuspidal and non-cuspidal parts of principal divisors** (IUT I,
Corollary 5.3 (iv), proof: the divisor of the theta function and its conjugates, and divisors of
degree zero supported on torsion points): a positive multiple of every `x ∈ Φ^gp(A)` is
`π_c(Div_B b₁) + π_n(Div_B b₂)`. -/
def DivGen (πc πn : ∀ A : D, Φ.obj A →+ Φ.obj A) : Prop :=
  ∀ (A : D) (x : Φ.obj A), ∃ n : ℕ, 0 < n ∧ ∃ b₁ b₂ : B.obj A,
    n • x = πc A (divB.app A b₁) + πn A (divB.app A b₂)

variable (Φ) in
/-- `Φ^gp(A)` is torsion-free. -/
def TorsionFree : Prop := ∀ (A : D) (n : ℕ) (x : Φ.obj A), 0 < n → n • x = 0 → x = 0

/-- **The divisor step of IUT I, Corollary 5.3 (iv)**: an automorphism over the identity fixing
the rational functions fixes the divisor monoid, given the cuspidal compatibility, the
generation property and torsion-freeness. -/
theorem fixesDiv_of_fixesRat {πc πn : ∀ A : D, Φ.obj A →+ Φ.obj A}
    (hcc : CuspCompat Φ divB πc πn) (hgen : DivGen divB πc πn) (htf : TorsionFree Φ)
    (hunit : FixesRat h β) : FixesDiv h β := by
  refine fixesDiv_iff.2 fun A x => ?_
  have hH : ∀ y ∈ (divB.app A).range, rho h β A y = y := by
    rintro _ ⟨b, rfl⟩
    rw [rho_apply, fixesDiv_divB hunit A b, ← GrpOn.pb_comp']
    exact (congrArg (fun f => Φ.pb f _) (β.inv_hom_id_app A)).trans (Φ.pb_id' A _)
  exact Model.addHom_eq_id_of_fix (htf A) (rho h β A) (πc A) (πn A)
    (fun y => (hcc h β A y).1) (fun y => (hcc h β A y).2) (divB.app A).range hH
    (fun y => by
      obtain ⟨n, hn, b₁, b₂, e⟩ := hgen A y
      exact ⟨n, hn, _, ⟨b₁, rfl⟩, _, ⟨b₂, rfl⟩, e⟩) x

end ModelAut

open ModelAut in
/-- **IUT I, Corollary 5.3 (iv), injectivity, for a model Frobenioid**: if every automorphism over
the identity fixes the rational functions (the Kummer step, `FixesRat`), commutes with the
cuspidal and non-cuspidal projections (`CuspCompat`), and the divisors are generated by parts of
principal divisors (`DivGen`) in a torsion-free `Φ^gp`, then `modelFrob Φ B divB` is
`FrobCat.AutRigid`, i.e. `F ↦ D` is injective on isomorphism classes
(`FrobCat.IsoClass.toD_injective`). -/
theorem modelFrob_autRigid {πc πn : ∀ A : D, Φ.obj A →+ Φ.obj A}
    (hrat : ∀ (h : (modelFrob Φ B divB).Iso (modelFrob Φ B divB))
      (β : h.D.functor ≅ 𝟭 (modelFrob Φ B divB).D), FixesRat h β)
    (hcc : CuspCompat Φ divB πc πn) (hgen : DivGen divB πc πn) (htf : TorsionFree Φ) :
    (modelFrob Φ B divB).AutRigid := fun h ⟨β⟩ =>
  rel_refl_of_fixes (fixesDiv_of_fixesRat hcc hgen htf (hrat h β)) (hrat h β)

end PrimeStrip

end Multiradial

end Iut
