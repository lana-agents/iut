/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.KummerClass
import Iut.Frobenioid.KummerFrob

/-!
# Kummer classes of model Frobenioids ([FrdII], Definition 2.1(ii), Theorem 2.4(i))

For an object `X` of a model Frobenioid, `O^×(X)` is a commutative normal subgroup
`Model.ouAut X` of `Aut_C(X)` (with the discrete topology). The group-theoretic Kummer classes of
`KummerClass.lean` therefore give, for a subgroup `H ⊆ Aut_C(X)` and `g ∈ O^×(X)` with `g^n`
fixed by `H`, **Kummer classes `κ ∈ H¹(H, μ_n(X))`** (`Model.frobKummerClass`), whose cocycle is
the Frobenioid-theoretic Kummer cocycle `Model.kummerCocycle` of `KummerFrob.lean`
(`Model.kfun_hom`).

* `Model.conj_eq_self_of_base`, `Model.kfun_eq_of_base`: automorphisms with trivial base act
  trivially on `O^×(X)` ([FrdII], Theorem 1.2(ii)), so the cocycle factors through the image
  `H_A` of `H` in `Aut_D(X_D)` ([FrdII], Definition 2.2(i));
* **`Model.thm24_kummerClass`**: a fully faithful functor preserving `O^×` maps Kummer classes to
  Kummer classes, through the isomorphism `Aut_C(X) ≅ Aut_C(F X)` and
  `μ_n(X) → μ_n(F X)` ([FrdII], Theorem 2.4(i): "isomorphisms … `H¹((H₁)_{A₁}, μ_N(A₁)) ≅
  H¹((H₂)_{A₂}, μ_N(A₂))` … compatible with the respective Kummer maps");
* `PAdicGalois.thm24_kummerClass`: the case of an equivalence `C^⊢(E) ≌ C^⊢(E')`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory
open scoped IsMulCommutative

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

lemma id_mem_ounits (X : Model Φ B divB) : 𝟙 X ∈ Ounits 𝐏 X :=
  ⟨inferInstance, Base_id X, degFr_id X⟩

lemma comp_mem_ounits {X : Model Φ B divB} {e e' : X ⟶ X} (he : e ∈ Ounits 𝐏 X)
    (he' : e' ∈ Ounits 𝐏 X) : e ≫ e' ∈ Ounits 𝐏 X := by
  haveI := he.1; haveI := he'.1
  refine ⟨inferInstance, ?_, ?_⟩
  · change Base 𝐏 (e ≫ e') = 𝟙 _
    rw [Base_comp, show Base 𝐏 e = 𝟙 _ from he.2.1, show Base 𝐏 e' = 𝟙 _ from he'.2.1,
      Category.comp_id]
  · change degFr 𝐏 (e ≫ e') = 1
    rw [degFr_comp, show degFr 𝐏 e = 1 from he.2.2, show degFr 𝐏 e' = 1 from he'.2.2, mul_one]

lemma inv_mem_ounits {X : Model Φ B divB} (α : X ≅ X) (h : α.hom ∈ Ounits 𝐏 X) :
    α.inv ∈ Ounits 𝐏 X := by
  refine ⟨inferInstance, ?_, degFr_of_isIso α.inv⟩
  change Base 𝐏 α.inv = 𝟙 _
  have := congrArg (Base 𝐏) α.hom_inv_id
  rwa [Base_comp, show Base 𝐏 α.hom = 𝟙 _ from h.2.1, Category.id_comp, Base_id] at this

/-- **`O^×(X)` as a subgroup of `Aut_C(X)`** (discrete topology). -/
def ouAut (X : Model Φ B divB) : Subgroup (WithDisc (Aut X)) where
  carrier := {α | (show Aut X from α).hom ∈ Ounits 𝐏 X}
  mul_mem' {a b} ha hb := by
    change ((show Aut X from a) * (show Aut X from b)).hom ∈ Ounits 𝐏 X
    rw [Aut.Aut_mul_def]
    exact comp_mem_ounits hb ha
  one_mem' := id_mem_ounits X
  inv_mem' {a} ha := inv_mem_ounits (show Aut X from a) ha

lemma mem_ouAut {X : Model Φ B divB} {α : WithDisc (Aut X)} :
    α ∈ ouAut X ↔ (show Aut X from α).hom ∈ Ounits 𝐏 X := Iff.rfl

/-- `(g u g⁻¹).hom = conj g u.hom`. -/
lemma conj_hom {X : Model Φ B divB} (g u : WithDisc (Aut X)) :
    (show Aut X from g * u * g⁻¹).hom = conj (show Aut X from g) (show Aut X from u).hom := by
  change (((show Aut X from g) * (show Aut X from u)) * (show Aut X from g)⁻¹).hom = _
  simp only [Aut.Aut_mul_def, Iso.trans_hom, Aut.Aut_inv_def, Iso.symm_hom, conj]

instance (X : Model Φ B divB) : (ouAut X).Normal :=
  ⟨fun u hu g => by
    rw [mem_ouAut, conj_hom]
    exact conj_mem_ounits _ hu⟩

instance (X : Model Φ B divB) : IsMulCommutative (ouAut X) :=
  ⟨⟨fun a b => Subtype.ext (by
    change (show Aut X from (a : WithDisc (Aut X))) * (show Aut X from (b : WithDisc (Aut X))) =
      (show Aut X from (b : WithDisc (Aut X))) * (show Aut X from (a : WithDisc (Aut X)))
    simp only [Aut.Aut_mul_def]
    exact Iso.ext (ounits_comm b.2 a.2))⟩⟩

/-- **The Kummer class** `κ ∈ H¹(H, μ_n(X))` of `g ∈ O^×(X)` with `g^n` fixed by `H ⊆ Aut_C(X)`
([FrdII], Definition 2.1(ii)). -/
noncomputable abbrev frobKummerClass (X : Model Φ B divB) (H : Subgroup (WithDisc (Aut X)))
    (n : ℕ) (g : ouAut X)
    (hg : ∀ h ∈ H, KummerClass.conjU (ouAut X) h (g ^ n) = g ^ n) :
    ContH1 H (KummerClass.mu (ouAut X) n) :=
  KummerClass.kummerClass (ouAut X) H n g hg

/-- The Kummer cocycle of `KummerClass` is the Frobenioid-theoretic Kummer cocycle. -/
lemma kfun_hom {X : Model Φ B divB} (H : Subgroup (WithDisc (Aut X))) (n : ℕ) (g : ouAut X)
    (hg : ∀ h ∈ H, KummerClass.conjU (ouAut X) h (g ^ n) = g ^ n) (h : H) :
    (show Aut X from ((KummerClass.kfun (ouAut X) H n g hg h : ouAut X) : WithDisc (Aut X))).hom =
      kummerCocycle (show Aut X from (g : WithDisc (Aut X))).hom
        (show Aut X from (h : WithDisc (Aut X))) := by
  have e : ((KummerClass.kfun (ouAut X) H n g hg h : ouAut X) : WithDisc (Aut X)) =
      (h : WithDisc (Aut X)) * (g : WithDisc (Aut X)) * (h : WithDisc (Aut X))⁻¹ *
        (g : WithDisc (Aut X))⁻¹ :=
    KummerClass.coe_kfun _ _ _ _ _ _
  rw [e]
  change ((show Aut X from (h : WithDisc (Aut X)) * (g : WithDisc (Aut X)) *
    (h : WithDisc (Aut X))⁻¹) *
    (show Aut X from (g : WithDisc (Aut X)))⁻¹).hom = _
  rw [Aut.Aut_mul_def, Iso.trans_hom, conj_hom, kummerCocycle, Aut.Aut_inv_def, Iso.symm_hom,
    IsIso.Iso.inv_hom]

/-- **Automorphisms with trivial base act trivially on `O^×`** ([FrdII], Theorem 1.2(ii)). -/
theorem conj_eq_self_of_base {X : Model Φ B divB} (α : X ≅ X) (hα : α.hom.base = 𝟙 _)
    {e : X ⟶ X} (he : e ∈ Ounits 𝐏 X) : conj α e = e := by
  have hc := conj_mem_ounits α he
  have hinv : α.inv.base = 𝟙 _ := by
    have := iso_base α
    rwa [hα, Category.comp_id] at this
  refine hom_ext ?_ ?_ ?_ ?_
  · rw [ounits_deg hc, ounits_deg he]
  · rw [ounits_base hc, ounits_base he]
  · rw [ounits_div hc, ounits_div he]
  · rw [conj_u α he, hinv, GrpOn.pb_id']

/-- The Kummer cocycle factors through the image of `H` in `Aut_D(X_D)` (`H_A`). -/
theorem kfun_eq_of_base {X : Model Φ B divB} (H : Subgroup (WithDisc (Aut X))) (n : ℕ)
    (g : ouAut X) (hg : ∀ h ∈ H, KummerClass.conjU (ouAut X) h (g ^ n) = g ^ n) {h h' : H}
    (hb : (show Aut X from ((h : WithDisc (Aut X))⁻¹ * (h' : WithDisc (Aut X)))).hom.base =
      𝟙 _) :
    KummerClass.kfun (ouAut X) H n g hg h = KummerClass.kfun (ouAut X) H n g hg h' := by
  refine KummerClass.kfun_eq_of_mul_mem (ouAut X) H n g hg fun u => Subtype.ext ?_
  change (show Aut X from _) = (show Aut X from (u : WithDisc (Aut X)))
  apply Iso.ext
  rw [KummerClass.coe_conjU, conj_hom]
  exact conj_eq_self_of_base _ hb u.2

variable {D' : Type*} [Category D'] {Φ' : DivMonoid.{w} D'} {B' : GrpOn.{w} D'}
  {divB' : DivHom B' Φ'.toGrpOn}

local notation "𝐏'" => toElem Φ' B' divB'

/-- `Aut_C(X) ≅ Aut_C(F X)` for a fully faithful `F` (discrete topologies). -/
noncomputable def autEquiv (F : Model Φ B divB ⥤ Model Φ' B' divB') [F.Full] [F.Faithful]
    (X : Model Φ B divB) : WithDisc (Aut X) ≃* WithDisc (Aut (F.obj X)) :=
  (Functor.FullyFaithful.ofFullyFaithful F).autMulEquivOfFullyFaithful X

lemma autEquiv_hom (F : Model Φ B divB ⥤ Model Φ' B' divB') [F.Full] [F.Faithful]
    (X : Model Φ B divB) (α : WithDisc (Aut X)) :
    (show Aut (F.obj X) from autEquiv F X α).hom = F.map (show Aut X from α).hom := rfl

/-- **[FrdII], Theorem 2.4(i), Kummer classes**: a fully faithful functor `F` preserving `O^×`
maps the Kummer class of `(H, g)` to that of `(F(H), F g)`, through `Aut_C(X) ≅ Aut_C(F X)` and
`μ_n(X) → μ_n(F X)`. -/
theorem thm24_kummerClass (F : Model Φ B divB ⥤ Model Φ' B' divB') [F.Full] [F.Faithful]
    {X : Model Φ B divB}
    (hF : ∀ {e : X ⟶ X}, e ∈ Ounits 𝐏 X → F.map e ∈ Ounits 𝐏' (F.obj X))
    (H : Subgroup (WithDisc (Aut X))) (n : ℕ) (g : ouAut X)
    (hg : ∀ h ∈ H, KummerClass.conjU (ouAut X) h (g ^ n) = g ^ n) :
    ∃ (hU : ∀ u ∈ ouAut X, autEquiv F X u ∈ ouAut (F.obj X)),
      KummerClass.kummerMap (ouAut X) H n (autEquiv F X) hU rfl (frobKummerClass X H n g hg) =
      frobKummerClass (F.obj X) (H.map (autEquiv F X : WithDisc (Aut X) →* _)) n
        ⟨autEquiv F X g, hU _ g.2⟩
        (KummerClass.fixed_map (ouAut X) H n (autEquiv F X) hU rfl g hg) :=
  ⟨fun _ hu => hF hu, KummerClass.map_kummerClass (ouAut X) H n (autEquiv F X) _ rfl g hg _⟩

end Model

namespace PAdicGalois

variable {p : ℕ} [hp : Fact p.Prime]
variable {Γ : AddSubgroup ℝ}
variable {E E' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E']

/-- **[FrdII], Theorem 2.4(i), Kummer classes, for `C^⊢`**: an equivalence
`Ψ : C^⊢(E) ≌ C^⊢(E')` maps the Kummer class `κ ∈ H¹(H, μ_n(X))` of `g ∈ O^×(X)` to the Kummer
class of `Ψ g` in `H¹(Ψ(H), μ_n(Ψ X))`. -/
theorem thm24_kummerClass (F : GFrob p E Γ ⥤ GFrob p E' Γ) [F.IsEquivalence] {X : GFrob p E Γ}
    (H : Subgroup (WithDisc (Aut X))) (n : ℕ) (g : Model.ouAut X)
    (hg : ∀ h ∈ H, KummerClass.conjU (Model.ouAut X) h (g ^ n) = g ^ n) :
    ∃ (hU : ∀ u ∈ Model.ouAut X, Model.autEquiv F X u ∈ Model.ouAut (F.obj X)),
      KummerClass.kummerMap (Model.ouAut X) H n (Model.autEquiv F X) hU rfl
        (Model.frobKummerClass X H n g hg) =
      Model.frobKummerClass (F.obj X) (H.map (Model.autEquiv F X : WithDisc (Aut X) →* _)) n
        ⟨Model.autEquiv F X g, hU _ g.2⟩
        (KummerClass.fixed_map (Model.ouAut X) H n (Model.autEquiv F X) hU rfl g hg) :=
  Model.thm24_kummerClass F (fun he => (thm24_kummer F he (Iso.refl _)).1) H n g hg

end PAdicGalois

end Frobenioid

end Iut
