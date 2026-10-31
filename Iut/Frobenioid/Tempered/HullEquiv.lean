/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BsFldPreserve

/-!
# The equivalence of base-field-theoretic hulls

[EtTh], Corollary 3.8(ii); [IUTchI], Example 3.2(iii),(vi)(d).

[EtTh], Corollary 3.8(ii) (l.5925–5933, proof l.5971–5980 of `~/iut-scratch/wall/txt/The Etale
Theta Function and its Frobenioid-theoretic Manifestations.txt`): an equivalence `Ψ : C₁ ≅ C₂` of
tempered Frobenioids over Div-slim bases "preserves the base-field-theoretic morphisms and induces a
compatible equivalence `C₁^bs-fld ≅ C₂^bs-fld` of the subcategories `C₁^bs-fld ⊆ C₁`,
`C₂^bs-fld ⊆ C₂` given by the respective base-field-theoretic hulls". The proof: `Ψ` preserves the
Frobenius-trivial objects, the base-field-theoretic pre-steps and morphisms, and by Remark 3.6.3 the
objects of the hull are those linked to Frobenius-trivial objects by base-field-theoretic
pre-steps, its morphisms the base-field-theoretic morphisms between them.

[IUTchI], Example 3.2(iii) (l.3681–3690 of `Inter-universal Teichmuller Theory I.txt`): by [EtTh],
Corollary 3.8(ii), the `p_v`-adic Frobenioid `C_v ⊆ F_v` (the hull) "may be reconstructed
category-theoretically from `F_v`" (i.e. is preserved by equivalences, Remark 3.2.1(i)).
Example 3.2(vi)(d): the base `D_v` may be reconstructed from `F_v` or from `C_v` ([FrdI],
Theorem 3.4(v)).

## Formalisation

* **A lifting lemma** (`liftFunctor`, `liftCompIso`, `liftFunctor_isEquivalence`): for faithful
  functors `i₁ : C₁' ⥤ C₁`, `i₂ : C₂' ⥤ C₂` whose images are characterized by morphism classes
  `P₁`, `P₂` (closed under composition, containing the isomorphisms), an equivalence
  `F : C₁ ⥤ C₂` matching `P₁`, `P₂` and the essential images induces an equivalence
  `H : C₁' ⥤ C₂'` with `i₁ ⋙ F ≅ H ⋙ i₂`.
* **Objects of the hull** (Remark 3.6.3): `Model.exists_iso_hullObj_of_preSteps` (an object linked
  by two base-field-theoretic pre-steps `E → W`, `E → hull(Z')` is isomorphic to an object of the
  hull), `Model.exists_iso_hullObj_of_frob` (an object with a base-identity endomorphism of
  Frobenius type and degree `2`, i.e. Frobenius-trivial, is isomorphic to `hull(A, 0)`),
  `Model.hullObj_linked` (every object of the hull is linked to `hull(A, 0)` in this way).
* **[EtTh], Corollary 3.8(ii); [IUTchI], Example 3.2(iii)** (`Model.hullEquiv`,
  `Model.hullEquivIso`, `Model.hullEquiv_isEquivalence`): an equivalence `F` of model Frobenioids
  matching morphism types, Frobenius degrees (through an automorphism `σ` of `ℕ_{≥1}`),
  base-equivalent pairs and base-field-theoretic morphisms induces an equivalence of the hulls
  `C₁^bs-fld ≅ C₂^bs-fld` compatible with `F`. `Model.exists_hullEquiv_fsm`: over slim bases
  of FSM-type with `BsFldChar` (all hypotheses discharged by [FrdI], Theorem 3.4 and
  `Model.isBsFld_map_iff_fsm`).
* **[IUTchI], Example 3.2(vi)(d)** (`Model.hullEquiv_base`): the base functors of `F` and of the
  induced equivalence of hulls agree (`Base(H φ') = Base(F φ)` up to the comparison isomorphisms);
  with `Model.thm34_fsm_preservesBase` for the hulls themselves, `D_v` is reconstructed from `F_v`
  and from `C_v` compatibly.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u u₁ u₂

/-! ### Lifting an equivalence to subcategories -/

section Lift

variable {C₁' : Type*} [Category C₁'] {C₁ : Type*} [Category C₁] {C₂' : Type*} [Category C₂']
  {C₂ : Type*} [Category C₂]
variable (i₁ : C₁' ⥤ C₁) (i₂ : C₂' ⥤ C₂) (F : C₁ ⥤ C₂)
variable (P₂ : ∀ ⦃X Y : C₂⦄, (X ⟶ Y) → Prop)
  (hP₂ : ∀ ⦃Y Y' : C₂'⦄ (φ : i₂.obj Y ⟶ i₂.obj Y'), (∃ ψ, i₂.map ψ = φ) ↔ P₂ φ)
  (hcomp : ∀ ⦃X Y Z : C₂⦄ (φ : X ⟶ Y) (ψ : Y ⟶ Z), P₂ φ → P₂ ψ → P₂ (φ ≫ ψ))
  (hiso : ∀ ⦃X Y : C₂⦄ (φ : X ⟶ Y), IsIso φ → P₂ φ)
  (hF : ∀ ⦃X X' : C₁'⦄ (f : X ⟶ X'), P₂ (F.map (i₁.map f)))
  (hobj : ∀ X : C₁', ∃ Y : C₂', Nonempty (F.obj (i₁.obj X) ≅ i₂.obj Y))

/-- The lifted object. -/
noncomputable def liftObj (X : C₁') : C₂' := (hobj X).choose

/-- The comparison isomorphism `F(i₁ X) ≅ i₂(H X)`. -/
noncomputable def liftIso (X : C₁') : F.obj (i₁.obj X) ≅ i₂.obj (liftObj i₁ i₂ F hobj X) :=
  (hobj X).choose_spec.some

include hcomp hiso hF in
lemma liftMap_spec {X X' : C₁'} (f : X ⟶ X') :
    P₂ ((liftIso i₁ i₂ F hobj X).inv ≫ F.map (i₁.map f) ≫ (liftIso i₁ i₂ F hobj X').hom) :=
  hcomp _ _ (hiso _ inferInstance) (hcomp _ _ (hF f) (hiso _ inferInstance))

/-- The lifted morphism. -/
noncomputable def liftMap {X X' : C₁'} (f : X ⟶ X') :
    liftObj i₁ i₂ F hobj X ⟶ liftObj i₁ i₂ F hobj X' :=
  ((hP₂ _).2 (liftMap_spec i₁ i₂ F P₂ hcomp hiso hF hobj f)).choose

lemma i₂_map_liftMap {X X' : C₁'} (f : X ⟶ X') :
    i₂.map (liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj f) =
      (liftIso i₁ i₂ F hobj X).inv ≫ F.map (i₁.map f) ≫ (liftIso i₁ i₂ F hobj X').hom :=
  ((hP₂ _).2 (liftMap_spec i₁ i₂ F P₂ hcomp hiso hF hobj f)).choose_spec

variable [i₂.Faithful]

/-- **The induced functor `H : C₁' ⥤ C₂'`**. -/
noncomputable def liftFunctor : C₁' ⥤ C₂' where
  obj := liftObj i₁ i₂ F hobj
  map f := liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj f
  map_id X := i₂.map_injective (by simp [i₂_map_liftMap])
  map_comp f g := i₂.map_injective (by simp [i₂_map_liftMap])

/-- **Compatibility** `i₁ ⋙ F ≅ H ⋙ i₂`. -/
noncomputable def liftCompIso : i₁ ⋙ F ≅ liftFunctor i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj ⋙ i₂ :=
  NatIso.ofComponents (liftIso i₁ i₂ F hobj) (fun f => by
    change F.map (i₁.map f) ≫ _ = _ ≫ i₂.map (liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj f)
    simp [i₂_map_liftMap])

include hP₂ hiso in
/-- Isomorphisms between objects of the image of `i₂` lift. -/
lemma nonempty_iso_of_iso {Y Y' : C₂'} (e : i₂.obj Y ≅ i₂.obj Y') : Nonempty (Y ≅ Y') := by
  obtain ⟨a, ha⟩ := (hP₂ e.hom).2 (hiso _ inferInstance)
  obtain ⟨b, hb⟩ := (hP₂ e.inv).2 (hiso _ inferInstance)
  exact ⟨⟨a, b, i₂.map_injective (by simp [ha, hb]), i₂.map_injective (by simp [ha, hb])⟩⟩

variable (P₁ : ∀ ⦃X Y : C₁⦄, (X ⟶ Y) → Prop)
  (hP₁ : ∀ ⦃X X' : C₁'⦄ (φ : i₁.obj X ⟶ i₁.obj X'), (∃ ψ, i₁.map ψ = φ) ↔ P₁ φ)
  (hFP : ∀ ⦃X Y : C₁⦄ (φ : X ⟶ Y), P₁ φ ↔ P₂ (F.map φ))
  (hobj' : ∀ Y : C₂', ∃ X : C₁', Nonempty (F.obj (i₁.obj X) ≅ i₂.obj Y))

include hP₁ hFP hobj' in
/-- **`H` is an equivalence.** -/
theorem liftFunctor_isEquivalence [i₁.Faithful] [F.IsEquivalence] :
    (liftFunctor i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj).IsEquivalence where
  faithful := ⟨fun {X X'} f g h => by
    have h' := congrArg i₂.map h
    change i₂.map (liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj f) =
      i₂.map (liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj g) at h'
    rw [i₂_map_liftMap, i₂_map_liftMap] at h'
    simp only [cancel_epi, cancel_mono] at h'
    exact i₁.map_injective (F.map_injective h')⟩
  full := ⟨fun {X X'} ψ => by
    let φ := (liftIso i₁ i₂ F hobj X).hom ≫ i₂.map ψ ≫ (liftIso i₁ i₂ F hobj X').inv
    have hφ : P₂ φ := hcomp _ _ (hiso _ inferInstance)
      (hcomp _ _ ((hP₂ _).1 ⟨ψ, rfl⟩) (hiso _ inferInstance))
    have hχ : P₁ (F.preimage φ) := (hFP _).2 (by rw [F.map_preimage]; exact hφ)
    obtain ⟨f, hf⟩ := (hP₁ _).2 hχ
    refine ⟨f, i₂.map_injective ?_⟩
    change i₂.map (liftMap i₁ i₂ F P₂ hP₂ hcomp hiso hF hobj f) = _
    rw [i₂_map_liftMap, hf, F.map_preimage]
    simp only [φ, Category.assoc]
    erw [Iso.inv_hom_id (liftIso i₁ i₂ F hobj X'), Iso.inv_hom_id_assoc]
    exact Category.comp_id (i₂.map ψ)⟩
  essSurj := ⟨fun Y => by
    obtain ⟨X, ⟨e⟩⟩ := hobj' Y
    exact ⟨X, nonempty_iso_of_iso i₂ P₂ hP₂ hiso ((liftIso i₁ i₂ F hobj X).symm ≪≫ e)⟩⟩

end Lift

namespace Model

/-! ### Objects of the hull ([EtTh], Remark 3.6.3) -/

section Objects

variable {D : Type u} [Category.{v} D]
variable {Φ Φ' : DivMonoid.{w} D} {B B' : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {divB' : DivHom B' Φ'.toGrpOn}
variable {ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- **Objects linked to the hull by base-field-theoretic pre-steps lie in its essential image**
([EtTh], Remark 3.6.3): if `s : E → W` and `t : E → (A, ι z)` are base-field-theoretic pre-steps,
then `W ≅ (A_W, ι y)` for some `y`. -/
theorem exists_iso_hullObj_of_preSteps {E W : Model Φ B divB} {A : D} {z : Φ'.obj A}
    (s : E ⟶ W) (t : E ⟶ ⟨A, ιΦ.app A z⟩) (hs : IsPreStep 𝐏 s) (ht : IsPreStep 𝐏 t)
    (hsb : IsBsFld ιΦ s) (htb : IsBsFld ιΦ t) :
    ∃ y : Φ'.obj W.base, Nonempty (W ≅ ⟨W.base, ιΦ.app _ y⟩) := by
  obtain ⟨a, -, ha⟩ := hsb
  obtain ⟨b, -, hb⟩ := htb
  have hs1 : s.deg = 1 := hs.1
  have ht1 : t.deg = 1 := ht.1
  haveI : IsIso s.base := hs.2
  let g := inv s.base
  have rs := s.rel
  have rt := t.rel
  rw [hs1, PNat.one_coe, one_smul, ← ha] at rs
  rw [ht1, PNat.one_coe, one_smul, ← hb] at rt
  change E.α + ιΦ.app _ b = Φ.pb t.base (ιΦ.app A z) + divB.app _ t.u at rt
  rw [← ιΦ.natural] at rt
  let y : Φ'.obj W.base := Φ'.pb g (a - b + Φ'.pb t.base z)
  let u : B.obj W.base := B.pb g (t.u - s.u)
  have key : Φ.pb s.base W.α = ιΦ.app _ a - ιΦ.app _ b + ιΦ.app _ (Φ'.pb t.base z) +
      divB.app _ t.u - divB.app _ s.u := by
    linear_combination (norm := module) rt - rs
  have hW : W.α = Φ.pb g (Φ.pb s.base W.α) := (GrpOn.pb_inv_pb _ _ _).symm
  have hrel : W.α + 0 = Φ.pb (𝟙 _) (ιΦ.app _ y) + divB.app _ u := by
    rw [add_zero, GrpOn.pb_id', hW, key]
    simp only [y, u, ιΦ.natural, divB.natural, map_add, map_sub]
    abel_nf
  let m : W ⟶ ⟨W.base, ιΦ.app _ y⟩ := mk1 (𝟙 _) 0 (Φ.pos _).zero_mem u hrel
  haveI : IsIso m := isIso_of m rfl (by simp only [m, mk1_base]; infer_instance) rfl
  exact ⟨y, ⟨asIso m⟩⟩

/-- **Frobenius-trivial objects lie in the essential image of the hull**: an object with a
base-identity endomorphism with zero divisor and Frobenius degree `2` is isomorphic to
`(A, ι 0)`. -/
theorem exists_iso_hullObj_of_frob {Z : Model Φ B divB} (ψ : Z ⟶ Z) (hb : ψ.base = 𝟙 _)
    (h0 : ψ.div = 0) (h2 : ψ.deg = 2) :
    Nonempty (Z ≅ (⟨Z.base, ιΦ.app _ 0⟩ : Model Φ B divB)) := by
  have r := ψ.rel
  rw [hb, h0, h2, GrpOn.pb_id', add_zero] at r
  have hrel : Z.α + 0 = Φ.pb (𝟙 _) (ιΦ.app _ 0) + divB.app _ ψ.u := by
    rw [map_zero, map_zero, zero_add, add_zero]
    have : ((2 : ℕ+) : ℕ) • Z.α = Z.α + Z.α := by
      rw [show ((2 : ℕ+) : ℕ) = 2 from rfl, two_nsmul]
    rw [this] at r
    exact add_left_cancel r
  let m : Z ⟶ ⟨Z.base, ιΦ.app _ 0⟩ := mk1 (𝟙 _) 0 (Φ.pos _).zero_mem ψ.u hrel
  haveI : IsIso m := isIso_of m rfl (by simp only [m, mk1_base]; infer_instance) rfl
  exact ⟨asIso m⟩

/-- **Every object of the hull is linked to `(A, ι 0)`** by two base-field-theoretic pre-steps
([EtTh], Remark 3.6.3). -/
theorem hullObj_linked (hpos : ∀ A x, x ∈ Φ'.pos A → ιΦ.app A x ∈ Φ.pos A)
    (X' : Model Φ' B' divB') :
    ∃ (E : Model Φ B divB) (s : E ⟶ ⟨X'.base, ιΦ.app _ X'.α⟩) (t : E ⟶ ⟨X'.base, ιΦ.app _ 0⟩),
      IsPreStep 𝐏 s ∧ IsPreStep 𝐏 t ∧ IsBsFld ιΦ s ∧ IsBsFld ιΦ t := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Φ'.generating X'.α
  refine ⟨⟨X'.base, -ιΦ.app _ q⟩, mk1 (𝟙 _) (ιΦ.app _ p) (hpos _ _ hp) 0 ?_,
    mk1 (𝟙 _) (ιΦ.app _ q) (hpos _ _ hq) 0 ?_, isPreStep_mk1 _ _ _ _ _, isPreStep_mk1 _ _ _ _ _,
    ⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩⟩
  · rw [hpq, GrpOn.pb_id', map_zero, add_zero, map_sub]
    abel_nf
  · rw [GrpOn.pb_id', map_zero, map_zero, add_zero, neg_add_cancel]

end Objects

/-! ### The equivalence of hulls -/

section HullEquiv

variable {D₁ : Type u₁} [Category.{v} D₁]
variable {Φ₁ Φ₁' : DivMonoid.{w} D₁} {B₁ B₁' : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
  {divB₁' : DivHom B₁' Φ₁'.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂]
variable {Φ₂ Φ₂' : DivMonoid.{w} D₂} {B₂ B₂' : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}
  {divB₂' : DivHom B₂' Φ₂'.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (ιΦ₁ : DivHom Φ₁'.toGrpOn Φ₁.toGrpOn) (ιB₁ : DivHom B₁' B₁)
  (hpos₁ : ∀ A x, x ∈ Φ₁'.pos A → ιΦ₁.app A x ∈ Φ₁.pos A)
  (hdiv₁ : ∀ A x, divB₁.app A (ιB₁.app A x) = ιΦ₁.app A (divB₁'.app A x))
  (hιΦ₁ : ∀ A, Function.Injective (ιΦ₁.app A)) (hιB₁ : ∀ A, Function.Injective (ιB₁.app A))
  (hfib₁ : ∀ A (b : B₁.obj A) (y : Φ₁'.obj A), divB₁.app A b = ιΦ₁.app A y →
    ∃ b' : B₁'.obj A, ιB₁.app A b' = b)
variable (ιΦ₂ : DivHom Φ₂'.toGrpOn Φ₂.toGrpOn) (ιB₂ : DivHom B₂' B₂)
  (hpos₂ : ∀ A x, x ∈ Φ₂'.pos A → ιΦ₂.app A x ∈ Φ₂.pos A)
  (hdiv₂ : ∀ A x, divB₂.app A (ιB₂.app A x) = ιΦ₂.app A (divB₂'.app A x))
  (hιΦ₂ : ∀ A, Function.Injective (ιΦ₂.app A)) (hιB₂ : ∀ A, Function.Injective (ιB₂.app A))
  (hfib₂ : ∀ A (b : B₂.obj A) (y : Φ₂'.obj A), divB₂.app A b = ιΦ₂.app A y →
    ∃ b' : B₂'.obj A, ιB₂.app A b' = b)
variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] (c : TypeCorresp F)
  (σ : ℕ+ ≃* ℕ+) (hσ : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), (F.map φ).deg = σ φ.deg)
  (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y),
    φ.base = φ'.base ↔ (F.map φ).base = (F.map φ').base)
  (hbs : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ))

/-- The base-identity endomorphism `(n, id, 0, 0)` of `(A, ι 0)`. -/
def frobZero {Φ Φ' : DivMonoid.{w} D₁} {B : GrpOn.{w} D₁} {divB : DivHom B Φ.toGrpOn}
    (ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn) (A : D₁) (n : ℕ+) :
    (⟨A, ιΦ.app _ 0⟩ : Model Φ B divB) ⟶ ⟨A, ιΦ.app _ 0⟩ :=
  mk' n (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp)

omit [F.IsEquivalence] in
include c σ hσ hbe in
/-- **`F` maps `(A, ι 0)` into the essential image of the hull** (Frobenius-trivial objects are
preserved, [FrdI], Corollary 4.11(iv)). -/
theorem map_zero_iso_hull (A : D₁) :
    Nonempty (F.obj ⟨A, ιΦ₁.app _ 0⟩ ≅
      (⟨(F.obj ⟨A, ιΦ₁.app _ 0⟩).base, ιΦ₂.app _ 0⟩ : Model Φ₂ B₂ divB₂)) := by
  let fr := frobZero (B := B₁) (divB := divB₁) ιΦ₁ A (σ.symm 2)
  have hfr : IsFrobeniusType 𝐏₁ fr :=
    (isFrobeniusType_iff _).2 ⟨rfl, by simp only [fr, frobZero, mk'_base]; infer_instance⟩
  have hb : (F.map fr).base = 𝟙 _ := by
    have := (hbe fr (𝟙 _)).1 rfl
    rwa [F.map_id] at this
  refine exists_iso_hullObj_of_frob (F.map fr) hb
    ((isFrobeniusType_iff _).1 ((c.frobType fr).1 hfr)).1 ?_
  rw [hσ]
  exact σ.apply_symm_apply 2

include c σ hσ hbe in
/-- **Objects of `C₁` mapped by `F` into `(A, ι 0)` are in the essential image of the hull.** -/
theorem iso_hull_of_map_iso_zero {Z : Model Φ₁ B₁ divB₁} {A₂ : D₂}
    (e : F.obj Z ≅ (⟨A₂, ιΦ₂.app _ 0⟩ : Model Φ₂ B₂ divB₂)) :
    Nonempty (Z ≅ (⟨Z.base, ιΦ₁.app _ 0⟩ : Model Φ₁ B₁ divB₁)) := by
  let fr₂ := frobZero (B := B₂) (divB := divB₂) ιΦ₂ A₂ (σ 2)
  let ψ := F.preimage (e.hom ≫ fr₂ ≫ e.inv)
  have hFψ : F.map ψ = e.hom ≫ fr₂ ≫ e.inv := F.map_preimage _
  obtain ⟨he1, hei, he0⟩ := (isIso_iff e.hom).1 inferInstance
  obtain ⟨hf1, hfi, hf0⟩ := (isIso_iff e.inv).1 inferInstance
  have hb : ψ.base = 𝟙 _ := by
    refine (hbe ψ (𝟙 _)).2 ?_
    rw [hFψ, F.map_id, comp_base, comp_base]
    simp only [fr₂, frobZero, mk'_base, Category.id_comp, id_base]
    rw [← comp_base, e.hom_inv_id, id_base]
  have hfr : IsFrobeniusType 𝐏₂ (F.map ψ) := by
    rw [isFrobeniusType_iff, hFψ]
    refine ⟨?_, ?_⟩
    · simp only [comp_div, he0, hf0, fr₂, frobZero, mk'_div, map_zero, smul_zero, add_zero]
    · simp only [comp_base, fr₂, frobZero, mk'_base, Category.id_comp]
      infer_instance
  have h0 : ψ.div = 0 := ((isFrobeniusType_iff _).1 ((c.frobType ψ).2 hfr)).1
  have h2 : ψ.deg = 2 := by
    apply σ.injective
    rw [← hσ, hFψ, comp_deg, comp_deg, he1, hf1, one_mul, mul_one]
    rfl
  exact exists_iso_hullObj_of_frob ψ hb h0 h2

omit [F.IsEquivalence] in
include c σ hσ hbe hbs hpos₁ in
/-- **`F` maps the hull of `C₁` into the essential image of the hull of `C₂`** ([EtTh], proof of
Corollary 3.8(ii)). -/
theorem map_hullObj (X' : Model Φ₁' B₁' divB₁') :
    ∃ Y' : Model Φ₂' B₂' divB₂', Nonempty (F.obj ((hullFunctor ιΦ₁ ιB₁ hpos₁ hdiv₁).obj X') ≅
      (hullFunctor ιΦ₂ ιB₂ hpos₂ hdiv₂).obj Y') := by
  obtain ⟨E, s, t, hs, ht, hsb, htb⟩ := hullObj_linked (divB := divB₁) (divB' := divB₁') hpos₁ X'
  obtain ⟨e⟩ := map_zero_iso_hull ιΦ₁ ιΦ₂ F c σ hσ hbe X'.base
  have ht' : IsPreStep 𝐏₂ (F.map t ≫ e.hom) :=
    (isPreStep_respIso (toElem Φ₂ B₂ divB₂)).right _ e ((c.preStep t).1 ht)
  have htb' : IsBsFld ιΦ₂ (F.map t ≫ e.hom) :=
    isBsFld_comp ιΦ₂ ((hbs t).1 htb) (isBsFld_of_isIso ιΦ₂ e.hom)
  obtain ⟨y, ⟨i⟩⟩ := exists_iso_hullObj_of_preSteps (F.map s) (F.map t ≫ e.hom)
    ((c.preStep s).1 hs) ht' ((hbs s).1 hsb) htb'
  exact ⟨⟨_, y⟩, ⟨i⟩⟩

include c σ hσ hbe hbs hpos₂ in
/-- **Every object of the hull of `C₂` comes from the hull of `C₁`** up to isomorphism. -/
theorem exists_map_hullObj (Y' : Model Φ₂' B₂' divB₂') :
    ∃ X' : Model Φ₁' B₁' divB₁', Nonempty (F.obj ((hullFunctor ιΦ₁ ιB₁ hpos₁ hdiv₁).obj X') ≅
      (hullFunctor ιΦ₂ ιB₂ hpos₂ hdiv₂).obj Y') := by
  obtain ⟨E, s, t, hs, ht, hsb, htb⟩ := hullObj_linked (divB := divB₂) (divB' := divB₂') hpos₂ Y'
  let ε := fun P : Model Φ₂ B₂ divB₂ => F.objObjPreimageIso P
  have hc : ∀ {P Q : Model Φ₂ B₂ divB₂} (g : P ⟶ Q),
      F.map (F.inv.map g) = (ε P).hom ≫ g ≫ (ε Q).inv := fun g => F.map_preimage _
  have hpre' : ∀ {P Q : Model Φ₂ B₂ divB₂} (g : P ⟶ Q), IsPreStep 𝐏₂ g →
      IsPreStep 𝐏₁ (F.inv.map g) := by
    intro P Q g hg
    refine (c.preStep _).2 ?_
    rw [hc]
    exact (isPreStep_respIso (toElem Φ₂ B₂ divB₂)).left (ε P) _
      ((isPreStep_respIso (toElem Φ₂ B₂ divB₂)).right g (ε Q).symm hg)
  have hbs' : ∀ {P Q : Model Φ₂ B₂ divB₂} (g : P ⟶ Q), IsBsFld ιΦ₂ g →
      IsBsFld ιΦ₁ (F.inv.map g) := by
    intro P Q g hg
    refine (hbs _).2 ?_
    rw [hc]
    exact isBsFld_comp ιΦ₂ (isBsFld_of_isIso ιΦ₂ (ε P).hom)
      (isBsFld_comp ιΦ₂ hg (isBsFld_of_isIso ιΦ₂ (ε Q).inv))
  obtain ⟨z⟩ := iso_hull_of_map_iso_zero ιΦ₁ ιΦ₂ F c σ hσ hbe (ε _)
  have ht' : IsPreStep 𝐏₁ (F.inv.map t ≫ z.hom) :=
    (isPreStep_respIso (toElem Φ₁ B₁ divB₁)).right _ z (hpre' t ht)
  have htb' : IsBsFld ιΦ₁ (F.inv.map t ≫ z.hom) :=
    isBsFld_comp ιΦ₁ (hbs' t htb) (isBsFld_of_isIso ιΦ₁ z.hom)
  obtain ⟨x, ⟨i⟩⟩ := exists_iso_hullObj_of_preSteps (F.inv.map s) (F.inv.map t ≫ z.hom)
    (hpre' s hs) ht' (hbs' s hsb) htb'
  exact ⟨⟨_, x⟩, ⟨F.mapIso i.symm ≪≫ ε _⟩⟩

/-- **The induced functor of hulls** `C₁^bs-fld ⥤ C₂^bs-fld` ([EtTh], Corollary 3.8(ii);
[IUTchI], Example 3.2(iii)). -/
noncomputable def hullEquiv : Model Φ₁' B₁' divB₁' ⥤ Model Φ₂' B₂' divB₂' :=
  haveI := hullFunctor_faithful ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂
  liftFunctor (hullFunctor ιΦ₁ ιB₁ hpos₁ hdiv₁) (hullFunctor ιΦ₂ ιB₂ hpos₂ hdiv₂) F
    (fun _ _ φ => IsBsFld ιΦ₂ φ)
    (fun _ _ φ => exists_hullFunctor_map_iff ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hfib₂ φ)
    (fun _ _ _ _ _ h h' => isBsFld_comp ιΦ₂ h h')
    (fun _ _ φ h => by haveI := h; exact isBsFld_of_isIso ιΦ₂ φ)
    (fun _ _ f => (hbs _).1 (hullFunctor_map_isBsFld ιΦ₁ ιB₁ hpos₁ hdiv₁ f))
    (map_hullObj ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ F c σ hσ hbe hbs)

/-- **Compatibility** of the equivalence of hulls with `F`:
`(C₁^bs-fld ⥤ C₁ ⥤ C₂) ≅ (C₁^bs-fld ⥤ C₂^bs-fld ⥤ C₂)`. -/
noncomputable def hullEquivIso :
    hullFunctor ιΦ₁ ιB₁ hpos₁ hdiv₁ ⋙ F ≅
      hullEquiv ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe hbs ⋙
        hullFunctor ιΦ₂ ιB₂ hpos₂ hdiv₂ :=
  haveI := hullFunctor_faithful ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂
  liftCompIso _ _ _ _ _ _ _ _ _

include hιΦ₁ hιB₁ hfib₁ in
/-- **[EtTh], Corollary 3.8(ii); [IUTchI], Example 3.2(iii)**: the induced functor of
base-field-theoretic hulls is an equivalence of categories. -/
theorem hullEquiv_isEquivalence :
    (hullEquiv ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe
      hbs).IsEquivalence :=
  haveI := hullFunctor_faithful ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂
  haveI := hullFunctor_faithful ιΦ₁ ιB₁ hpos₁ hdiv₁ hιΦ₁ hιB₁
  liftFunctor_isEquivalence _ _ _ _ _ _ _ _ _ (fun _ _ φ => IsBsFld ιΦ₁ φ)
    (fun _ _ φ => exists_hullFunctor_map_iff ιΦ₁ ιB₁ hpos₁ hdiv₁ hιΦ₁ hfib₁ φ) hbs
    (exists_map_hullObj ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ F c σ hσ hbe hbs)

/-- The projection to the base of the hull is that of `C` restricted to the hull. -/
def hullBaseIso {D : Type u} [Category.{v} D] {Φ Φ' : DivMonoid.{w} D} {B B' : GrpOn.{w} D}
    {divB : DivHom B Φ.toGrpOn} {divB' : DivHom B' Φ'.toGrpOn} (ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn)
    (ιB : DivHom B' B) (hpos : ∀ A x, x ∈ Φ'.pos A → ιΦ.app A x ∈ Φ.pos A)
    (hdiv : ∀ A x, divB.app A (ιB.app A x) = ιΦ.app A (divB'.app A x)) :
    hullFunctor ιΦ ιB hpos hdiv ⋙ toElem Φ B divB ⋙ Elem.proj ≅
      toElem Φ' B' divB' ⋙ Elem.proj :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
    erw [Category.comp_id, Category.id_comp]
    rfl)

omit [F.IsEquivalence] in
/-- **[IUTchI], Example 3.2(vi)(d)**: the base functor of `F` (the reconstruction of `D_v` from
`F_v`, [FrdI], Theorem 3.4(v)) is a base functor of the induced equivalence of hulls (the
reconstruction of `D_v` from `C_v`): both reconstructions agree. -/
theorem hullEquiv_base {G : D₁ ⥤ D₂}
    (e : F ⋙ toElem Φ₂ B₂ divB₂ ⋙ Elem.proj ≅ (toElem Φ₁ B₁ divB₁ ⋙ Elem.proj) ⋙ G) :
    Nonempty (hullEquiv ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe hbs ⋙
        toElem Φ₂' B₂' divB₂' ⋙ Elem.proj ≅ (toElem Φ₁' B₁' divB₁' ⋙ Elem.proj) ⋙ G) := by
  let H := hullEquiv ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe hbs
  exact ⟨Functor.isoWhiskerLeft H (hullBaseIso ιΦ₂ ιB₂ hpos₂ hdiv₂).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (hullEquivIso ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂
      F c σ hσ hbe hbs).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (hullBaseIso ιΦ₁ ιB₁ hpos₁ hdiv₁) G⟩

end HullEquiv

/-! ### Over bases of FSM-type -/

section FSM

variable {D₁ : Type u₁} [Category.{v} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ Φ₁' : DivMonoid.{w} D₁} {B₁ B₁' : GrpOn.{w} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
  {divB₁' : DivHom B₁' Φ₁'.toGrpOn}
variable {D₂ : Type u₂} [Category.{v} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ Φ₂' : DivMonoid.{w} D₂} {B₂ B₂' : GrpOn.{w} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}
  {divB₂' : DivHom B₂' Φ₂'.toGrpOn}

/-- **[EtTh], Corollary 3.8(ii); [IUTchI], Example 3.2(iii),(vi)(d)** over slim bases of
FSM-type: every equivalence `F : C₁ ⥤ C₂` of model Frobenioids whose hulls satisfy `BsFldChar`
induces an equivalence of the base-field-theoretic hulls compatible with `F` and lying over the
base functor of `F`. -/
theorem exists_hullEquiv_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂)
    (ιΦ₁ : DivHom Φ₁'.toGrpOn Φ₁.toGrpOn) (ιB₁ : DivHom B₁' B₁)
    (hpos₁ : ∀ A x, x ∈ Φ₁'.pos A → ιΦ₁.app A x ∈ Φ₁.pos A)
    (hdiv₁ : ∀ A x, divB₁.app A (ιB₁.app A x) = ιΦ₁.app A (divB₁'.app A x))
    (hιΦ₁ : ∀ A, Function.Injective (ιΦ₁.app A)) (hιB₁ : ∀ A, Function.Injective (ιB₁.app A))
    (hfib₁ : ∀ A (b : B₁.obj A) (y : Φ₁'.obj A), divB₁.app A b = ιΦ₁.app A y →
      ∃ b' : B₁'.obj A, ιB₁.app A b' = b)
    (ιΦ₂ : DivHom Φ₂'.toGrpOn Φ₂.toGrpOn) (ιB₂ : DivHom B₂' B₂)
    (hpos₂ : ∀ A x, x ∈ Φ₂'.pos A → ιΦ₂.app A x ∈ Φ₂.pos A)
    (hdiv₂ : ∀ A x, divB₂.app A (ιB₂.app A x) = ιΦ₂.app A (divB₂'.app A x))
    (hιΦ₂ : ∀ A, Function.Injective (ιΦ₂.app A)) (hιB₂ : ∀ A, Function.Injective (ιB₂.app A))
    (hfib₂ : ∀ A (b : B₂.obj A) (y : Φ₂'.obj A), divB₂.app A b = ιΦ₂.app A y →
      ∃ b' : B₂'.obj A, ιB₂.app A b' = b)
    (hchar₁ : BsFldChar divB₁ ιΦ₁) (hchar₂ : BsFldChar divB₂ ιΦ₂)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    ∃ H : Model Φ₁' B₁' divB₁' ⥤ Model Φ₂' B₂' divB₂', H.IsEquivalence ∧
      Nonempty (hullFunctor ιΦ₁ ιB₁ hpos₁ hdiv₁ ⋙ F ≅ H ⋙ hullFunctor ιΦ₂ ιB₂ hpos₂ hdiv₂) ∧
      ∃ G : D₁ ⥤ D₂, Nonempty (F ⋙ toElem Φ₂ B₂ divB₂ ⋙ Elem.proj ≅
          (toElem Φ₁ B₁ divB₁ ⋙ Elem.proj) ⋙ G) ∧
        Nonempty (H ⋙ toElem Φ₂' B₂' divB₂' ⋙ Elem.proj ≅
          (toElem Φ₁' B₁' divB₁' ⋙ Elem.proj) ⋙ G) := by
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have c' := typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv
  obtain ⟨σ, hσ⟩ := exists_degEquiv F (fun _ _ φ h => (c.linear φ).1 h)
    (fun _ _ φ h => (c'.linear φ).1 h)
  have hbe := base_eq_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ F
  have hbs : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), IsBsFld ιΦ₁ φ ↔ IsBsFld ιΦ₂ (F.map φ) :=
    fun _ _ φ => isBsFld_map_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ hchar₁ hchar₂ F φ
  obtain ⟨G, ⟨e⟩⟩ := thm34_fsm_preservesBase hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₂ F
  exact ⟨_, hullEquiv_isEquivalence ιΦ₁ ιB₁ hpos₁ hdiv₁ hιΦ₁ hιB₁ hfib₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂
      hιB₂ hfib₂ F c σ hσ hbe hbs,
    ⟨hullEquivIso ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe hbs⟩,
    G, ⟨e⟩, hullEquiv_base ιΦ₁ ιB₁ hpos₁ hdiv₁ ιΦ₂ ιB₂ hpos₂ hdiv₂ hιΦ₂ hιB₂ hfib₂ F c σ hσ hbe
      hbs e⟩

end FSM

end Model

end Frobenioid

end Iut
