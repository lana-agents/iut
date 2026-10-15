/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34

/-!
# Equivalences of model Frobenioids induce order isomorphisms of divisor monoids

[FrdI], Corollary 4.11(iii) asserts that an equivalence `Ψ : C₁ ≌ C₂` of Frobenioids induces an
isomorphism of divisor monoids `Ψ_Φ : Φ₁ ≅ Φ₂ ∘ Ψ_Base`. The input is the category-theoreticity
of pre-steps (Theorem 3.4(ii)) together with the equivalence of categories of [FrdI], Definition
1.3(iii)(d), between co-angular pre-steps out of `A` and `Order(Φ(A_D))`.

For a model Frobenioid and an equivalence `F` that matches pre-steps (e.g. under the hypotheses
of `Iut/Frobenioid/Thm34.lean`, `Model.typeCorresp`), this file constructs for every object `X`
the bijection (`Model.divEquiv`)

  `τ_X : Φ₁(A_X) ≃ Φ₂(A_{F X})`,  `z ↦ Div(F(s_z))`,  `s_z = (1, id, z, 0) : X → (A_X, α_X + z)`,

and proves:

* `Model.div_map_preStep`: `Div(F φ) = τ_X(Div φ)` for **every** pre-step `φ` out of `X`;
* `Model.divEquiv_le_iff`: `τ_X` is an **order isomorphism** for the orders `a ≤ b ⟺ b − a ∈ Φ`
  of [FrdI] §0;
* `Model.divEquiv_zero`: `τ_X(0) = 0`.

The additivity of `τ_X` (the monoid structure in Corollary 4.11(iii)) needs further hypotheses in
[FrdI] ("perf-factorial", Frobenius compatibility) and is not treated here; when `Φ(A) ≅ ℤ_{≥0}`
(the `p`-adic Frobenioids) an order isomorphism is automatically the identity.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

namespace Model

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

/-- The step `s_z = (1, id, z, 0) : X → (A_X, α_X + z)`. -/
def stepTo (X : Model Φ₁ B₁ divB₁) (z : Φ₁.obj X.base) (hz : z ∈ Φ₁.pos X.base) :
    X ⟶ ⟨X.base, X.α + z⟩ :=
  mk1 (𝟙 _) z hz 0 (by simp)

lemma stepTo_isPreStep (X : Model Φ₁ B₁ divB₁) (z : Φ₁.obj X.base) (hz : z ∈ Φ₁.pos X.base) :
    IsPreStep 𝐏₁ (stepTo X z hz) :=
  isPreStep_mk1 _ _ _ _ _

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
variable (hpre : Corresp F (fun _ _ φ => IsPreStep (toElem Φ₁ B₁ divB₁) φ)
  (fun _ _ φ => IsPreStep (toElem Φ₂ B₂ divB₂) φ))

/-- `τ_X(z) = Div(F(s_z))`. -/
def divMap (X : Model Φ₁ B₁ divB₁) (z : Φ₁.obj X.base) (hz : z ∈ Φ₁.pos X.base) :
    Φ₂.obj (F.obj X).base :=
  (F.map (stepTo X z hz)).div

omit [F.IsEquivalence] in
lemma divMap_mem (X : Model Φ₁ B₁ divB₁) (z : Φ₁.obj X.base) (hz : z ∈ Φ₁.pos X.base) :
    divMap F X z hz ∈ Φ₂.pos (F.obj X).base :=
  (F.map (stepTo X z hz)).div_mem

omit [F.IsEquivalence] in
/-- The image of an isomorphism has zero divisor and degree `1`. -/
lemma map_iso_div_deg {Y Y' : Model Φ₁ B₁ divB₁} (χ : Y ⟶ Y') [IsIso χ] :
    (F.map χ).div = 0 ∧ (F.map χ).deg = 1 :=
  ⟨Div_of_isIso (P := 𝐏₂) (F.map χ), degFr_of_isIso (P := 𝐏₂) (F.map χ)⟩

omit [F.IsEquivalence] in
/-- **`Div(F φ) = τ_X(Div φ)` for every pre-step `φ` out of `X`.** -/
theorem div_map_preStep {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) (hφ : IsPreStep 𝐏₁ φ) :
    (F.map φ).div = divMap F X φ.div φ.div_mem := by
  obtain ⟨χ, -, hχ, hc⟩ := coslice_full (stepTo X φ.div φ.div_mem) φ
    (stepTo_isPreStep X _ _) hφ (Φ₁.le_refl _)
  have h0 : χ.div = 0 := by
    have := congrArg Hom.div hc
    simp only [comp_div, stepTo, mk1_base, mk1_div, GrpOn.pb_id'] at this
    rw [show χ.deg = 1 from hχ.1, PNat.one_coe, one_smul] at this
    exact add_eq_right.mp this
  haveI : IsIso χ := isIso_of χ hχ.1 hχ.2 h0
  obtain ⟨hd, hg⟩ := map_iso_div_deg F χ
  conv_lhs => rw [← hc]
  rw [F.map_comp, comp_div, hd, hg, map_zero, zero_add, PNat.one_coe, one_smul]
  rfl

include hpre in
/-- **`τ_X` is an order embedding**: `τ_X(z) ≤ τ_X(z') ⟺ z ≤ z'`. -/
theorem divMap_le_iff (X : Model Φ₁ B₁ divB₁) {z z' : Φ₁.obj X.base} (hz : z ∈ Φ₁.pos X.base)
    (hz' : z' ∈ Φ₁.pos X.base) :
    Φ₂.le (divMap F X z hz) (divMap F X z' hz') ↔ Φ₁.le z z' := by
  constructor
  · intro h
    obtain ⟨χ', -, hχ', hc'⟩ := coslice_full (F.map (stepTo X z hz)) (F.map (stepTo X z' hz'))
      ((hpre _).1 (stepTo_isPreStep X z hz)) ((hpre _).1 (stepTo_isPreStep X z' hz')) h
    let χ := F.preimage χ'
    have hχ : IsPreStep 𝐏₁ χ := (hpre χ).2 (by simpa [χ] using hχ')
    have hc : stepTo X z hz ≫ χ = stepTo X z' hz' := F.map_injective (by simp [χ, hc'])
    have := congrArg Hom.div hc
    simp only [comp_div, stepTo, mk1_base, mk1_div, GrpOn.pb_id'] at this
    rw [show χ.deg = 1 from hχ.1, PNat.one_coe, one_smul] at this
    change z' - z ∈ Φ₁.pos X.base
    rw [← this, add_sub_cancel_right]
    exact χ.div_mem
  · intro h
    obtain ⟨χ, -, hχ, hc⟩ := coslice_full (stepTo X z hz) (stepTo X z' hz')
      (stepTo_isPreStep X z hz) (stepTo_isPreStep X z' hz') h
    have hFχ := (hpre χ).1 hχ
    have := congrArg (fun ψ => (F.map ψ).div) hc
    simp only [F.map_comp, comp_div] at this
    rw [show (F.map χ).deg = 1 from hFχ.1, PNat.one_coe, one_smul] at this
    change (F.map (stepTo X z' hz')).div - (F.map (stepTo X z hz)).div ∈ Φ₂.pos (F.obj X).base
    rw [← this, add_sub_cancel_right]
    exact Φ₂.pb_mem _ (F.map χ).div_mem

include hpre in
/-- **`τ_X` is surjective onto `Φ₂(A_{F X})`.** -/
theorem divMap_surjective (X : Model Φ₁ B₁ divB₁) {y : Φ₂.obj (F.obj X).base}
    (hy : y ∈ Φ₂.pos (F.obj X).base) :
    ∃ (z : Φ₁.obj X.base) (hz : z ∈ Φ₁.pos X.base), divMap F X z hz = y := by
  obtain ⟨Y', ψ, -, hψ, hd⟩ := coslice_surj (F.obj X) y hy
  let e := F.objObjPreimageIso Y'
  let φ : X ⟶ F.objPreimage Y' := F.preimage (ψ ≫ e.inv)
  have hFφ : F.map φ = ψ ≫ e.inv := by simp [φ]
  have hφ : IsPreStep 𝐏₁ φ :=
    (hpre φ).2 (by rw [hFφ]; exact (isPreStep_respIso _).right ψ e.symm hψ)
  refine ⟨φ.div, φ.div_mem, ?_⟩
  have h1 : e.inv.div = 0 := Div_of_isIso (P := 𝐏₂) e.inv
  have h2 : e.inv.deg = 1 := degFr_of_isIso (P := 𝐏₂) e.inv
  rw [← div_map_preStep F φ hφ, hFφ, comp_div, h1, map_zero, zero_add, h2, PNat.one_coe,
    one_smul]
  exact hd

omit [F.IsEquivalence] in
lemma divMap_zero (X : Model Φ₁ B₁ divB₁) : divMap F X 0 (Φ₁.pos _).zero_mem = 0 := by
  have hs : IsIso (stepTo X 0 (Φ₁.pos _).zero_mem) := isIso_of _ rfl
    (by simp only [stepTo, mk1_base]; infer_instance) rfl
  exact (map_iso_div_deg F _).1

include hpre in
/-- **The order isomorphism `τ_X : Φ₁(A_X) ≃ Φ₂(A_{F X})`** induced by `F` ([FrdI], Corollary
4.11(iii), as an isomorphism of ordered sets). -/
noncomputable def divEquiv (X : Model Φ₁ B₁ divB₁) :
    {z // z ∈ Φ₁.pos X.base} ≃ {y // y ∈ Φ₂.pos (F.obj X).base} :=
  Equiv.ofBijective (fun z => ⟨divMap F X z.1 z.2, divMap_mem F X z.1 z.2⟩)
    ⟨fun z z' h => Subtype.ext (Φ₁.le_antisymm
      ((divMap_le_iff F hpre X z.2 z'.2).1 (by rw [Subtype.mk.inj h]; exact Φ₂.le_refl _))
      ((divMap_le_iff F hpre X z'.2 z.2).1 (by rw [Subtype.mk.inj h]; exact Φ₂.le_refl _))),
     fun y => by
      obtain ⟨z, hz, h⟩ := divMap_surjective F hpre X y.2
      exact ⟨⟨z, hz⟩, Subtype.ext h⟩⟩

lemma divEquiv_apply (X : Model Φ₁ B₁ divB₁) (z : {z // z ∈ Φ₁.pos X.base}) :
    (divEquiv F hpre X z).1 = divMap F X z.1 z.2 := rfl

lemma divEquiv_le_iff (X : Model Φ₁ B₁ divB₁) (z z' : {z // z ∈ Φ₁.pos X.base}) :
    Φ₂.le (divEquiv F hpre X z).1 (divEquiv F hpre X z').1 ↔ Φ₁.le z.1 z'.1 :=
  divMap_le_iff F hpre X z.2 z'.2

lemma divEquiv_zero (X : Model Φ₁ B₁ divB₁) :
    (divEquiv F hpre X ⟨0, (Φ₁.pos _).zero_mem⟩).1 = 0 :=
  divMap_zero F X

end Model

end Frobenioid

end Iut
