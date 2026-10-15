/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# [FrdI], Theorem 3.4(v) for model Frobenioids: category-theoreticity of the base

**Theorem** (`Model.thm34_preservesBase`). In the situation of `Iut/Frobenioid/Thm34.lean`
(model Frobenioids over base categories of FSM- and Aut-type, rational functions with torsion of
every order), suppose moreover that the base category `D₂` is **slim** ([FrdI] §0, p. 14: for
every object `A`, the forgetful functor `D_A → D` has no nontrivial automorphisms). Then every
equivalence `F : C₁ ≌ C₂` lies over a functor `F_Base : D₁ → D₂` of base categories, i.e.
`Base ∘ F ≅ F_Base ∘ Base` (`PreservesBase`).

The key step is `Model.base_map_eq_of_base_eq`: **co-objective morphisms with the same base
are mapped to morphisms with the same base** ([FrdI], Theorem 3.4(v): "Ψ preserves
base-equivalent pairs of co-objective morphisms"; in particular base-identity endomorphisms are
preserved, `Model.base_map_eq_id`). Let `φ, φ̃ : X → Y` have the same base. For each object
`t : T → Base(F X)` of `(D₂)_{Base(F X)}` take the pull-back `π'_t : (T, t^* α) → F X`, its
preimage `π_t : P_t → X`, and the factorizations `π_t ≫ φ = γ_t ≫ ρ_t`, `π_t ≫ φ̃ = γ̃_t ≫ ρ_t`
through the same pull-back `ρ_t`, with base-identity `γ_t, γ̃_t` (`facAt`, `pbAt`). Then
`η_t = Base(F γ_t) ∘ Base(F γ̃_t)⁻¹` (transported to `T`) is an automorphism of the forgetful
functor `(D₂)_{Base(F X)} → D₂` (naturality comes from the compatibility of these factorizations
with pull-back morphisms), hence trivial by slimness; at `t = id` this gives
`Base(F φ) = Base(F φ̃)`.

The functor `F_Base` is `A ↦ Base(F(A, 0))`; the isomorphism `Base(F X) ≅ F_Base(Base X)` comes
from the span of pre-steps `X ← (A, −q) → (A, 0)`.

This replaces the 2-categorical argument of [FrdI] (the categories `Q_i`, `R_i` and the slim
exponentiation of Appendix A) by a direct construction in the model.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- **Slim categories** ([FrdI] §0, p. 14): for every object `A`, the natural functor
`D_A → D` is rigid (has no automorphism other than the identity). -/
def IsSlim (D : Type u₁) [Category.{v₁} D] : Prop :=
  ∀ (A : D) (η : Over.forget A ≅ Over.forget A), η = Iso.refl _

namespace Model

section Canonical

variable {D : Type u₁} [Category.{v₁} D]
variable {Φ : DivMonoid.{w₁} D} {B : GrpOn.{w₁} D} {divB : DivHom B Φ.toGrpOn}

instance isIso_base_of_isIso {X Y : Model Φ B divB} (φ : X ⟶ Y) [IsIso φ] : IsIso φ.base :=
  isIso_Base (P := toElem Φ B divB) φ

/-- The domain `(A_X, f^* α_Y)` of the canonical pull-back morphism over `f : A_X → A_Y`. -/
abbrev pbObj (X Y : Model Φ B divB) (f : X.base ⟶ Y.base) : Model Φ B divB :=
  ⟨X.base, Φ.pb f Y.α⟩

/-- The canonical pull-back morphism `(1, f, 0, 0) : (A_X, f^* α_Y) → Y`. -/
def pbAt (X Y : Model Φ B divB) (f : X.base ⟶ Y.base) : pbObj X Y f ⟶ Y :=
  mk1 f 0 (Φ.pos _).zero_mem 0 (by simp)

/-- The base-identity part `(deg ψ, id, Div ψ, u_ψ) : X → (A_X, f^* α_Y)` of `ψ` with base `f`.
-/
def facAt {X Y : Model Φ B divB} (ψ : X ⟶ Y) (f : X.base ⟶ Y.base) (hf : ψ.base = f) :
    X ⟶ pbObj X Y f :=
  mk' ψ.deg (𝟙 _) ψ.div ψ.div_mem ψ.u (by simpa [← hf] using ψ.rel)

lemma facAt_pbAt {X Y : Model Φ B divB} (ψ : X ⟶ Y) (f : X.base ⟶ Y.base) (hf : ψ.base = f) :
    facAt ψ f hf ≫ pbAt X Y f = ψ := by
  ext <;> simp [facAt, pbAt, hf]

lemma facAt_base {X Y : Model Φ B divB} (ψ : X ⟶ Y) (f : X.base ⟶ Y.base) (hf : ψ.base = f) :
    (facAt ψ f hf).base = 𝟙 _ := rfl

/-- The canonical pull-back into `X` over `t : T → A_X`. -/
abbrev pbOver (X : Model Φ B divB) (T : Over X.base) : Model Φ B divB := ⟨T.left, Φ.pb T.hom X.α⟩

/-- The canonical pull-back morphism `(1, t, 0, 0) : (T, t^* α_X) → X`. -/
def pbOverHom (X : Model Φ B divB) (T : Over X.base) : pbOver X T ⟶ X :=
  mk1 T.hom 0 (Φ.pos _).zero_mem 0 (by simp)

/-- The morphism of canonical pull-backs induced by a morphism of `D_{A_X}`. -/
def pbOverMap (X : Model Φ B divB) {T₁ T₂ : Over X.base} (h : T₁ ⟶ T₂) :
    pbOver X T₁ ⟶ pbOver X T₂ :=
  mk1 h.left 0 (Φ.pos _).zero_mem 0 (by simp [← GrpOn.pb_comp', Over.w h])

lemma pbOverMap_comp (X : Model Φ B divB) {T₁ T₂ : Over X.base} (h : T₁ ⟶ T₂) :
    pbOverMap X h ≫ pbOverHom X T₂ = pbOverHom X T₁ := by
  ext <;> simp [pbOverMap, pbOverHom, Over.w h]

/-- The square relating the base-identity parts of `π₁ ≫ φ` and `π₂ ≫ φ` along a morphism
`ĥ : P₁ → P₂` over `X` (`π₁ = ĥ ≫ π₂`, `π₁, π₂` pull-backs): the morphism `(1, Base ĥ, 0, 0)`
between the canonical pull-backs. -/
def pbObjMap {P₁ P₂ Y : Model Φ B divB} (ĥ : P₁ ⟶ P₂) (f₁ : P₁.base ⟶ Y.base)
    (f₂ : P₂.base ⟶ Y.base) (hf : ĥ.base ≫ f₂ = f₁) : pbObj P₁ Y f₁ ⟶ pbObj P₂ Y f₂ :=
  mk1 ĥ.base 0 (Φ.pos _).zero_mem 0 (by simp [← GrpOn.pb_comp', hf])

lemma facAt_pbObjMap {P₁ P₂ X Y : Model Φ B divB} (ĥ : P₁ ⟶ P₂) (π₁ : P₁ ⟶ X) (π₂ : P₂ ⟶ X)
    (hπ₁ : π₁.deg = 1 ∧ π₁.div = 0) (hπ₂ : π₂.deg = 1 ∧ π₂.div = 0) (hh : ĥ ≫ π₂ = π₁)
    (φ : X ⟶ Y) (f₁ : P₁.base ⟶ Y.base) (f₂ : P₂.base ⟶ Y.base) (hf₁ : (π₁ ≫ φ).base = f₁)
    (hf₂ : (π₂ ≫ φ).base = f₂) (hf : ĥ.base ≫ f₂ = f₁) :
    facAt (π₁ ≫ φ) f₁ hf₁ ≫ pbObjMap ĥ f₁ f₂ hf = ĥ ≫ facAt (π₂ ≫ φ) f₂ hf₂ := by
  have hd := congrArg Hom.deg hh
  have hv := congrArg Hom.div hh
  have hu := congrArg Hom.u hh
  simp only [comp_deg, comp_div, comp_u, hπ₁.1, hπ₁.2, hπ₂.1, hπ₂.2] at hd hv hu
  have hd' : ĥ.deg = 1 := by simpa using hd
  simp only [PNat.one_coe, one_smul, map_zero, zero_add] at hv
  ext
  · simp [facAt, pbObjMap, hπ₁.1, hπ₂.1, hd']
  · simp [facAt, pbObjMap]
  · simp only [comp_div, facAt, pbObjMap, mk1_div, mk'_div, mk'_base, mk1_deg,
      PNat.one_coe, one_smul, map_zero, zero_add, mk'_deg, hπ₂.2, ← hh, comp_base,
      GrpOn.pb_comp', smul_zero, add_zero, hv]
  · simp only [comp_u, facAt, pbObjMap, mk1_u, mk'_u, mk'_base, mk1_deg,
      PNat.one_coe, one_smul, map_zero, zero_add, mk'_deg, ← hh, map_add, map_nsmul,
      comp_base, GrpOn.pb_comp', smul_add, hπ₂.1, hd', comp_deg, mul_one]
    abel

end Canonical

section Main

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]
variable (hpb : Corresp F (fun _ _ φ => IsPullback (toElem Φ₁ B₁ divB₁) φ)
  (fun _ _ φ => IsPullback (toElem Φ₂ B₂ divB₂) φ))
variable (hbi : Corresp F (fun _ _ φ => IsBaseIso (toElem Φ₁ B₁ divB₁) φ)
  (fun _ _ φ => IsBaseIso (toElem Φ₂ B₂ divB₂) φ))

/-- The preimage under `F` of the canonical pull-back over `T`. -/
noncomputable abbrev preObj (X : Model Φ₁ B₁ divB₁) (T : Over (F.obj X).base) :
    Model Φ₁ B₁ divB₁ :=
  F.objPreimage (pbOver (F.obj X) T)

/-- The comparison isomorphism `F(P_t) ≅ (T, t^* α)`. -/
noncomputable abbrev preIso (X : Model Φ₁ B₁ divB₁) (T : Over (F.obj X).base) :
    F.obj (preObj F X T) ≅ pbOver (F.obj X) T :=
  F.objObjPreimageIso _

/-- The pull-back `π_t : P_t → X` of `C₁` corresponding to `(T, t)`. -/
noncomputable def preπ (X : Model Φ₁ B₁ divB₁) (T : Over (F.obj X).base) :
    preObj F X T ⟶ X :=
  F.preimage ((preIso F X T).hom ≫ pbOverHom (F.obj X) T)

lemma map_preπ (X : Model Φ₁ B₁ divB₁) (T : Over (F.obj X).base) :
    F.map (preπ F X T) = (preIso F X T).hom ≫ pbOverHom (F.obj X) T := by
  simp [preπ]

include hpb in
lemma preπ_spec (X : Model Φ₁ B₁ divB₁) (T : Over (F.obj X).base) :
    (preπ F X T).deg = 1 ∧ (preπ F X T).div = 0 := by
  refine (isPullback_iff _).mp ((hpb _).2 ?_)
  rw [map_preπ]
  exact isPullback_respIso.left _ _ ((isPullback_iff _).mpr ⟨rfl, rfl⟩)

/-- The morphism `P_{t₁} → P_{t₂}` over `X` induced by a morphism of `(D₂)_{Base(F X)}`. -/
noncomputable def preMap (X : Model Φ₁ B₁ divB₁) {T₁ T₂ : Over (F.obj X).base} (h : T₁ ⟶ T₂) :
    preObj F X T₁ ⟶ preObj F X T₂ :=
  F.preimage ((preIso F X T₁).hom ≫ pbOverMap (F.obj X) h ≫ (preIso F X T₂).inv)

lemma map_preMap (X : Model Φ₁ B₁ divB₁) {T₁ T₂ : Over (F.obj X).base} (h : T₁ ⟶ T₂) :
    F.map (preMap F X h) = (preIso F X T₁).hom ≫ pbOverMap (F.obj X) h ≫ (preIso F X T₂).inv := by
  simp [preMap]

lemma preMap_preπ (X : Model Φ₁ B₁ divB₁) {T₁ T₂ : Over (F.obj X).base} (h : T₁ ⟶ T₂) :
    preMap F X h ≫ preπ F X T₂ = preπ F X T₁ :=
  F.map_injective (by
    simp only [F.map_comp, map_preMap, map_preπ, Category.assoc, Iso.inv_hom_id_assoc,
      pbOverMap_comp])

variable {X Y : Model Φ₁ B₁ divB₁} (φ φ' : X ⟶ Y) (h : φ.base = φ'.base)

/-- The base-identity part `γ_t` of `π_t ≫ φ`. -/
noncomputable def gam (T : Over (F.obj X).base) :
    preObj F X T ⟶ pbObj (preObj F X T) Y ((preπ F X T).base ≫ φ.base) :=
  facAt (preπ F X T ≫ φ) _ rfl

/-- The base-identity part `γ̃_t` of `π_t ≫ φ'` (with the same codomain as `γ_t`). -/
noncomputable def gam' (T : Over (F.obj X).base) :
    preObj F X T ⟶ pbObj (preObj F X T) Y ((preπ F X T).base ≫ φ.base) :=
  facAt (preπ F X T ≫ φ') _ (by simp [h])

omit [F.IsEquivalence] in
include hbi in
lemma isIso_base_map_facAt {P Q : Model Φ₁ B₁ divB₁} (ψ : P ⟶ Q) (f : P.base ⟶ Q.base)
    (hf : ψ.base = f) : IsIso (F.map (facAt ψ f hf)).base :=
  (hbi _).1 (show IsIso (facAt ψ f hf).base by rw [facAt_base]; infer_instance)

include hbi in
lemma isIso_gam (T : Over (F.obj X).base) : IsIso (F.map (gam F φ T)).base :=
  isIso_base_map_facAt F hbi _ _ _

include hbi in
lemma isIso_gam' (T : Over (F.obj X).base) : IsIso (F.map (gam' F φ φ' h T)).base :=
  isIso_base_map_facAt F hbi _ _ _

/-- The component `η_t : T → T`. -/
noncomputable def etaHom (T : Over (F.obj X).base) : T.left ⟶ T.left :=
  haveI := isIso_gam' F hbi φ φ' h T
  (preIso F X T).inv.base ≫ (F.map (gam F φ T)).base ≫ inv (F.map (gam' F φ φ' h T)).base ≫
    (preIso F X T).hom.base

lemma preIso_hom_inv_base (T : Over (F.obj X).base) :
    (preIso F X T).hom.base ≫ (preIso F X T).inv.base = 𝟙 _ := by
  rw [← comp_base, Iso.hom_inv_id]; rfl

lemma preIso_inv_hom_base (T : Over (F.obj X).base) :
    (preIso F X T).inv.base ≫ (preIso F X T).hom.base = 𝟙 _ := by
  rw [← comp_base, Iso.inv_hom_id]; rfl

lemma preIso_inv_hom_base_assoc (T : Over (F.obj X).base) {Z : D₂} (g : T.left ⟶ Z) :
    (preIso F X T).inv.base ≫ (preIso F X T).hom.base ≫ g = g := by
  rw [← Category.assoc, preIso_inv_hom_base, Category.id_comp]

include hpb hbi in
/-- Naturality of `η` along morphisms of `(D₂)_{Base(F X)}`. -/
lemma etaHom_natural {T₁ T₂ : Over (F.obj X).base} (k : T₁ ⟶ T₂) :
    etaHom F hbi φ φ' h T₁ ≫ k.left = k.left ≫ etaHom F hbi φ φ' h T₂ := by
  haveI := isIso_gam' F hbi φ φ' h T₁
  haveI := isIso_gam' F hbi φ φ' h T₂
  set ĥ := preMap F X k
  have hh := preMap_preπ F X k
  have hf : ĥ.base ≫ (preπ F X T₂).base ≫ φ.base = (preπ F X T₁).base ≫ φ.base := by
    rw [← Category.assoc, ← comp_base, hh]
  have S₁ := congrArg (fun ψ => (F.map ψ).base)
    (facAt_pbObjMap ĥ _ _ (preπ_spec F hpb X T₁) (preπ_spec F hpb X T₂) hh φ _ _ rfl rfl hf)
  have S₂ := congrArg (fun ψ => (F.map ψ).base)
    (facAt_pbObjMap ĥ _ _ (preπ_spec F hpb X T₁) (preπ_spec F hpb X T₂) hh φ' _ _
      (by simp [h]) (by simp [h]) hf)
  simp only [F.map_comp, comp_base] at S₁ S₂
  have S₃ : (F.map ĥ).base = (preIso F X T₁).hom.base ≫ k.left ≫ (preIso F X T₂).inv.base := by
    rw [map_preMap]
    simp [pbOverMap]
  change (F.map (gam F φ T₁)).base ≫ _ = (F.map ĥ).base ≫ (F.map (gam F φ T₂)).base at S₁
  change (F.map (gam' F φ φ' h T₁)).base ≫ _ = (F.map ĥ).base ≫
    (F.map (gam' F φ φ' h T₂)).base at S₂
  set q := (F.map (pbObjMap ĥ _ _ hf)).base
  have S₂' : inv (F.map (gam' F φ φ' h T₁)).base ≫ (F.map ĥ).base =
      q ≫ inv (F.map (gam' F φ φ' h T₂)).base := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, S₂, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hk : (preIso F X T₁).hom.base ≫ k.left = (F.map ĥ).base ≫ (preIso F X T₂).hom.base := by
    rw [S₃]
    simp only [Category.assoc, preIso_inv_hom_base, Category.comp_id]
  simp only [etaHom, Category.assoc]
  rw [hk, reassoc_of% S₂', reassoc_of% S₁, S₃]
  simp only [Category.assoc, preIso_inv_hom_base_assoc]


include hbi in
lemma isIso_etaHom (T : Over (F.obj X).base) : IsIso (etaHom F hbi φ φ' h T) := by
  haveI := isIso_gam' F hbi φ φ' h T
  haveI := isIso_gam F hbi φ T
  unfold etaHom
  infer_instance

include hpb hbi h in
/-- **Co-objective morphisms with the same base have images with the same base** ([FrdI],
Theorem 3.4(v)), for a slim base category `D₂`. -/
theorem base_map_eq_of_base_eq (hD : IsSlim D₂) : (F.map φ).base = (F.map φ').base := by
  let η : Over.forget (F.obj X).base ≅ Over.forget (F.obj X).base :=
    NatIso.ofComponents
      (fun T => @asIso _ _ _ _ (etaHom F hbi φ φ' h T) (isIso_etaHom F hbi φ φ' h T))
      (fun k => (etaHom_natural F hpb hbi φ φ' h k).symm)
  have hη := congrArg (fun e : Over.forget (F.obj X).base ≅ Over.forget (F.obj X).base =>
    e.hom.app (Over.mk (𝟙 (F.obj X).base))) (hD _ η)
  simp only [η, NatIso.ofComponents_hom_app, asIso_hom, Iso.refl_hom, NatTrans.id_app] at hη
  set T₀ : Over (F.obj X).base := Over.mk (𝟙 (F.obj X).base)
  haveI := isIso_gam' F hbi φ φ' h T₀
  set k := (preIso F X T₀).hom.base
  set k' := (preIso F X T₀).inv.base
  set g := (F.map (gam F φ T₀)).base
  set g' := (F.map (gam' F φ φ' h T₀)).base
  have hkk' : k ≫ k' = 𝟙 _ := preIso_hom_inv_base F T₀
  have hk'k : k' ≫ k = 𝟙 _ := preIso_inv_hom_base F T₀
  have hgg : g ≫ inv g' = 𝟙 _ := by
    have e : g ≫ inv g' = k ≫ (k' ≫ g ≫ inv g' ≫ k) ≫ k' := by
      simp only [Category.assoc, hkk', Category.comp_id, reassoc_of% hkk']
    rw [e]
    have hη' : etaHom F hbi φ φ' h T₀ = 𝟙 T₀.left := hη
    change k ≫ etaHom F hbi φ φ' h T₀ ≫ k' = _
    rw [hη', Category.id_comp, hkk']
  have hg : g = g' := by
    rw [← Category.comp_id g, ← IsIso.inv_hom_id g', ← Category.assoc, hgg, Category.id_comp]
  have e₁ := congrArg (fun ψ => (F.map ψ).base) (facAt_pbAt (preπ F X T₀ ≫ φ) _ rfl)
  have e₂ := congrArg (fun ψ => (F.map ψ).base)
    (facAt_pbAt (preπ F X T₀ ≫ φ') ((preπ F X T₀).base ≫ φ.base) (by simp [h]))
  simp only [F.map_comp, comp_base] at e₁ e₂
  change g ≫ _ = _ at e₁
  change g' ≫ _ = _ at e₂
  rw [← hg, e₁] at e₂
  have hπ : (F.map (preπ F X T₀)).base = k := by
    rw [map_preπ, comp_base]
    change k ≫ 𝟙 _ = k
    exact Category.comp_id _
  rw [hπ] at e₂
  haveI : IsIso k := inferInstance
  exact (cancel_epi k).mp e₂

include hpb hbi in
/-- **Base-identity endomorphisms are mapped to base-identity endomorphisms** ([FrdI], Theorem
3.4(v)). -/
theorem base_map_eq_id (hD : IsSlim D₂) (e : X ⟶ X) (he : e.base = 𝟙 _) :
    (F.map e).base = 𝟙 _ := by
  rw [base_map_eq_of_base_eq F hpb hbi e (𝟙 X) (by rw [he]; rfl) hD, F.map_id]
  rfl

end Main

/-! ### The functor of base categories -/

section Base

variable {D₁ : Type u₁} [Category.{v₁} D₁] [IsConnected D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [IsConnected D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

/-- The divisor `q_X ∈ Φ(A_X)` of a chosen decomposition `α_X = p_X − q_X`. -/
noncomputable def negPart (X : Model Φ₁ B₁ divB₁) : Φ₁.obj X.base :=
  (Φ₁.generating X.α).choose_spec.2.choose

omit [IsConnected D₁] [TotallyEpimorphic D₁] in
lemma negPart_mem (X : Model Φ₁ B₁ divB₁) : negPart X ∈ Φ₁.pos X.base :=
  (Φ₁.generating X.α).choose_spec.2.choose_spec.1

/-- The positive part `p_X`. -/
noncomputable def posPart (X : Model Φ₁ B₁ divB₁) : Φ₁.obj X.base :=
  (Φ₁.generating X.α).choose

omit [IsConnected D₁] [TotallyEpimorphic D₁] in
lemma posPart_mem (X : Model Φ₁ B₁ divB₁) : posPart X ∈ Φ₁.pos X.base :=
  (Φ₁.generating X.α).choose_spec.1

omit [IsConnected D₁] [TotallyEpimorphic D₁] in
lemma posPart_sub_negPart (X : Model Φ₁ B₁ divB₁) : X.α = posPart X - negPart X :=
  (Φ₁.generating X.α).choose_spec.2.choose_spec.2

/-- The object `E_X = (A_X, −q_X)`. -/
noncomputable abbrev spanObj (X : Model Φ₁ B₁ divB₁) : Model Φ₁ B₁ divB₁ :=
  ⟨X.base, -negPart X⟩

/-- The pre-step `E_X → X` with zero divisor `p_X`. -/
noncomputable def spanL (X : Model Φ₁ B₁ divB₁) : spanObj X ⟶ X :=
  mk1 (𝟙 _) (posPart X) (posPart_mem X) 0 (by
    simp only [GrpOn.pb_id', map_zero, add_zero]
    rw [posPart_sub_negPart X]
    abel)

/-- The pre-step `E_X → (A_X, 0)` with zero divisor `q_X`. -/
noncomputable def spanR (X : Model Φ₁ B₁ divB₁) : spanObj X ⟶ zeroObj Φ₁ B₁ divB₁ X.base :=
  mk1 (𝟙 _) (negPart X) (negPart_mem X) 0 (by simp)

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence]

/-- **The functor of base categories** `F_Base : D₁ → D₂`, `A ↦ Base(F(A, 0))`. -/
noncomputable def baseFunctor : D₁ ⥤ D₂ :=
  zeroSection Φ₁ B₁ divB₁ ⋙ F ⋙ forget Φ₂ B₂ divB₂

variable (hD₁ : BaseHyp D₁) (hB₁ : HasAllTorsion B₁) (hD₂ : BaseHyp D₂)
  (hB₂ : HasAllTorsion B₂)

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
lemma isIso_base_map_of_baseIso {X Y : Model Φ₁ B₁ divB₁} (ψ : X ⟶ Y) (hψ : IsIso ψ.base) :
    IsIso (F.map ψ).base :=
  ((typeCorresp hD₁ hB₁ hD₂ hB₂ F).baseIso ψ).1 hψ

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
lemma isIso_spanL (X : Model Φ₁ B₁ divB₁) : IsIso (F.map (spanL X)).base :=
  isIso_base_map_of_baseIso F hD₁ hB₁ hD₂ hB₂ (spanL X)
    (by change IsIso (𝟙 X.base); infer_instance)

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
lemma isIso_spanR (X : Model Φ₁ B₁ divB₁) : IsIso (F.map (spanR X)).base :=
  isIso_base_map_of_baseIso F hD₁ hB₁ hD₂ hB₂ (spanR X)
    (by change IsIso (𝟙 X.base); infer_instance)

/-- The component `Base(F X) ≅ F_Base(A_X)`. -/
noncomputable def baseComp (X : Model Φ₁ B₁ divB₁) :
    (F.obj X).base ≅ (baseFunctor F).obj X.base :=
  (@asIso _ _ _ _ (F.map (spanL X)).base (isIso_spanL F hD₁ hB₁ hD₂ hB₂ X)).symm ≪≫
    @asIso _ _ _ _ (F.map (spanR X)).base (isIso_spanR F hD₁ hB₁ hD₂ hB₂ X)

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
lemma baseComp_natural (hD : IsSlim D₂) {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) :
    (F.map φ).base ≫ (baseComp F hD₁ hB₁ hD₂ hB₂ Y).hom =
      (baseComp F hD₁ hB₁ hD₂ hB₂ X).hom ≫ (baseFunctor F).map φ.base := by
  have c := typeCorresp hD₁ hB₁ hD₂ hB₂ F
  -- the auxiliary object `W = (A_X, −q_X − f^* q_Y)` with `μ : W → E_X`, `ν : W → E_Y`
  let W : Model Φ₁ B₁ divB₁ := ⟨X.base, -negPart X - Φ₁.pb φ.base (negPart Y)⟩
  let μ : W ⟶ spanObj X := mk1 (𝟙 _) (Φ₁.pb φ.base (negPart Y)) (Φ₁.pb_mem _ (negPart_mem Y)) 0
    (by simp [W])
  let ν : W ⟶ spanObj Y := mk1 φ.base (negPart X) (negPart_mem X) 0 (by simp [W]; abel)
  have K₁ := base_map_eq_of_base_eq F c.pullback c.baseIso (μ ≫ spanL X ≫ φ) (ν ≫ spanL Y)
    (by simp [μ, ν, spanL]) hD
  have K₂ := base_map_eq_of_base_eq F c.pullback c.baseIso
    (μ ≫ spanR X ≫ (zeroSection Φ₁ B₁ divB₁).map φ.base) (ν ≫ spanR Y)
    (by simp [μ, ν, spanR, zeroSection]) hD
  simp only [F.map_comp, comp_base] at K₁ K₂
  haveI := isIso_spanL F hD₁ hB₁ hD₂ hB₂ X
  haveI := isIso_spanL F hD₁ hB₁ hD₂ hB₂ Y
  haveI := isIso_base_map_of_baseIso F hD₁ hB₁ hD₂ hB₂ μ
    (by change IsIso (𝟙 X.base); infer_instance)
  rw [← cancel_epi ((F.map μ).base ≫ (F.map (spanL X)).base)]
  simp only [baseComp, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv, Category.assoc,
    IsIso.hom_inv_id_assoc]
  rw [reassoc_of% K₁, IsIso.hom_inv_id_assoc]
  exact K₂.symm

omit [IsConnected D₁] [IsConnected D₂] in
include hD₁ hB₁ hD₂ hB₂ in
/-- **[FrdI], Theorem 3.4(v)** for model Frobenioids with a slim base category `D₂`: every
equivalence lies over a functor of base categories. -/
theorem thm34_preservesBase (hD : IsSlim D₂) : PreservesBase 𝐏₁ 𝐏₂ F :=
  ⟨baseFunctor F, ⟨NatIso.ofComponents (fun X => baseComp F hD₁ hB₁ hD₂ hB₂ X)
    (fun φ => baseComp_natural F hD₁ hB₁ hD₂ hB₂ hD φ)⟩⟩

end Base

end Model

end Frobenioid

end Iut
