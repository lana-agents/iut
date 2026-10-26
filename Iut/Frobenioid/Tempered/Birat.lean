/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.Thm34Temp

/-!
# The birationalization of a model Frobenioid ([FrdI], Proposition 4.4, Corollary 4.10)

[FrdI], Proposition 4.4, defines the **birationalization** `C^birat` of a Frobenioid `C`: its
objects are those of `C`, and

  `Hom^birat(A, B) = lim_{(A' → A) ∈ C^{coa-pre}_A} Hom_C(A', B)`

(inductive limit over the co-angular pre-steps into `A`). [EtTh] §4–§5 and IUT I, Example 3.2(ii)
(`F^÷_v = F^birat_v`, the theta function `Θ_v ∈ O^×(T^÷_Ÿ)`) work in `C^birat` of the tempered
Frobenioid.

For a model Frobenioid `C = Model Φ B divB` (every morphism is co-angular) the inductive limit has
an explicit description, used here as the definition: a **birational morphism** `X → Y` is a
triple `(deg, base, u)` with `u ∈ B(X_D)` (`BHom`), composed like the morphisms of the model; the
"zero divisor" `birDiv b = base^* α_Y + Div_B(u) − deg·α_X ∈ Φ^gp(X_D)` is no longer required to be
effective. We prove that this is the inductive limit of Proposition 4.4:

* `Model.toBirat : C ⥤ C^birat` is faithful (Proposition 4.4(ii));
* `Model.exists_rep`: every birational morphism `b : X → Y` is `α^{-1} ∘ φ` for a pre-step
  `α : X' → X` and a morphism `φ : X' → Y` of `C`;
* `Model.rep_unique`: two such representations agree after composing with pre-steps (the
  equality in the inductive limit);
* `Model.isIso_toBirat_map_iff`: `φ` becomes an isomorphism in `C^birat` iff it is a pre-step
  (Proposition 4.4(iv), every morphism of a model being co-angular);
* `Model.birUnitEquiv`: `O^×(X^birat) ≅ B(X_D)` (the rational function monoid, Proposition
  4.4(ii)), and `Model.birDiv_unit`: the divisor map `O^×(X^birat) → Φ^gp` is `Div_B`, with
  kernel `O^×(X)` (Proposition 4.4(iii)).

**Category-theoreticity** ([FrdI], Corollary 4.10): `Model.biratFunctor F` is the functor
`C₁^birat → C₂^birat` induced by any functor `F` mapping pre-steps to pre-steps (e.g. an
equivalence, by [FrdI], Theorem 3.4(ii)); it satisfies `toBirat ⋙ F^birat = F ⋙ toBirat`
(`Model.biratFunctor_map_toBirat`). If moreover `F` maps base-equivalent pairs of pre-steps to
base-equivalent pairs ([FrdI], Theorem 3.4(v)), `F^birat` maps `O^×(X^birat)` into
`O^×(F(X)^birat)` (`Model.biratFunctor_map_unit`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-! ### The category `C^birat` -/

variable (Φ B divB) in
/-- **The objects of the birationalization** `C^birat`: those of `C`. -/
structure Birat where
  /-- The underlying object of `C`. -/
  obj : Model Φ B divB

/-- **Birational morphisms** `X → Y`: Frobenius degree, base and rational function. -/
@[ext]
structure BHom (X Y : Birat Φ B divB) where
  /-- The Frobenius degree. -/
  deg : ℕ+
  /-- The projection to `D`. -/
  base : X.obj.base ⟶ Y.obj.base
  /-- The rational function. -/
  u : B.obj X.obj.base

instance : Category (Birat Φ B divB) where
  Hom := BHom
  id X := ⟨1, 𝟙 _, 0⟩
  comp φ ψ := ⟨ψ.deg * φ.deg, φ.base ≫ ψ.base, B.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u⟩
  id_comp φ := by
    refine BHom.ext (mul_one _) (Category.id_comp _) ?_
    simp
  comp_id φ := by
    refine BHom.ext (one_mul _) (Category.comp_id _) ?_
    simp
  assoc φ ψ χ := by
    refine BHom.ext (mul_assoc _ _ _).symm (Category.assoc _ _ _) ?_
    simp only [GrpOn.pb_comp', map_add, map_nsmul, smul_add, PNat.mul_coe, mul_smul]
    abel

namespace Birat

@[ext] lemma hom_ext {X Y : Birat Φ B divB} {φ ψ : X ⟶ Y} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.base = ψ.base) (h₃ : φ.u = ψ.u) : φ = ψ := BHom.ext h₁ h₂ h₃

@[simp] lemma id_deg (X : Birat Φ B divB) : (𝟙 X : X ⟶ X).deg = 1 := rfl
@[simp] lemma id_base (X : Birat Φ B divB) : (𝟙 X : X ⟶ X).base = 𝟙 _ := rfl
@[simp] lemma id_u (X : Birat Φ B divB) : (𝟙 X : X ⟶ X).u = 0 := rfl

section comp

variable {X Y Z : Birat Φ B divB} (φ : X ⟶ Y) (ψ : Y ⟶ Z)

@[simp] lemma comp_deg : (φ ≫ ψ).deg = ψ.deg * φ.deg := rfl
@[simp] lemma comp_base : (φ ≫ ψ).base = φ.base ≫ ψ.base := rfl
@[simp] lemma comp_u : (φ ≫ ψ).u = B.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u := rfl

end comp

/-- **The zero divisor of a birational morphism** `base^* α_Y + Div_B(u) − deg·α_X ∈ Φ^gp(X_D)`
(the functor `C^birat → F_{Φ^gp}` of [FrdI], Proposition 4.4(i)). -/
def birDiv {X Y : Birat Φ B divB} (b : X ⟶ Y) : Φ.obj X.obj.base :=
  Φ.pb b.base Y.obj.α + divB.app _ b.u - (b.deg : ℕ) • X.obj.α

lemma birDiv_comp {X Y Z : Birat Φ B divB} (b : X ⟶ Y) (c : Y ⟶ Z) :
    birDiv (b ≫ c) = Φ.pb b.base (birDiv c) + (c.deg : ℕ) • birDiv b := by
  simp only [birDiv, comp_base, comp_u, comp_deg, GrpOn.pb_comp', map_add, map_sub, map_nsmul,
    divB.natural, PNat.mul_coe, smul_sub, smul_add, mul_smul]
  abel

/-- The inverse of a birational morphism of degree `1` with invertible base. -/
noncomputable def invOf {X Y : Birat Φ B divB} (b : X ⟶ Y) [IsIso b.base] : Y ⟶ X :=
  ⟨1, inv b.base, -B.pb (inv b.base) b.u⟩

lemma isIso_of {X Y : Birat Φ B divB} (b : X ⟶ Y) (h₁ : b.deg = 1) [IsIso b.base] : IsIso b :=
  ⟨invOf b, by ext <;> simp [invOf, h₁], by ext <;> simp [invOf, h₁]⟩

/-- **Isomorphisms of `C^birat`**: degree `1` and invertible base. -/
theorem isIso_iff {X Y : Birat Φ B divB} (b : X ⟶ Y) : IsIso b ↔ b.deg = 1 ∧ IsIso b.base := by
  constructor
  · intro h
    have hd := congrArg BHom.deg (IsIso.hom_inv_id b)
    have hb := congrArg BHom.base (IsIso.hom_inv_id b)
    have hb' := congrArg BHom.base (IsIso.inv_hom_id b)
    simp only [comp_deg, id_deg, comp_base, id_base] at hd hb hb'
    exact ⟨PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val hd)),
      ⟨(inv b).base, hb, hb'⟩⟩
  · rintro ⟨h₁, h₂⟩
    haveI := h₂
    exact isIso_of b h₁

end Birat

open Birat

variable (Φ B divB) in
/-- **The natural functor `C → C^birat`** ([FrdI], Proposition 4.4(i)). -/
def toBirat : Model Φ B divB ⥤ Birat Φ B divB where
  obj X := ⟨X⟩
  map φ := ⟨φ.deg, φ.base, φ.u⟩
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] lemma toBirat_obj_obj (X : Model Φ B divB) : ((toBirat Φ B divB).obj X).obj = X := rfl
@[simp] lemma toBirat_map_deg {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((toBirat Φ B divB).map φ).deg = φ.deg := rfl
@[simp] lemma toBirat_map_base {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((toBirat Φ B divB).map φ).base = φ.base := rfl
@[simp] lemma toBirat_map_u {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    ((toBirat Φ B divB).map φ).u = φ.u := rfl

/-- The zero divisor of the image of a morphism of `C` is its zero divisor. -/
lemma birDiv_toBirat {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    birDiv ((toBirat Φ B divB).map φ) = φ.div := by
  change Φ.pb φ.base Y.α + divB.app X.base φ.u - (φ.deg : ℕ) • X.α = φ.div
  rw [← φ.rel]
  abel

/-- **`C → C^birat` is faithful** ([FrdI], Proposition 4.4(ii)): the zero divisor is determined
by the other data. -/
theorem toBirat_map_injective {X Y : Model Φ B divB} {φ ψ : X ⟶ Y}
    (h : (toBirat Φ B divB).map φ = (toBirat Φ B divB).map ψ) : φ = ψ := by
  have hd := congrArg BHom.deg h
  have hb := congrArg BHom.base h
  have hu := congrArg BHom.u h
  have hdiv : φ.div = ψ.div := by
    rw [← birDiv_toBirat φ, ← birDiv_toBirat ψ, h]
  exact hom_ext hd hb hdiv hu

instance : (toBirat Φ B divB).Faithful := ⟨fun h => toBirat_map_injective h⟩

/-- **Prop. 4.4(iv)**: a morphism of `C` becomes an isomorphism of `C^birat` iff it is a pre-step
(all morphisms of a model Frobenioid are co-angular). -/
theorem isIso_toBirat_map_iff {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsIso ((toBirat Φ B divB).map φ) ↔ IsPreStep 𝐏 φ := by
  rw [Birat.isIso_iff]
  rfl

/-! ### `C^birat` as an inductive limit -/

/-- **Every birational morphism is `α^{-1} ∘ φ`** with `α` a pre-step of `C` into `X` and `φ` a
morphism of `C`. -/
theorem exists_rep {X Y : Model Φ B divB} (b : (⟨X⟩ : Birat Φ B divB) ⟶ ⟨Y⟩) :
    ∃ (X' : Model Φ B divB) (α : X' ⟶ X) (φ : X' ⟶ Y), IsPreStep 𝐏 α ∧
      (toBirat Φ B divB).map α ≫ b = (toBirat Φ B divB).map φ := by
  obtain ⟨p, hp, q, hq, he⟩ := Φ.generating (show Φ.obj X.base from birDiv b)
  let X' : Model Φ B divB := ⟨X.base, X.α - q⟩
  let α : X' ⟶ X := mk1 (𝟙 _) q hq 0 (by simp [X'])
  have hW : p + ((b.deg : ℕ) - 1) • q ∈ Φ.pos X.base :=
    (Φ.pos _).add_mem hp ((Φ.pos _).nsmul_mem hq _)
  have he' : birDiv b = p - q := he
  have e : ((b.deg : ℕ) - 1) • q = (b.deg : ℕ) • q - q := by
    rw [eq_sub_iff_add_eq, ← succ_nsmul, Nat.sub_add_cancel b.deg.pos]
  let φ : X' ⟶ Y := mk' b.deg b.base (p + ((b.deg : ℕ) - 1) • q) hW b.u (by
    have hb : Φ.pb b.base Y.α + divB.app X.base b.u = (p - q) + (b.deg : ℕ) • X.α := by
      rw [← he']
      change _ = (Φ.pb b.base Y.α + divB.app X.base b.u - (b.deg : ℕ) • X.α) + _
      abel
    change (b.deg : ℕ) • (X.α - q) + _ = _
    rw [hb, e, smul_sub]
    abel)
  refine ⟨X', α, φ, isPreStep_mk1 _ _ _ _ _, ?_⟩
  ext
  · simp [α, φ]
  · simp [α, φ]
  · change B.pb (𝟙 X.base) b.u + (b.deg : ℕ) • (0 : B.obj X.base) = b.u
    simp

/-- **Uniqueness of representatives** (the equality relation of the inductive limit): two
representations `α₁^{-1} φ₁ = α₂^{-1} φ₂` become equal after composing with pre-steps
`β₁, β₂` with `β₁ ≫ α₁ = β₂ ≫ α₂`. -/
theorem rep_unique {X Y X₁ X₂ : Model Φ B divB} {α₁ : X₁ ⟶ X} {φ₁ : X₁ ⟶ Y} {α₂ : X₂ ⟶ X}
    {φ₂ : X₂ ⟶ Y} (h₁ : IsPreStep 𝐏 α₁) (h₂ : IsPreStep 𝐏 α₂)
    {b : (toBirat Φ B divB).obj X ⟶ (toBirat Φ B divB).obj Y}
    (e₁ : (toBirat Φ B divB).map α₁ ≫ b = (toBirat Φ B divB).map φ₁)
    (e₂ : (toBirat Φ B divB).map α₂ ≫ b = (toBirat Φ B divB).map φ₂) :
    ∃ (W : Model Φ B divB) (β₁ : W ⟶ X₁) (β₂ : W ⟶ X₂), IsPreStep 𝐏 β₁ ∧ IsPreStep 𝐏 β₂ ∧
      β₁ ≫ α₁ = β₂ ≫ α₂ ∧ β₁ ≫ φ₁ = β₂ ≫ φ₂ := by
  haveI : IsIso α₁.base := h₁.2
  haveI : IsIso α₂.base := h₂.2
  have d₁ : α₁.deg = 1 := h₁.1
  have d₂ : α₂.deg = 1 := h₂.1
  -- `k = α₁.base ≫ α₂.base⁻¹ : X₁ → X₂` on bases
  set k := α₁.base ≫ inv α₂.base with hk
  have hkα : k ≫ α₂.base = α₁.base := by simp [hk]
  -- `W = (X₁, α_{X₁} − k^* Div α₂)` with `β₁ = (1, id, k^* Div α₂, 0)`
  have hZ : Φ.pb k α₂.div ∈ Φ.pos X₁.base := Φ.pb_mem _ α₂.div_mem
  let W : Model Φ B divB := ⟨X₁.base, X₁.α - Φ.pb k α₂.div⟩
  let β₁ : W ⟶ X₁ := mk1 (𝟙 _) (Φ.pb k α₂.div) hZ 0 (by simp [W])
  let β₂ : W ⟶ X₂ := mk1 k α₁.div α₁.div_mem (α₁.u - B.pb k α₂.u) (by
    have r₁ := α₁.rel
    have r₂ := congrArg (Φ.pb k) α₂.rel
    rw [d₁, PNat.one_coe, one_smul] at r₁
    rw [d₂, PNat.one_coe, one_smul] at r₂
    simp only [map_add, ← GrpOn.pb_comp', hkα, ← divB.natural] at r₂
    simp only [W, map_sub]
    linear_combination (norm := module) r₁ - r₂)
  have hβα : β₁ ≫ α₁ = β₂ ≫ α₂ := by
    ext
    · simp [β₁, β₂, d₁, d₂]
    · simp [β₁, β₂, hkα]
    · simp [β₁, β₂, d₁, d₂, add_comm]
    · simp [β₁, β₂, d₁, d₂]
  refine ⟨W, β₁, β₂, isPreStep_mk1 _ _ _ _ _, ⟨rfl, by change IsIso k; infer_instance⟩,
    hβα, toBirat_map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_comp, ← e₁, ← e₂, ← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hβα]

/-- **Pushing a pre-step across a morphism** (the Ore condition of the inductive limit): for
`φ : X' → Y` and a pre-step `β : Y' → Y` there are a pre-step `α : X'' → X'` and `φ' : X'' → Y'`
with `α ≫ φ = φ' ≫ β`. -/
theorem exists_ore {X' Y Y' : Model Φ B divB} (φ : X' ⟶ Y) {β : Y' ⟶ Y} (hβ : IsPreStep 𝐏 β) :
    ∃ (X'' : Model Φ B divB) (α : X'' ⟶ X') (φ' : X'' ⟶ Y'), IsPreStep 𝐏 α ∧
      α ≫ φ = φ' ≫ β := by
  haveI : IsIso β.base := hβ.2
  have d : β.deg = 1 := hβ.1
  set k := φ.base ≫ inv β.base with hk
  have hkβ : k ≫ β.base = φ.base := by simp [hk]
  set Z := Φ.pb k β.div with hZdef
  have hZ : Z ∈ Φ.pos X'.base := Φ.pb_mem _ β.div_mem
  let X'' : Model Φ B divB := ⟨X'.base, X'.α - Z⟩
  let α : X'' ⟶ X' := mk1 (𝟙 _) Z hZ 0 (by simp [X''])
  have hW : φ.div + ((φ.deg : ℕ) - 1) • Z ∈ Φ.pos X'.base :=
    (Φ.pos _).add_mem φ.div_mem ((Φ.pos _).nsmul_mem hZ _)
  have e : ((φ.deg : ℕ) - 1) • Z = (φ.deg : ℕ) • Z - Z := by
    rw [eq_sub_iff_add_eq, ← succ_nsmul, Nat.sub_add_cancel φ.deg.pos]
  let φ' : X'' ⟶ Y' := mk' φ.deg k (φ.div + ((φ.deg : ℕ) - 1) • Z) hW (φ.u - B.pb k β.u) (by
    have r₁ := φ.rel
    have r₂ := congrArg (Φ.pb k) β.rel
    rw [d, PNat.one_coe, one_smul] at r₂
    simp only [map_add, ← GrpOn.pb_comp', hkβ, ← divB.natural] at r₂
    rw [← hZdef] at r₂
    simp only [X'', map_sub, smul_sub]
    rw [e]
    linear_combination (norm := module) r₁ - r₂)
  refine ⟨X'', α, φ', isPreStep_mk1 _ _ _ _ _, ?_⟩
  ext
  · simp [α, φ', d]
  · simp [α, φ', hkβ]
  · simp only [comp_div, α, φ', mk1_base, mk1_div, mk'_base, mk'_div,
      GrpOn.pb_id', d, PNat.one_coe, one_smul]
    rw [e]
    abel
  · simp [α, φ', d]

/-! ### Units of `C^birat` -/

/-- **`O^×(X^birat) ≅ B(X_D)`** ([FrdI], Proposition 4.4(ii): the rational function monoid). -/
def birUnitEquiv (X : Birat Φ B divB) :
    B.obj X.obj.base ≃ {e : X ⟶ X // e.deg = 1 ∧ e.base = 𝟙 _} where
  toFun u := ⟨⟨1, 𝟙 _, u⟩, rfl, rfl⟩
  invFun e := e.1.u
  left_inv _ := rfl
  right_inv e := by
    obtain ⟨⟨d, b, u⟩, hd, hb⟩ := e
    simp only at hd hb
    subst hd hb
    rfl

lemma birUnitEquiv_mul (X : Birat Φ B divB) (u v : B.obj X.obj.base) :
    ((birUnitEquiv X u).1 ≫ (birUnitEquiv X v).1) = (birUnitEquiv X (u + v)).1 := by
  ext <;> simp [birUnitEquiv, add_comm]

/-- **[FrdI], Proposition 4.4(iii)**: on `O^×(X^birat) ≅ B(X_D)` the divisor map is `Div_B`; its
kernel is `O^×(X)` (`Div_B(u) = 0`). -/
lemma birDiv_unit (X : Birat Φ B divB) (u : B.obj X.obj.base) :
    birDiv (birUnitEquiv X u).1 = divB.app _ u := by
  simp [birDiv, birUnitEquiv]

/-! ### Category-theoreticity of the birationalization ([FrdI], Corollary 4.10) -/

section Functor

variable {D₁ : Type u₁} [Category.{v₁} D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂
local notation "𝐓₁" => toBirat Φ₁ B₁ divB₁
local notation "𝐓₂" => toBirat Φ₂ B₂ divB₂

variable (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
  (hF : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ : X ⟶ Y), IsPreStep (toElem Φ₁ B₁ divB₁) φ →
    IsPreStep (toElem Φ₂ B₂ divB₂) (F.map φ))

/-- The image of a representation `α^{-1} φ`: `F(α)^{-1} F(φ)` in `C₂^birat`. -/
noncomputable def repImage {X Y X' : Model Φ₁ B₁ divB₁} (α : X' ⟶ X) (φ : X' ⟶ Y)
    (hα : IsPreStep 𝐏₁ α) : 𝐓₂.obj (F.obj X) ⟶ 𝐓₂.obj (F.obj Y) :=
  haveI := (isIso_toBirat_map_iff (F.map α)).2 (hF α hα)
  inv (𝐓₂.map (F.map α)) ≫ 𝐓₂.map (F.map φ)

include hF in
@[reassoc]
lemma repImage_spec {X Y X' : Model Φ₁ B₁ divB₁} (α : X' ⟶ X) (φ : X' ⟶ Y)
    (hα : IsPreStep 𝐏₁ α) : 𝐓₂.map (F.map α) ≫ repImage F hF α φ hα = 𝐓₂.map (F.map φ) := by
  haveI := (isIso_toBirat_map_iff (F.map α)).2 (hF α hα)
  simp [repImage]

include hF in
/-- `repImage` is characterized by `F(α) ≫ c = F(φ)`. -/
lemma repImage_eq {X Y X' : Model Φ₁ B₁ divB₁} (α : X' ⟶ X) (φ : X' ⟶ Y)
    (hα : IsPreStep 𝐏₁ α) (c : 𝐓₂.obj (F.obj X) ⟶ 𝐓₂.obj (F.obj Y))
    (hc : 𝐓₂.map (F.map α) ≫ c = 𝐓₂.map (F.map φ)) : repImage F hF α φ hα = c := by
  haveI := (isIso_toBirat_map_iff (F.map α)).2 (hF α hα)
  rw [← cancel_epi (𝐓₂.map (F.map α)), repImage_spec, hc]

include hF in
lemma isPreStep_comp {X Y Z : Model Φ₁ B₁ divB₁} {a : X ⟶ Y} {b : Y ⟶ Z}
    (ha : IsPreStep 𝐏₁ a) (hb : IsPreStep 𝐏₁ b) : IsPreStep 𝐏₂ (F.map a ≫ F.map b) := by
  refine ⟨?_, ?_⟩
  · change degFr _ (F.map a ≫ F.map b) = 1
    rw [degFr_comp, (hF a ha).1, (hF b hb).1]
    rfl
  · haveI : IsIso (F.map a).base := (hF a ha).2
    haveI : IsIso (F.map b).base := (hF b hb).2
    change IsIso (F.map a ≫ F.map b).base
    rw [comp_base]; infer_instance

include hF in
/-- Independence of the representation. -/
lemma repImage_congr {X Y X₁ X₂ : Model Φ₁ B₁ divB₁} {α₁ : X₁ ⟶ X} {φ₁ : X₁ ⟶ Y}
    {α₂ : X₂ ⟶ X} {φ₂ : X₂ ⟶ Y} (h₁ : IsPreStep 𝐏₁ α₁) (h₂ : IsPreStep 𝐏₁ α₂)
    {b : 𝐓₁.obj X ⟶ 𝐓₁.obj Y} (e₁ : 𝐓₁.map α₁ ≫ b = 𝐓₁.map φ₁) (e₂ : 𝐓₁.map α₂ ≫ b = 𝐓₁.map φ₂) :
    repImage F hF α₁ φ₁ h₁ = repImage F hF α₂ φ₂ h₂ := by
  obtain ⟨W, β₁, β₂, hβ₁, hβ₂, hα, hφ⟩ := rep_unique h₁ h₂ e₁ e₂
  have k₁ : 𝐓₂.map (F.map β₁ ≫ F.map α₁) ≫ repImage F hF α₁ φ₁ h₁ =
      𝐓₂.map (F.map (β₁ ≫ φ₁)) := by
    simp only [F.map_comp, Functor.map_comp, Category.assoc, repImage_spec]
  have k₂ : 𝐓₂.map (F.map β₂ ≫ F.map α₂) ≫ repImage F hF α₂ φ₂ h₂ =
      𝐓₂.map (F.map (β₂ ≫ φ₂)) := by
    simp only [F.map_comp, Functor.map_comp, Category.assoc, repImage_spec]
  rw [← F.map_comp, hα, hφ, F.map_comp] at k₁
  haveI := (isIso_toBirat_map_iff (F.map β₂ ≫ F.map α₂)).2 (isPreStep_comp F hF hβ₂ h₂)
  exact (cancel_epi _).mp (k₁.trans k₂.symm)

/-- The map on morphisms of `F^birat`, through a chosen representation. -/
noncomputable def biratMap {X Y : Birat Φ₁ B₁ divB₁} (b : X ⟶ Y) :
    𝐓₂.obj (F.obj X.obj) ⟶ 𝐓₂.obj (F.obj Y.obj) :=
  repImage F hF (exists_rep b).choose_spec.choose (exists_rep b).choose_spec.choose_spec.choose
    (exists_rep b).choose_spec.choose_spec.choose_spec.1

include hF in
lemma biratMap_eq {X Y : Birat Φ₁ B₁ divB₁} (b : X ⟶ Y) {X' : Model Φ₁ B₁ divB₁}
    (α : X' ⟶ X.obj) (φ : X' ⟶ Y.obj) (hα : IsPreStep 𝐏₁ α) (e : 𝐓₁.map α ≫ b = 𝐓₁.map φ) :
    biratMap F hF b = repImage F hF α φ hα :=
  repImage_congr F hF _ hα (exists_rep b).choose_spec.choose_spec.choose_spec.2 e

lemma isPreStep_id (X : Model Φ₁ B₁ divB₁) : IsPreStep 𝐏₁ (𝟙 X) :=
  ⟨rfl, by change IsIso (𝟙 X.base); infer_instance⟩

/-- **The functor `F^birat : C₁^birat → C₂^birat`** induced by a functor preserving pre-steps
([FrdI], Corollary 4.10): `b = α^{-1} φ ↦ F(α)^{-1} F(φ)`. -/
noncomputable def biratFunctor : Birat Φ₁ B₁ divB₁ ⥤ Birat Φ₂ B₂ divB₂ where
  obj X := 𝐓₂.obj (F.obj X.obj)
  map b := biratMap F hF b
  map_id X := by
    rw [biratMap_eq F hF (𝟙 X) (𝟙 X.obj) (𝟙 X.obj) (isPreStep_id X.obj)
      (by rw [CategoryTheory.Functor.map_id]; exact Category.id_comp _)]
    exact repImage_eq F hF _ _ _ _ (by simp)
  map_comp {X Y Z} b c := by
    obtain ⟨X', α, φ, hα, e₁⟩ := exists_rep b
    obtain ⟨Y', β, ψ, hβ, e₂⟩ := exists_rep c
    obtain ⟨X'', α', φ', hα', e₃⟩ := exists_ore φ hβ
    have hcomp : IsPreStep 𝐏₁ (α' ≫ α) := ⟨by
      change degFr _ (α' ≫ α) = 1
      rw [degFr_comp, hα.1, hα'.1]
      rfl, by
      haveI : IsIso α'.base := hα'.2
      haveI : IsIso α.base := hα.2
      change IsIso (α' ≫ α).base
      rw [comp_base]; infer_instance⟩
    have eb : 𝐓₁.map (α' ≫ α) ≫ (b ≫ c) = 𝐓₁.map (φ' ≫ ψ) := by
      calc 𝐓₁.map (α' ≫ α) ≫ (b ≫ c) = 𝐓₁.map α' ≫ (𝐓₁.map α ≫ b) ≫ c := by
            rw [Functor.map_comp]; simp only [Category.assoc]
        _ = 𝐓₁.map α' ≫ 𝐓₁.map φ ≫ c := congrArg (fun t => 𝐓₁.map α' ≫ t ≫ c) e₁
        _ = 𝐓₁.map (α' ≫ φ) ≫ c := by rw [Functor.map_comp, Category.assoc]
        _ = 𝐓₁.map (φ' ≫ β) ≫ c := by rw [e₃]
        _ = 𝐓₁.map φ' ≫ (𝐓₁.map β ≫ c) := by rw [Functor.map_comp, Category.assoc]
        _ = 𝐓₁.map (φ' ≫ ψ) := by
          rw [CategoryTheory.Functor.map_comp]
          exact congrArg (fun t => 𝐓₁.map φ' ≫ t) e₂
    rw [biratMap_eq F hF (b ≫ c) _ _ hcomp eb, biratMap_eq F hF b α φ hα e₁,
      biratMap_eq F hF c β ψ hβ e₂]
    refine repImage_eq F hF _ _ _ _ ?_
    have e₃' : 𝐓₂.map (F.map α') ≫ 𝐓₂.map (F.map φ) =
        𝐓₂.map (F.map φ') ≫ 𝐓₂.map (F.map β) := by
      rw [← Functor.map_comp, ← F.map_comp, e₃, F.map_comp, Functor.map_comp]
    simp only [F.map_comp, Functor.map_comp, Category.assoc, repImage_spec_assoc]
    rw [reassoc_of% e₃', repImage_spec]

include hF in
/-- **`toBirat ⋙ F^birat = F ⋙ toBirat`** on morphisms. -/
theorem biratFunctor_map_toBirat {X Y : Model Φ₁ B₁ divB₁} (φ : X ⟶ Y) :
    (biratFunctor F hF).map (𝐓₁.map φ) = 𝐓₂.map (F.map φ) := by
  change biratMap F hF (𝐓₁.map φ) = _
  rw [biratMap_eq F hF (𝐓₁.map φ) (𝟙 X) φ (isPreStep_id X) (by simp)]
  exact repImage_eq F hF _ _ _ _ (by simp)

include hF in
/-- **`F^birat` preserves units** (`O^×(X^birat) → O^×(F(X)^birat)`) when `F` maps pairs of
pre-steps with the same base to pairs with the same base ([FrdI], Theorem 3.4(v)). -/
theorem biratFunctor_map_unit
    (hbe : ∀ ⦃X Y : Model Φ₁ B₁ divB₁⦄ (φ φ' : X ⟶ Y), φ.base = φ'.base →
      (F.map φ).base = (F.map φ').base)
    {X : Birat Φ₁ B₁ divB₁} (e : X ⟶ X) (hd : e.deg = 1) (hb : e.base = 𝟙 _) :
    ((biratFunctor F hF).map e).deg = 1 ∧ ((biratFunctor F hF).map e).base = 𝟙 _ := by
  obtain ⟨X', α, φ, hα, he⟩ := exists_rep e
  change (biratMap F hF e).deg = 1 ∧ (biratMap F hF e).base = 𝟙 _
  rw [biratMap_eq F hF e α φ hα he]
  have hφb : φ.base = α.base := by
    have := congrArg BHom.base he
    simp only [Birat.comp_base, toBirat_map_base, hb] at this
    exact this.symm.trans (Category.comp_id _)
  have hφd : φ.deg = 1 := by
    have := congrArg BHom.deg he
    simp only [Birat.comp_deg, toBirat_map_deg, hd, one_mul] at this
    rw [← this]; exact hα.1
  have hFb := hbe φ α hφb
  have hFd : (F.map φ).deg = 1 := by
    have hs : IsPreStep 𝐏₁ φ := ⟨hφd, by change IsIso φ.base; rw [hφb]; exact hα.2⟩
    exact (hF φ hs).1
  have hspec := repImage_spec F hF α φ hα
  have hdeg := congrArg BHom.deg hspec
  have hbase := congrArg BHom.base hspec
  have hFαd : (F.map α).deg = 1 := (hF α hα).1
  simp only [Birat.comp_deg, toBirat_map_deg, hFαd, mul_one, hFd] at hdeg
  simp only [Birat.comp_base, toBirat_map_base] at hbase
  rw [← hFb] at hbase
  haveI : IsIso (F.map φ).base := by rw [hFb]; exact (hF α hα).2
  exact ⟨hdeg, (cancel_epi (F.map φ).base).mp (hbase.trans (Category.comp_id _).symm)⟩

end Functor

end Model

end Frobenioid

end Iut
