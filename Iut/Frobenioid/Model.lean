/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Model Frobenioids ([FrdI], Theorem 5.2(i))

Data: a divisorial monoid `Φ` on `D`, a group-like monoid `B` on `D` (the *rational function
monoid*) and a homomorphism `Div_B : B → Φ^gp` (`DivHom B Φ.toGrpOn`).

The **model Frobenioid** `Model Φ B divB` ([FrdI], Theorem 5.2(i)) has objects `(A_D, α)` with
`A_D ∈ D`, `α ∈ Φ^gp(A_D)` (the "arithmetic divisor of a line bundle"), and morphisms
`φ : (A_D, α) → (B_D, β)` the data

* `deg φ ∈ ℕ_{≥1}` (Frobenius degree), `base φ : A_D → B_D`, `div φ ∈ Φ(A_D)` (zero divisor),
* `u φ ∈ B(A_D)` (a "rational function"),

subject to `deg(φ)·α + Div(φ) = Base(φ)^*β + Div_B(u_φ)` in `Φ^gp(A_D)`, with composition

`ψ ∘ φ = (deg ψ·deg φ, Base ψ ∘ Base φ, Base(φ)^* Div(ψ) + deg(ψ)·Div(φ),
  Base(φ)^* u_ψ + deg(ψ)·u_φ)`.

`Model.toElem` is the functor to the elementary Frobenioid `F_Φ` (degree, projection, zero
divisor). This file proves the category laws and the characterizations used for Theorem
5.2(ii) (`Iut/Frobenioid/ModelFrobenioid.lean`):

* `Model.isIso_iff`: `φ` is an isomorphism iff it is linear, isometric and a base-isomorphism
  (the rational function `u_φ` is invertible because `B` is group-like);
* `Model.isPullback_iff`: pull-back morphisms are exactly the linear isometric morphisms;
* `Model.isIsotropic`: every object is isotropic, and `Model.isCoangular`: every morphism is
  co-angular.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

variable {D : Type u} [Category.{v} D]

/-- **The objects of the model Frobenioid** ([FrdI], Theorem 5.2(i)): pairs `(A_D, α)`,
`α ∈ Φ^gp(A_D)`. -/
structure Model (Φ : DivMonoid.{w} D) (B : GrpOn.{w} D) (divB : DivHom B Φ.toGrpOn) where
  /-- `A_D = Base(A)`. -/
  base : D
  /-- The divisor `α ∈ Φ^gp(A_D)`. -/
  α : Φ.obj base

namespace Model

variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

/-- **The morphisms of the model Frobenioid**. -/
@[ext]
structure Hom (X Y : Model Φ B divB) where
  /-- The Frobenius degree. -/
  deg : ℕ+
  /-- The projection to `D`. -/
  base : X.base ⟶ Y.base
  /-- The zero divisor. -/
  div : Φ.obj X.base
  div_mem : div ∈ Φ.pos X.base
  /-- The rational function `u_φ ∈ B(A_D)`. -/
  u : B.obj X.base
  /-- `deg(φ)·α + Div(φ) = Base(φ)^*β + Div_B(u_φ)`. -/
  rel : (deg : ℕ) • X.α + div = Φ.pb base Y.α + divB.app X.base u

/-- The identity `(1, id, 0, 0)`. -/
def Hom.id (X : Model Φ B divB) : Hom X X where
  deg := 1
  base := 𝟙 _
  div := 0
  div_mem := (Φ.pos _).zero_mem
  u := 0
  rel := by simp

/-- **The composition** of [FrdI], Theorem 5.2(i). -/
def Hom.comp {X Y Z : Model Φ B divB} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  deg := ψ.deg * φ.deg
  base := φ.base ≫ ψ.base
  div := Φ.pb φ.base ψ.div + (ψ.deg : ℕ) • φ.div
  div_mem := (Φ.pos _).add_mem (Φ.pb_mem _ ψ.div_mem) ((Φ.pos _).nsmul_mem φ.div_mem _)
  u := B.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u
  rel := by
    have h₁ := φ.rel
    have h₂ := congrArg (Φ.pb φ.base) ψ.rel
    simp only [map_add, map_nsmul, GrpOn.pb_comp', divB.natural] at h₂ ⊢
    rw [PNat.mul_coe]
    linear_combination (norm := module) (ψ.deg : ℕ) • h₁ + h₂

instance : Category (Model Φ B divB) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp φ := by
    refine Hom.ext (mul_one _) (Category.id_comp _) ?_ ?_ <;> simp [Hom.comp, Hom.id]
  comp_id φ := by
    refine Hom.ext (one_mul _) (Category.comp_id _) ?_ ?_ <;> simp [Hom.comp, Hom.id]
  assoc φ ψ χ := by
    refine Hom.ext (mul_assoc _ _ _).symm (Category.assoc _ _ _) ?_ ?_ <;>
    · simp only [Hom.comp, GrpOn.pb_comp', map_add, map_nsmul, smul_add, PNat.mul_coe,
        mul_smul]
      abel

@[ext] lemma hom_ext {X Y : Model Φ B divB} {φ ψ : X ⟶ Y} (h₁ : φ.deg = ψ.deg)
    (h₂ : φ.base = ψ.base) (h₃ : φ.div = ψ.div) (h₄ : φ.u = ψ.u) : φ = ψ :=
  Hom.ext h₁ h₂ h₃ h₄

@[simp] lemma id_deg (X : Model Φ B divB) : (𝟙 X : X ⟶ X).deg = 1 := rfl
@[simp] lemma id_base (X : Model Φ B divB) : (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl
@[simp] lemma id_div (X : Model Φ B divB) : (𝟙 X : X ⟶ X).div = 0 := rfl
@[simp] lemma id_u (X : Model Φ B divB) : (𝟙 X : X ⟶ X).u = 0 := rfl

section comp

variable {X Y Z : Model Φ B divB} (φ : X ⟶ Y) (ψ : Y ⟶ Z)

@[simp] lemma comp_deg : (φ ≫ ψ).deg = ψ.deg * φ.deg := rfl
@[simp] lemma comp_base : (φ ≫ ψ).base = φ.base ≫ ψ.base := rfl
@[simp] lemma comp_div : (φ ≫ ψ).div = Φ.pb φ.base ψ.div + (ψ.deg : ℕ) • φ.div := rfl
@[simp] lemma comp_u : (φ ≫ ψ).u = B.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u := rfl

end comp

/-- Constructor for morphisms. -/
def mk' {X Y : Model Φ B divB} (n : ℕ+) (f : X.base ⟶ Y.base) (Z : Φ.obj X.base)
    (hZ : Z ∈ Φ.pos X.base) (u : B.obj X.base)
    (h : (n : ℕ) • X.α + Z = Φ.pb f Y.α + divB.app X.base u) : X ⟶ Y :=
  ⟨n, f, Z, hZ, u, h⟩

@[simp] lemma mk'_deg {X Y : Model Φ B divB} (n f Z hZ u h) :
    (mk' (X := X) (Y := Y) n f Z hZ u h).deg = n := rfl
@[simp] lemma mk'_base {X Y : Model Φ B divB} (n f Z hZ u h) :
    (mk' (X := X) (Y := Y) n f Z hZ u h).base = f := rfl
@[simp] lemma mk'_div {X Y : Model Φ B divB} (n f Z hZ u h) :
    (mk' (X := X) (Y := Y) n f Z hZ u h).div = Z := rfl
@[simp] lemma mk'_u {X Y : Model Φ B divB} (n f Z hZ u h) :
    (mk' (X := X) (Y := Y) n f Z hZ u h).u = u := rfl

/-- Constructor for linear morphisms (`deg = 1`). -/
def mk1 {X Y : Model Φ B divB} (f : X.base ⟶ Y.base) (Z : Φ.obj X.base)
    (hZ : Z ∈ Φ.pos X.base) (u : B.obj X.base)
    (h : X.α + Z = Φ.pb f Y.α + divB.app X.base u) : X ⟶ Y :=
  mk' 1 f Z hZ u (by rw [PNat.one_coe, one_smul]; exact h)

@[simp] lemma mk1_deg {X Y : Model Φ B divB} (f Z hZ u h) :
    (mk1 (X := X) (Y := Y) f Z hZ u h).deg = 1 := rfl
@[simp] lemma mk1_base {X Y : Model Φ B divB} (f Z hZ u h) :
    (mk1 (X := X) (Y := Y) f Z hZ u h).base = f := rfl
@[simp] lemma mk1_div {X Y : Model Φ B divB} (f Z hZ u h) :
    (mk1 (X := X) (Y := Y) f Z hZ u h).div = Z := rfl
@[simp] lemma mk1_u {X Y : Model Φ B divB} (f Z hZ u h) :
    (mk1 (X := X) (Y := Y) f Z hZ u h).u = u := rfl

variable (Φ B divB) in
/-- **The pre-Frobenioid structure** `C → F_Φ` of the model Frobenioid (Frobenius degree,
projection to `D`, zero divisor). -/
@[simps]
def toElem : Model Φ B divB ⥤ Elem Φ where
  obj X := ⟨X.base⟩
  map φ := ⟨φ.base, φ.div, φ.div_mem, φ.deg⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable (Φ B divB) in
/-- The projection `C → D` to the base category. -/
abbrev forget : Model Φ B divB ⥤ D := toElem Φ B divB ⋙ Elem.proj

local notation "𝐏" => toElem Φ B divB

@[simp] lemma base_eq (X : Model Φ B divB) : Frobenioid.base 𝐏 X = X.base := rfl
@[simp] lemma Base_eq {X Y : Model Φ B divB} (φ : X ⟶ Y) : Base 𝐏 φ = φ.base := rfl
@[simp] lemma Div_eq {X Y : Model Φ B divB} (φ : X ⟶ Y) : Div 𝐏 φ = φ.div := rfl
@[simp] lemma degFr_eq {X Y : Model Φ B divB} (φ : X ⟶ Y) : degFr 𝐏 φ = φ.deg := rfl

/-! ### Isomorphisms -/

/-- The inverse of a linear isometric base-isomorphism `(1, f, 0, u)`: `(1, f⁻¹, 0, −(f⁻¹)^*u)`.
-/
noncomputable def invHom {X Y : Model Φ B divB} (φ : X ⟶ Y) (h₁ : φ.deg = 1) [IsIso φ.base]
    (h₃ : φ.div = 0) : Y ⟶ X :=
  mk' 1 (inv φ.base) 0 (Φ.pos _).zero_mem (-B.pb (inv φ.base) φ.u) (by
    have h := congrArg (Φ.pb (inv φ.base)) φ.rel
    rw [h₁, h₃] at h
    simp only [PNat.one_coe, one_smul, add_zero, map_add, GrpOn.pb_inv_pb,
      ← divB.natural] at h ⊢
    rw [map_neg, h]
    abel)

lemma isIso_of {X Y : Model Φ B divB} (φ : X ⟶ Y) (h₁ : φ.deg = 1) (h₂ : IsIso φ.base)
    (h₃ : φ.div = 0) : IsIso φ := by
  refine ⟨invHom φ h₁ h₃, ?_, ?_⟩
  · ext <;> simp [invHom, h₁, h₃]
  · ext <;> simp [invHom, h₁, h₃]

/-- **Isomorphisms of the model Frobenioid**: linear isometric base-isomorphisms. -/
theorem isIso_iff {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsIso φ ↔ φ.deg = 1 ∧ IsIso φ.base ∧ φ.div = 0 :=
  ⟨fun _ => ⟨degFr_of_isIso (P := 𝐏) φ, isIso_Base (P := 𝐏) φ, Div_of_isIso (P := 𝐏) φ⟩,
    fun ⟨h₁, h₂, h₃⟩ => isIso_of φ h₁ h₂ h₃⟩

/-- **Every object of the model Frobenioid is isotropic**: an isometric pre-step is an
isomorphism. -/
theorem isIsotropic (X : Model Φ B divB) : IsIsotropic 𝐏 X :=
  fun _ φ h₀ ⟨h₁, h₂⟩ => isIso_of φ h₁ h₂ h₀

/-- **Every morphism of the model Frobenioid is co-angular.** -/
theorem isCoangular {X Y : Model Φ B divB} (φ : X ⟶ Y) : IsCoangular 𝐏 φ :=
  fun _ _ _ β _ _ _ h₀ hβ _ => isIsotropic _ _ β h₀ hβ

/-! ### Pull-back morphisms -/

/-- **Pull-back morphisms of the model Frobenioid** are exactly the linear isometric
morphisms (the "only if" uses the sharpness of `Φ`). -/
theorem isPullback_iff {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsPullback 𝐏 φ ↔ φ.deg = 1 ∧ φ.div = 0 := by
  constructor
  · intro hp
    let X' : Model Φ B divB := ⟨X.base, Φ.pb φ.base Y.α⟩
    let ψ : X' ⟶ Y := mk' 1 φ.base 0 (Φ.pos _).zero_mem 0 (by simp [X'])
    obtain ⟨χ, ⟨hχ, hχb⟩, -⟩ := hp X' ψ (𝟙 _) (by simp [ψ])
    have hdeg := congrArg Hom.deg hχ
    have hdiv := congrArg Hom.div hχ
    simp only [comp_deg, comp_div, ψ, mk'_deg, mk'_div] at hdeg hdiv
    have hdeg' : φ.deg = 1 := PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val hdeg))
    refine ⟨hdeg', ?_⟩
    have hb : χ.base = 𝟙 _ := hχb
    rw [hdeg', PNat.one_coe, one_smul, hb, GrpOn.pb_id'] at hdiv
    refine Φ.sharp φ.div_mem ?_
    rw [eq_neg_of_add_eq_zero_left hdiv, neg_neg]
    exact χ.div_mem
  · rintro ⟨h₁, h₃⟩ W ψ (g : W.base ⟶ X.base) hg
    have hg' : g ≫ φ.base = ψ.base := hg
    refine ⟨mk' ψ.deg g ψ.div ψ.div_mem (ψ.u - B.pb g φ.u) ?_, ⟨?_, rfl⟩, ?_⟩
    · have h := congrArg (Φ.pb g) φ.rel
      rw [h₁, h₃] at h
      simp only [PNat.one_coe, one_smul, add_zero, map_add, ← GrpOn.pb_comp', hg',
        ← divB.natural] at h
      have h' := ψ.rel
      rw [map_sub, h]
      linear_combination (norm := module) h'
    · ext <;> simp [h₁, h₃, hg']
    · rintro χ ⟨hχ, hχb⟩
      have hb : χ.base = g := hχb
      have hdeg := congrArg Hom.deg hχ
      have hdiv := congrArg Hom.div hχ
      have hu := congrArg Hom.u hχ
      simp only [comp_deg, comp_div, comp_u, h₁, h₃, map_zero, PNat.one_coe, one_smul,
        zero_add, one_mul, hb] at hdeg hdiv hu
      ext
      · exact hdeg
      · exact hb
      · exact hdiv
      · simp only [mk'_u, ← hu]
        abel

end Model

end Frobenioid

end Iut
