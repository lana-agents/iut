/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# Pre-Frobenioids and Frobenioids ([FrdI], Definitions 1.1(iv), 1.2, 1.3)

A **pre-Frobenioid** is a category `C` with a functor `P : C ⥤ F_Φ` to an elementary Frobenioid
([FrdI], Definition 1.1(iv)); `C` and `D` are connected and totally epimorphic
(`IsPreFrobenioid`). It induces `Base : C → D`, the zero divisor `Div(φ) ∈ Φ(Base(A))` and the
Frobenius degree `degFr(φ) ∈ ℕ_{≥1}` of `φ : A → B`, with (Remark 1.1.1)

  `Base(φ ∘ ψ) = Base(φ) ∘ Base(ψ)`, `Div(φ ∘ ψ) = Base(ψ)^* Div(φ) + degFr(φ)·Div(ψ)`,
  `degFr(φ ∘ ψ) = degFr(φ)·degFr(ψ)`.

Mathlib writes composition diagrammatically: `ψ ≫ φ = φ ∘ ψ`.

## Morphism and object types ([FrdI], Definition 1.2)

`IsLinear`, `IsIsometric`, `IsBaseIso`, `IsBaseFSM`, `IsPullback`, `IsPreStep`, `IsStep`,
`IsPrimaryPreStep`, `IsCoangular`, `IsLBInvertible`, `IsFrobeniusType`, `IsPrimeFrobenius`,
`IsBaseIdentity`, `IsDivIdentity`; `Ounits A = O^×(A)`, `Orhd A = O^▷(A)`; the object types
`IsFrobeniusAmple`, `IsFrobeniusTrivial`, `IsDivFrobeniusTrivial`, `IsQuasiFrobeniusTrivial`,
`IsMetricallyTrivial`, `IsBaseTrivial`, `IsAutAmple`, `IsEndAmple`, `IsGroupLike`,
`IsUnitTrivial`, `IsIsotropic`, `IsIsotropicHull`, `IsFrobeniusIsotropic`.

## The Frobenioid conditions ([FrdI], Definition 1.3)

`IsFrobenioid P` has one field per clause of Definition 1.3 (i)(a)–(vii)(b). Deviations from
the literal text (each is a logically equivalent or weaker-looking but implied reformulation):

* (i)(c) asks that the fully faithful functor `C^{pl-bk}_A → D_{A_D}` be an equivalence; full
  faithfulness is automatic (as [FrdI] notes), so the field records essential surjectivity:
  every `f : X → A_D` is, up to isomorphism over `A_D`, the base of a pull-back morphism to `A`.
* (iii)(c) asks for a *bijection of monoids* `O^▷(A) ≅ O^▷(B)` intertwined by `φ` and depending
  only on `Base(φ)`; multiplicativity follows from the intertwining relation since `φ` is an
  epimorphism (`Orhd.equiv_mul`), so the field records a bijection with the intertwining
  relation for every co-angular pre-step with the same base.
* (iii)(d) asks that `φ ↦ Div(φ)` (resp. `ψ ↦ (ψ^*)^{-1} Div(ψ)`) be an equivalence of the
  coslice (resp. slice) category of co-angular pre-steps with `Order(Φ(A))` (resp. its
  opposite). The functor is automatically faithful (morphisms of `C` are epimorphisms and
  `Order` is thin); the fields record essential surjectivity (isomorphic elements of the sharp
  monoid `Φ(A)` are equal) and fullness.
* The clauses in square brackets ("[uniquely determined]", "[necessarily unique]") are
  consequences and are not recorded.

General consequences proved here: Remark 1.2.1 (`isIso_iff_isPullback_isBaseIso`,
`IsBaseTrivial.isMetricallyTrivial`, `IsBaseIdentity.isDivIdentity`), and the uniqueness part
of (iv)(a) from (ii) and the pull-back property (`factorization_unique`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u v' u'

variable {D : Type u} [Category.{v} D] {Φ : DivMonoid.{w} D}
variable {C : Type u'} [Category.{v'} C] (P : C ⥤ Elem Φ)

/-! ### Base, divisor, Frobenius degree -/

/-- The projection `Base(A) ∈ D` of an object. -/
def base (A : C) : D := (P.obj A).base

/-- The projection `Base(φ)` of a morphism to the base category. -/
def Base {A B : C} (φ : A ⟶ B) : base P A ⟶ base P B := (P.map φ).base

/-- The zero divisor `Div(φ) ∈ Φ(Base(A))`. -/
def Div {A B : C} (φ : A ⟶ B) : Φ.obj (base P A) := (P.map φ).div

/-- The Frobenius degree `degFr(φ) ∈ ℕ_{≥1}`. -/
def degFr {A B : C} (φ : A ⟶ B) : ℕ+ := (P.map φ).deg

variable {P}

lemma Div_mem {A B : C} (φ : A ⟶ B) : Div P φ ∈ Φ.pos (base P A) := (P.map φ).div_mem

@[simp] lemma Base_id (A : C) : Base P (𝟙 A) = 𝟙 _ := by simp [Base]; rfl
@[simp] lemma Div_id (A : C) : Div P (𝟙 A) = 0 := by simp [Div]; rfl
@[simp] lemma degFr_id (A : C) : degFr P (𝟙 A) = 1 := by simp [degFr]

/-- Remark 1.1.1 (base). -/
@[simp] lemma Base_comp {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E) :
    Base P (φ ≫ ψ) = Base P φ ≫ Base P ψ := by simp [Base]; rfl

/-- Remark 1.1.1 (zero divisor). -/
@[simp] lemma Div_comp {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E) :
    Div P (φ ≫ ψ) = Φ.pb (Base P φ) (Div P ψ) + (degFr P ψ : ℕ) • Div P φ := by
  simp [Div, Base, degFr]; rfl

/-- Remark 1.1.1 (Frobenius degree). -/
@[simp] lemma degFr_comp {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E) :
    degFr P (φ ≫ ψ) = degFr P ψ * degFr P φ := by simp [degFr]

instance isIso_Base {A B : C} (φ : A ⟶ B) [IsIso φ] : IsIso (Base P φ) :=
  show IsIso ((Elem.proj (Φ := Φ)).map (P.map φ)) from inferInstance

lemma degFr_of_isIso {A B : C} (φ : A ⟶ B) [IsIso φ] : degFr P φ = 1 := by
  have h := congrArg (degFr P) (IsIso.hom_inv_id φ)
  rw [degFr_comp, degFr_id] at h
  exact PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val h))

lemma Div_of_isIso {A B : C} (φ : A ⟶ B) [IsIso φ] : Div P φ = 0 := by
  have h := congrArg (Div P) (IsIso.hom_inv_id φ)
  rw [Div_comp, Div_id, degFr_of_isIso (inv φ), PNat.one_coe, one_smul] at h
  refine Φ.sharp (Div_mem φ) ?_
  rw [eq_neg_of_add_eq_zero_right h, neg_neg]
  exact Φ.pb_mem _ (Div_mem (P := P) _)

/-! ### Types of morphisms ([FrdI], Definition 1.2(i)–(iii)) -/

variable (P)

/-- Linear: `degFr(φ) = 1`. -/
def IsLinear {A B : C} (φ : A ⟶ B) : Prop := degFr P φ = 1

/-- Isometric: `Div(φ) = 0`. -/
def IsIsometric {A B : C} (φ : A ⟶ B) : Prop := Div P φ = 0

/-- Base-isomorphism: `Base(φ)` is an isomorphism of `D`. -/
def IsBaseIso {A B : C} (φ : A ⟶ B) : Prop := IsIso (Base P φ)

/-- Base-FSM-morphism: `Base(φ)` is an FSM-morphism of `D`. -/
def IsBaseFSM {A B : C} (φ : A ⟶ B) : Prop := IsFSM (Base P φ)

/-- **Pull-back morphisms** ([FrdI], Definition 1.2(ii)): `Hom_C(−, A) → Hom_C(−, B)
×_{Hom_D(−, B_D)} Hom_D(−, A_D)`, `χ ↦ (φ ∘ χ, Base(χ))`, is a bijection. -/
def IsPullback {A B : C} (φ : A ⟶ B) : Prop :=
  ∀ (X : C) (ψ : X ⟶ B) (g : base P X ⟶ base P A), g ≫ Base P φ = Base P ψ →
    ∃! χ : X ⟶ A, χ ≫ φ = ψ ∧ Base P χ = g

/-- Pre-steps: linear base-isomorphisms ([FrdI], Definition 1.2(iii)). -/
def IsPreStep {A B : C} (φ : A ⟶ B) : Prop := IsLinear P φ ∧ IsBaseIso P φ

/-- Steps: pre-steps which are not isomorphisms. -/
def IsStep {A B : C} (φ : A ⟶ B) : Prop := IsPreStep P φ ∧ ¬ IsIso φ

/-- Primary pre-steps: pre-steps with primary zero divisor. -/
def IsPrimaryPreStep {A B : C} (φ : A ⟶ B) : Prop := IsPreStep P φ ∧ Φ.IsPrimary (Div P φ)

/-- **Co-angular morphisms** ([FrdI], Definition 1.2(iii)): for every factorization
`φ = α ∘ β ∘ γ` with `α` linear, `β` an isometric pre-step and `α` or `γ` a base-isomorphism,
`β` is an isomorphism. -/
def IsCoangular {A B : C} (φ : A ⟶ B) : Prop :=
  ∀ ⦃X Y : C⦄ (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B), γ ≫ β ≫ α = φ → IsLinear P α →
    IsIsometric P β → IsPreStep P β → (IsBaseIso P α ∨ IsBaseIso P γ) → IsIso β

/-- LB-invertible: co-angular and isometric. -/
def IsLBInvertible {A B : C} (φ : A ⟶ B) : Prop := IsCoangular P φ ∧ IsIsometric P φ

/-- Morphisms of Frobenius type: LB-invertible base-isomorphisms. -/
def IsFrobeniusType {A B : C} (φ : A ⟶ B) : Prop := IsLBInvertible P φ ∧ IsBaseIso P φ

/-- Prime-Frobenius morphisms: morphisms of Frobenius type of prime Frobenius degree. -/
def IsPrimeFrobenius {A B : C} (φ : A ⟶ B) : Prop :=
  IsFrobeniusType P φ ∧ (degFr P φ : ℕ).Prime

/-- Base-identity endomorphisms: `Base(e) = id`. -/
def IsBaseIdentity {A : C} (e : A ⟶ A) : Prop := Base P e = 𝟙 _

/-- Div-identity endomorphisms: `Φ(e) = Φ(id)`. -/
def IsDivIdentity {A : C} (e : A ⟶ A) : Prop := ∀ x, Φ.pb (Base P e) x = x

/-- `O^×(A) ⊆ Aut_C(A)`: the base-identity linear automorphisms. -/
def Ounits (A : C) : Set (A ⟶ A) := {e | IsIso e ∧ IsBaseIdentity P e ∧ IsLinear P e}

/-- `O^▷(A) ⊆ End_C(A)`: the base-identity linear endomorphisms. -/
def Orhd (A : C) : Set (A ⟶ A) := {e | IsBaseIdentity P e ∧ IsLinear P e}

/-! ### Types of objects ([FrdI], Definition 1.2(iv)) -/

/-- Frobenius-ample: endomorphisms of every Frobenius degree. -/
def IsFrobeniusAmple (A : C) : Prop := ∀ n : ℕ+, ∃ e : A ⟶ A, degFr P e = n

/-- **Frobenius-trivial objects**: a monoid homomorphism `ζ : ℕ_{≥1} → End(A)` splitting the
Frobenius degree, with values base-identity endomorphisms of Frobenius type. -/
def IsFrobeniusTrivial (A : C) : Prop :=
  ∃ ζ : ℕ+ → (A ⟶ A), ζ 1 = 𝟙 A ∧ (∀ m n, ζ (m * n) = ζ m ≫ ζ n) ∧
    ∀ n, degFr P (ζ n) = n ∧ IsBaseIdentity P (ζ n) ∧ IsFrobeniusType P (ζ n)

/-- Div-Frobenius-trivial objects (as Frobenius-trivial, with Div-identity values). -/
def IsDivFrobeniusTrivial (A : C) : Prop :=
  ∃ ζ : ℕ+ → (A ⟶ A), ζ 1 = 𝟙 A ∧ (∀ m n, ζ (m * n) = ζ m ≫ ζ n) ∧
    ∀ n, degFr P (ζ n) = n ∧ IsDivIdentity P (ζ n) ∧ IsFrobeniusType P (ζ n)

/-- Quasi-Frobenius-trivial: base-identity endomorphisms of every Frobenius degree. -/
def IsQuasiFrobeniusTrivial (A : C) : Prop :=
  ∀ n : ℕ+, ∃ e : A ⟶ A, degFr P e = n ∧ IsBaseIdentity P e

/-- Metrically trivial: every co-angular pre-step out of `A` has codomain isomorphic to `A`. -/
def IsMetricallyTrivial (A : C) : Prop :=
  ∀ (B : C) (φ : A ⟶ B), IsCoangular P φ → IsPreStep P φ → Nonempty (B ≅ A)

/-- Base-trivial: every object with isomorphic base is isomorphic to `A`. -/
def IsBaseTrivial (A : C) : Prop :=
  ∀ B : C, Nonempty (base P A ≅ base P B) → Nonempty (A ≅ B)

/-- Aut-ample: `Aut_C(A) → Aut_D(A_D)` is surjective. -/
def IsAutAmple (A : C) : Prop :=
  ∀ g : base P A ≅ base P A, ∃ e : A ≅ A, Base P e.hom = g.hom

/-- End-ample: `End_C(A) → End_D(A_D)` is surjective. -/
def IsEndAmple (A : C) : Prop := ∀ g : base P A ⟶ base P A, ∃ e : A ⟶ A, Base P e = g

/-- Group-like: `Φ(A) = 0`. -/
def IsGroupLike (A : C) : Prop := ∀ x ∈ Φ.pos (base P A), x = 0

/-- Unit-trivial: `O^×(A) = {1}`. -/
def IsUnitTrivial (A : C) : Prop := ∀ e ∈ Ounits P A, e = 𝟙 A

/-- **Isotropic objects**: every isometric pre-step out of `A` is an isomorphism. -/
def IsIsotropic (A : C) : Prop :=
  ∀ (B : C) (φ : A ⟶ B), IsIsometric P φ → IsPreStep P φ → IsIso φ

/-- Isotropic hulls: isometric pre-steps to an isotropic object, universal among morphisms to
isotropic objects. -/
def IsIsotropicHull {A B : C} (φ : A ⟶ B) : Prop :=
  IsIsometric P φ ∧ IsPreStep P φ ∧ IsIsotropic P B ∧
    ∀ (E : C) (γ : A ⟶ E), IsIsotropic P E → ∃! β : B ⟶ E, φ ≫ β = γ

/-- Frobenius-isotropic: a morphism of Frobenius type to an isotropic object. -/
def IsFrobeniusIsotropic (A : C) : Prop :=
  ∃ (B : C) (φ : A ⟶ B), IsFrobeniusType P φ ∧ IsIsotropic P B

/-! ### Pre-Frobenioids and Frobenioids -/

/-- **Pre-Frobenioids** ([FrdI], Definition 1.1(iv)): `C` and `D` are connected and totally
epimorphic (`Φ` is divisorial by construction of `DivMonoid`). -/
structure IsPreFrobenioid (_P : C ⥤ Elem Φ) : Prop where
  connected_D : IsConnected D
  epi_D : TotallyEpimorphic D
  connected_C : IsConnected C
  epi_C : TotallyEpimorphic C

/-- **Frobenioids** ([FrdI], Definition 1.3). -/
structure IsFrobenioid : Prop extends IsPreFrobenioid P where
  /-- (i)(a) Every isomorphism class of `D` is the base of a Frobenius-trivial object. -/
  base_surj : ∀ X : D, ∃ A : C, IsFrobeniusTrivial P A ∧ Nonempty (base P A ≅ X)
  /-- (i)(b) An isomorphism `α : A_D ≅ B_D` is `Base(ψ) ∘ Base(φ)⁻¹` for pre-steps
  `φ : E → A`, `ψ : E → B`. -/
  preStep_span : ∀ (A B : C) (α : base P A ≅ base P B), ∃ (E : C) (φ : E ⟶ A) (ψ : E ⟶ B),
    IsPreStep P φ ∧ IsPreStep P ψ ∧ Base P φ ≫ α.hom = Base P ψ
  /-- (i)(c) `C^{pl-bk}_A → D_{A_D}` is an equivalence (essential surjectivity). -/
  pullback_surj : ∀ (A : C) (X : D) (f : X ⟶ base P A), ∃ (B : C) (φ : B ⟶ A)
    (e : base P B ≅ X), IsPullback P φ ∧ e.hom ≫ f = Base P φ
  /-- (ii) Morphisms of Frobenius type of every degree, unique up to unique isomorphism. -/
  frobenius : ∀ (A : C) (n : ℕ+), ∃ (B : C) (φ : A ⟶ B), IsFrobeniusType P φ ∧ degFr P φ = n ∧
    ∀ (E : C) (ψ : A ⟶ E), IsFrobeniusType P ψ → degFr P ψ = n → ∃ β : B ≅ E, φ ≫ β.hom = ψ
  /-- (iii)(a) Co-angular morphisms are closed under composition. -/
  coangular_comp : ∀ {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E), IsCoangular P φ → IsCoangular P ψ →
    IsCoangular P (φ ≫ ψ)
  /-- (iii)(b) If there is a co-angular pre-step `A' → A`, every morphism `A' → A` is
  co-angular. -/
  coangular_of_preStep : ∀ {A' A : C} (φ ψ : A' ⟶ A), IsCoangular P φ → IsPreStep P φ →
    IsCoangular P ψ
  /-- (iii)(c) A co-angular pre-step `φ : A → B` induces a bijection `O^▷(A) ≅ O^▷(B)`,
  `α ↦ β` with `β ∘ φ = φ ∘ α`, depending only on `Base(φ)`. -/
  orhd_equiv : ∀ {A B : C} (φ : A ⟶ B), IsCoangular P φ → IsPreStep P φ →
    ∃ e : Orhd P A ≃ Orhd P B, ∀ φ' : A ⟶ B, IsCoangular P φ' → IsPreStep P φ' →
      Base P φ' = Base P φ → ∀ a, φ' ≫ (e a).1 = a.1 ≫ φ'
  /-- (iii)(d) `_A C^{coa-pre} → Order(Φ(A))`, `φ ↦ Div(φ)`, is essentially surjective … -/
  coslice_surj : ∀ (A : C) (z : Φ.obj (base P A)), z ∈ Φ.pos (base P A) →
    ∃ (B : C) (φ : A ⟶ B), IsCoangular P φ ∧ IsPreStep P φ ∧ Div P φ = z
  /-- … and full. -/
  coslice_full : ∀ {A B₁ B₂ : C} (φ₁ : A ⟶ B₁) (φ₂ : A ⟶ B₂), IsCoangular P φ₁ →
    IsPreStep P φ₁ → IsCoangular P φ₂ → IsPreStep P φ₂ → Φ.le (Div P φ₁) (Div P φ₂) →
    ∃ χ : B₁ ⟶ B₂, IsCoangular P χ ∧ IsPreStep P χ ∧ φ₁ ≫ χ = φ₂
  /-- (iii)(d) `C^{coa-pre}_A → Order(Φ(A))^op`, `ψ ↦ (ψ^*)⁻¹ Div(ψ)`, is essentially
  surjective … -/
  slice_surj : ∀ (A : C) (z : Φ.obj (base P A)), z ∈ Φ.pos (base P A) →
    ∃ (B : C) (ψ : B ⟶ A), IsCoangular P ψ ∧ IsPreStep P ψ ∧ Div P ψ = Φ.pb (Base P ψ) z
  /-- … and full. -/
  slice_full : ∀ {A B₁ B₂ : C} (ψ₁ : B₁ ⟶ A) (ψ₂ : B₂ ⟶ A) (z₁ z₂ : Φ.obj (base P A)),
    IsCoangular P ψ₁ → IsPreStep P ψ₁ → IsCoangular P ψ₂ → IsPreStep P ψ₂ →
    Div P ψ₁ = Φ.pb (Base P ψ₁) z₁ → Div P ψ₂ = Φ.pb (Base P ψ₂) z₂ → Φ.le z₂ z₁ →
    ∃ χ : B₁ ⟶ B₂, IsCoangular P χ ∧ IsPreStep P χ ∧ χ ≫ ψ₂ = ψ₁
  /-- (iv)(a) Every morphism factors as `α ∘ β ∘ γ` (pull-back ∘ pre-step ∘ Frobenius type) …
  -/
  factorization : ∀ {A B : C} (φ : A ⟶ B), ∃ (X Y : C) (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B),
    IsFrobeniusType P γ ∧ IsPreStep P β ∧ IsPullback P α ∧ γ ≫ β ≫ α = φ
  /-- … uniquely up to `(α, β, γ) ↦ (α ∘ δ, δ⁻¹ ∘ β ∘ ε, ε⁻¹ ∘ γ)`. -/
  factorization_unique : ∀ {A B X Y X' Y' : C} (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B)
    (γ' : A ⟶ X') (β' : X' ⟶ Y') (α' : Y' ⟶ B), IsFrobeniusType P γ → IsPreStep P β →
    IsPullback P α → IsFrobeniusType P γ' → IsPreStep P β' → IsPullback P α' →
    γ ≫ β ≫ α = γ' ≫ β' ≫ α' →
    ∃ (δ : Y' ≅ Y) (ε : X' ≅ X), α' = δ.hom ≫ α ∧ β' = ε.hom ≫ β ≫ δ.inv ∧ γ' = γ ≫ ε.inv
  /-- (iv)(b) Pull-back morphisms are LB-invertible and linear. -/
  pullback_lb : ∀ {A B : C} (φ : A ⟶ B), IsPullback P φ → IsLBInvertible P φ ∧ IsLinear P φ
  /-- (v)(a) Pre-steps are monomorphisms. -/
  preStep_mono : ∀ {A B : C} (φ : A ⟶ B), IsPreStep P φ → Mono φ
  /-- (v)(b) A pre-step is (isometric pre-step) ∘ (co-angular pre-step) … -/
  preStep_factor : ∀ {A B : C} (φ : A ⟶ B), IsPreStep P φ → ∃ (X : C) (β : A ⟶ X) (α : X ⟶ B),
    IsIsometric P α ∧ IsPreStep P α ∧ IsCoangular P β ∧ IsPreStep P β ∧ β ≫ α = φ
  /-- … uniquely up to isomorphism. -/
  preStep_factor_unique : ∀ {A B X X' : C} (β : A ⟶ X) (α : X ⟶ B) (β' : A ⟶ X')
    (α' : X' ⟶ B), IsIsometric P α → IsPreStep P α → IsCoangular P β → IsPreStep P β →
    IsIsometric P α' → IsPreStep P α' → IsCoangular P β' → IsPreStep P β' → β ≫ α = β' ≫ α' →
    ∃ ε : X' ≅ X, α' = ε.hom ≫ α ∧ β' = β ≫ ε.inv
  /-- (v)(c) A pre-step is (co-angular pre-step) ∘ (isometric pre-step) … -/
  preStep_factor' : ∀ {A B : C} (φ : A ⟶ B), IsPreStep P φ → ∃ (X : C) (β : A ⟶ X) (α : X ⟶ B),
    IsCoangular P α ∧ IsPreStep P α ∧ IsIsometric P β ∧ IsPreStep P β ∧ β ≫ α = φ
  /-- … uniquely up to isomorphism. -/
  preStep_factor'_unique : ∀ {A B X X' : C} (β : A ⟶ X) (α : X ⟶ B) (β' : A ⟶ X')
    (α' : X' ⟶ B), IsCoangular P α → IsPreStep P α → IsIsometric P β → IsPreStep P β →
    IsCoangular P α' → IsPreStep P α' → IsIsometric P β' → IsPreStep P β' → β ≫ α = β' ≫ α' →
    ∃ ε : X' ≅ X, α' = ε.hom ≫ α ∧ β' = β ≫ ε.inv
  /-- (vi) Base- and metrically equivalent co-angular pre-steps differ by a unit. -/
  units : ∀ {A B : C} (φ ψ : A ⟶ B), IsCoangular P φ → IsPreStep P φ → IsCoangular P ψ →
    IsPreStep P ψ → Base P φ = Base P ψ → Div P φ = Div P ψ → ∃ a ∈ Ounits P B, φ = ψ ≫ a
  /-- (vii)(a) Isotropic hulls exist. -/
  isotropicHull : ∀ A : C, ∃ (B : C) (φ : A ⟶ B), IsIsotropicHull P φ
  /-- (vii)(b) Codomains of morphisms out of isotropic objects are isotropic. -/
  isotropic_cod : ∀ {A E : C} (_ : A ⟶ E), IsIsotropic P A → IsIsotropic P E

/-! ### General consequences -/

variable {P}

lemma isPullback_of_isIso {A B : C} (φ : A ⟶ B) [IsIso φ] : IsPullback P φ := by
  intro X ψ g hg
  refine ⟨ψ ≫ inv φ, ⟨by simp, ?_⟩, fun χ ⟨h₁, _⟩ => by simp [← h₁]⟩
  rw [Base_comp, ← hg, Category.assoc, ← Base_comp, IsIso.hom_inv_id, Base_id,
    Category.comp_id]

/-- **[FrdI], Remark 1.2.1**: a pull-back morphism is a base-isomorphism iff it is an
isomorphism. -/
theorem isIso_iff_isPullback_isBaseIso {A B : C} (φ : A ⟶ B) :
    IsIso φ ↔ IsPullback P φ ∧ IsBaseIso P φ := by
  refine ⟨fun h => ⟨isPullback_of_isIso φ, isIso_Base φ⟩, fun ⟨hp, hb⟩ => ?_⟩
  haveI : IsIso (Base P φ) := hb
  obtain ⟨χ, ⟨h₁, h₂⟩, -⟩ := hp B (𝟙 B) (inv (Base P φ)) (by simp)
  obtain ⟨χ', -, hu⟩ := hp A φ (𝟙 _) (by simp)
  have e₁ : φ ≫ χ = 𝟙 A := by
    rw [hu (φ ≫ χ) ⟨by rw [Category.assoc, h₁, Category.comp_id], by simp [h₂]⟩,
      hu (𝟙 A) ⟨by simp, by simp⟩]
  exact ⟨χ, e₁, h₁⟩

/-- Remark 1.2.1: base-trivial objects are metrically trivial. -/
lemma IsBaseTrivial.isMetricallyTrivial {A : C} (h : IsBaseTrivial P A) :
    IsMetricallyTrivial P A := by
  intro B φ _ hφ
  haveI : IsIso (Base P φ) := hφ.2
  obtain ⟨e⟩ := h B ⟨asIso (Base P φ)⟩
  exact ⟨e.symm⟩

/-- Remark 1.2.1: base-identity endomorphisms are Div-identity endomorphisms. -/
lemma IsBaseIdentity.isDivIdentity {A : C} {e : A ⟶ A} (h : IsBaseIdentity P e) :
    IsDivIdentity P e := by
  intro x
  rw [show Base P e = 𝟙 _ from h, GrpOn.pb_id']

/-- The bijection of (iii)(c) is multiplicative: since `φ` is an epimorphism, the intertwining
relation `β ∘ φ = φ ∘ α` determines `β`, and composites go to composites. -/
lemma Orhd.equiv_mul [TotallyEpimorphic C] {A B : C} (φ : A ⟶ B) (e : Orhd P A ≃ Orhd P B)
    (he : ∀ a, φ ≫ (e a).1 = a.1 ≫ φ) (a b : Orhd P A) (ab : Orhd P A)
    (hab : ab.1 = a.1 ≫ b.1) : (e ab).1 = (e a).1 ≫ (e b).1 :=
  TotallyEpimorphic.cancel φ (by
    rw [he, hab, Category.assoc, ← he b, ← Category.assoc, ← he a, Category.assoc])

/-- **Uniqueness of the factorization (iv)(a)** from (ii), the pull-back property and total
epimorphicity of `C`: this shows that the uniqueness clause of Definition 1.3(iv)(a) is a
formal consequence. -/
theorem factorization_unique_of [TotallyEpimorphic C]
    (hii : ∀ {A X X' : C} (γ : A ⟶ X) (γ' : A ⟶ X'), IsFrobeniusType P γ →
      IsFrobeniusType P γ' → degFr P γ = degFr P γ' → ∃ e : X ≅ X', γ ≫ e.hom = γ')
    {A B X Y X' Y' : C} (γ : A ⟶ X) (β : X ⟶ Y) (α : Y ⟶ B)
    (γ' : A ⟶ X') (β' : X' ⟶ Y') (α' : Y' ⟶ B) (hγ : IsFrobeniusType P γ) (hβ : IsPreStep P β)
    (hα : IsPullback P α) (hγ' : IsFrobeniusType P γ') (hβ' : IsPreStep P β')
    (hα' : IsPullback P α') (hα1 : IsLinear P α) (hα1' : IsLinear P α')
    (h : γ ≫ β ≫ α = γ' ≫ β' ≫ α') :
    ∃ (δ : Y' ≅ Y) (ε : X' ≅ X), α' = δ.hom ≫ α ∧ β' = ε.hom ≫ β ≫ δ.inv ∧ γ' = γ ≫ ε.inv := by
  have hdeg : degFr P γ = degFr P γ' := by
    have := congrArg (degFr P) h
    simp only [degFr_comp] at this
    rw [hα1, hα1', hβ.1, hβ'.1] at this
    simpa using this
  obtain ⟨e, he⟩ := hii γ γ' hγ hγ' hdeg
  have h₂ : β ≫ α = e.hom ≫ β' ≫ α' :=
    TotallyEpimorphic.cancel γ (by rw [h, ← he, Category.assoc])
  haveI : IsIso (Base P β) := hβ.2
  haveI : IsIso (Base P β') := hβ'.2
  have hb : Base P β ≫ Base P α = Base P e.hom ≫ Base P β' ≫ Base P α' := by
    simpa using congrArg (Base P) h₂
  -- `m : Y → Y'` with `m ≫ α' = α`
  obtain ⟨m, ⟨hm₁, hm₂⟩, -⟩ := hα' Y α (inv (Base P β) ≫ Base P e.hom ≫ Base P β')
    (by rw [Category.assoc, Category.assoc, ← hb]; simp)
  -- `m' : Y' → Y` with `m' ≫ α = α'`
  have k₁ : Base P e.hom ≫ Base P e.inv = 𝟙 _ := by rw [← Base_comp, e.hom_inv_id, Base_id]
  have k₂ : Base P e.inv ≫ Base P e.hom = 𝟙 _ := by rw [← Base_comp, e.inv_hom_id, Base_id]
  have hb' : Base P β' ≫ Base P α' = Base P e.inv ≫ Base P β ≫ Base P α := by
    rw [hb, reassoc_of% k₂]
  obtain ⟨m', ⟨hm₁', hm₂'⟩, -⟩ := hα Y' α' (inv (Base P β') ≫ Base P e.inv ≫ Base P β)
    (by rw [Category.assoc, Category.assoc, ← hb']; simp)
  obtain ⟨_, -, uα⟩ := hα Y α (𝟙 _) (by simp)
  obtain ⟨_, -, uα'⟩ := hα' Y' α' (𝟙 _) (by simp)
  have hmm' : m ≫ m' = 𝟙 Y := by
    rw [uα (m ≫ m') ⟨by rw [Category.assoc, hm₁', hm₁], by
      rw [Base_comp, hm₂, hm₂']
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% k₁, IsIso.inv_hom_id]⟩,
      uα (𝟙 Y) ⟨by simp, by simp⟩]
  have hm'm : m' ≫ m = 𝟙 Y' := by
    rw [uα' (m' ≫ m) ⟨by rw [Category.assoc, hm₁, hm₁'], by
      rw [Base_comp, hm₂, hm₂']
      simp only [Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% k₂, IsIso.inv_hom_id]⟩,
      uα' (𝟙 Y') ⟨by simp, by simp⟩]
  -- `e.hom ≫ β' = β ≫ m`
  have hβe : e.hom ≫ β' = β ≫ m := by
    obtain ⟨_, -, u⟩ := hα' X (β ≫ α) (Base P β ≫ inv (Base P β) ≫ Base P e.hom ≫ Base P β')
      (by simp only [IsIso.hom_inv_id_assoc, Category.assoc, Base_comp, hb])
    rw [u (e.hom ≫ β') ⟨by rw [Category.assoc, h₂], by simp⟩,
      u (β ≫ m) ⟨by rw [Category.assoc, hm₁], by rw [Base_comp, hm₂]⟩]
  refine ⟨⟨m', m, hm'm, hmm'⟩, e.symm, hm₁'.symm, ?_, ?_⟩
  · change β' = e.inv ≫ β ≫ m
    rw [← hβe, Iso.inv_hom_id_assoc]
  · change γ' = γ ≫ e.hom
    exact he.symm

end Frobenioid

end Iut
