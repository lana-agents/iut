/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.ModelTypes

/-!
# First properties of Frobenioids ([FrdI] §1, Propositions 1.4–1.12)

General consequences of the definition of a Frobenioid (`IsFrobenioid`, [FrdI], Definition 1.3),
valid for every Frobenioid (not only for model Frobenioids).

* **Proposition 1.7(i)** (composites): isometries, base-isomorphisms, linear morphisms, pre-steps,
  pull-back morphisms (`isPullback_comp`), co-angular morphisms, LB-invertible morphisms and
  morphisms of Frobenius type are closed under composition.
* **Proposition 1.7(v)** (factors): if `α ≫ β` is an isomorphism (resp. base-isomorphism, linear
  morphism, pre-step, isometry), so are `α` and `β`.
* **Proposition 1.4**: (i) `coangular_of_isotropic` (morphisms whose domain only maps to isotropic
  objects are co-angular); (ii) `isPullback_iff` (pull-back morphisms are exactly the
  LB-invertible linear morphisms); (iii) `isIso_of_lbInvertible_preStep` (LB-invertible pre-steps
  are isomorphisms).
* **Proposition 1.8(iii)**: `nonGroupLike_iff_exists_step` (an object is non-group-like iff it is
  the domain of a co-angular step).
* **Proposition 1.9(iv)**: `isIsotropic_iff_of_coangular_linear` (along a co-angular linear
  morphism, the domain is isotropic iff the codomain is).
* **Proposition 1.11(iii)**: `exists_unique_end_of_isPullback` (endomorphisms lift uniquely along
  pull-back morphisms).
* **Proposition 1.12(i)**: `mem_ounits_iff` (`O^×(A)` is the kernel of `Aut(A) → Aut(A_D)`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u v' u'

variable {D : Type u} [Category.{v} D] {Φ : DivMonoid.{w} D}
variable {C : Type u'} [Category.{v'} C] {P : C ⥤ Elem Φ}

/-! ### Proposition 1.7(i): composites -/

section Comp

variable {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E)

lemma IsLinear.comp (hφ : IsLinear P φ) (hψ : IsLinear P ψ) : IsLinear P (φ ≫ ψ) := by
  unfold IsLinear at *
  rw [degFr_comp, hφ, hψ, mul_one]

lemma IsIsometric.comp (hφ : IsIsometric P φ) (hψ : IsIsometric P ψ) :
    IsIsometric P (φ ≫ ψ) := by
  unfold IsIsometric at *
  rw [Div_comp, hφ, hψ, map_zero, smul_zero, add_zero]

lemma IsBaseIso.comp (hφ : IsBaseIso P φ) (hψ : IsBaseIso P ψ) : IsBaseIso P (φ ≫ ψ) := by
  haveI : IsIso (Base P φ) := hφ
  haveI : IsIso (Base P ψ) := hψ
  change IsIso (Base P (φ ≫ ψ))
  rw [Base_comp]; infer_instance

lemma IsPreStep.comp (hφ : IsPreStep P φ) (hψ : IsPreStep P ψ) : IsPreStep P (φ ≫ ψ) :=
  ⟨hφ.1.comp φ ψ hψ.1, hφ.2.comp φ ψ hψ.2⟩

/-- **Pull-back morphisms are closed under composition** ([FrdI], Proposition 1.7(i)). -/
lemma isPullback_comp (hφ : IsPullback P φ) (hψ : IsPullback P ψ) : IsPullback P (φ ≫ ψ) := by
  intro X χ g hg
  obtain ⟨χ₁, ⟨h₁, h₁b⟩, u₁⟩ := hψ X χ (g ≫ Base P φ) (by rw [Category.assoc, ← Base_comp, hg])
  obtain ⟨χ₂, ⟨h₂, h₂b⟩, u₂⟩ := hφ X χ₁ g h₁b.symm
  refine ⟨χ₂, ⟨by rw [← Category.assoc, h₂, h₁], h₂b⟩, fun χ' ⟨e₁, e₂⟩ => ?_⟩
  have : χ' ≫ φ = χ₁ := u₁ _ ⟨by rw [Category.assoc, e₁], by rw [Base_comp, e₂]⟩
  exact u₂ _ ⟨this, e₂⟩

variable (hC : IsFrobenioid P)
include hC

lemma IsCoangular.comp (hφ : IsCoangular P φ) (hψ : IsCoangular P ψ) :
    IsCoangular P (φ ≫ ψ) :=
  hC.coangular_comp φ ψ hφ hψ

lemma IsLBInvertible.comp (hφ : IsLBInvertible P φ) (hψ : IsLBInvertible P ψ) :
    IsLBInvertible P (φ ≫ ψ) :=
  ⟨hφ.1.comp φ ψ hC hψ.1, hφ.2.comp φ ψ hψ.2⟩

lemma IsFrobeniusType.comp (hφ : IsFrobeniusType P φ) (hψ : IsFrobeniusType P ψ) :
    IsFrobeniusType P (φ ≫ ψ) :=
  ⟨hφ.1.comp φ ψ hC hψ.1, hφ.2.comp φ ψ hψ.2⟩

end Comp

/-! ### Proposition 1.7(v): factors -/

section Factors

variable {A B E : C} (φ : A ⟶ B) (ψ : B ⟶ E)

lemma isLinear_of_comp (h : IsLinear P (φ ≫ ψ)) : IsLinear P φ ∧ IsLinear P ψ := by
  unfold IsLinear at *
  rw [degFr_comp] at h
  exact ⟨PNat.eq (Nat.eq_one_of_mul_eq_one_left (congrArg PNat.val h)),
    PNat.eq (Nat.eq_one_of_mul_eq_one_right (congrArg PNat.val h))⟩

lemma isIsometric_of_comp (h : IsIsometric P (φ ≫ ψ)) :
    IsIsometric P φ ∧ IsIsometric P ψ := by
  unfold IsIsometric at *
  rw [Div_comp] at h
  have h₁ : Φ.pb (Base P φ) (Div P ψ) = 0 :=
    Φ.eq_zero_of_add_eq_zero_left (Φ.pb_mem _ (Div_mem ψ)) ((Φ.pos _).nsmul_mem (Div_mem φ) _) h
  rw [h₁, zero_add] at h
  exact ⟨Φ.eq_zero_of_nsmul_eq_zero (degFr P ψ).pos h,
    Φ.pb_injective _ (by rw [h₁, map_zero])⟩

lemma isBaseIso_of_comp [TotallyEpimorphic D] (h : IsBaseIso P (φ ≫ ψ)) :
    IsBaseIso P φ ∧ IsBaseIso P ψ := by
  have h' : IsIso (Base P φ ≫ Base P ψ) := by rw [← Base_comp]; exact h
  exact ⟨isIso_left_of_isIso_comp (Base P φ) (Base P ψ),
    isIso_right_of_isIso_comp (Base P φ) (Base P ψ)⟩

lemma isPreStep_of_comp [TotallyEpimorphic D] (h : IsPreStep P (φ ≫ ψ)) :
    IsPreStep P φ ∧ IsPreStep P ψ :=
  ⟨⟨(isLinear_of_comp φ ψ h.1).1, (isBaseIso_of_comp φ ψ h.2).1⟩,
    ⟨(isLinear_of_comp φ ψ h.1).2, (isBaseIso_of_comp φ ψ h.2).2⟩⟩

end Factors

/-! ### Proposition 1.4 -/

section Prop14

/-- An isomorphism is linear, isometric and a base-isomorphism. -/
lemma isPreStep_of_isIso {A B : C} (φ : A ⟶ B) [IsIso φ] : IsPreStep P φ :=
  ⟨degFr_of_isIso φ, isIso_Base φ⟩

lemma isIsometric_of_isIso {A B : C} (φ : A ⟶ B) [IsIso φ] : IsIsometric P φ :=
  Div_of_isIso φ

/-- **[FrdI], Proposition 1.4(iii)**: an LB-invertible pre-step is an isomorphism. -/
theorem isIso_of_lbInvertible_preStep {A B : C} (φ : A ⟶ B) (h : IsLBInvertible P φ)
    (hp : IsPreStep P φ) : IsIso φ :=
  h.1 (𝟙 A) φ (𝟙 B) (by simp) (degFr_id B) h.2 hp (Or.inl (isIso_Base (𝟙 B)))

/-- **[FrdI], Proposition 1.4(i)**: if every morphism out of `A` has isotropic codomain, every
`φ : A → B` is co-angular. -/
theorem coangular_of_isotropic {A B : C} (φ : A ⟶ B)
    (h : ∀ ⦃E : C⦄ (_ : A ⟶ E), IsIsotropic P E) : IsCoangular P φ :=
  fun _ _ γ β _ _ _ hβ hp _ => h γ _ β hβ hp

lemma IsPullback.iso_comp {A A' B : C} (e : A' ≅ A) (φ : A ⟶ B) (h : IsPullback P φ) :
    IsPullback P (e.hom ≫ φ) :=
  isPullback_comp _ _ (isPullback_of_isIso e.hom) h

variable (hC : IsFrobenioid P)
include hC

/-- **[FrdI], Proposition 1.4(ii)**: pull-back morphisms are exactly the LB-invertible linear
morphisms (co-angular linear isometries). -/
theorem isPullback_iff {A B : C} (φ : A ⟶ B) :
    IsPullback P φ ↔ IsLBInvertible P φ ∧ IsLinear P φ := by
  refine ⟨hC.pullback_lb φ, fun ⟨hlb, hl⟩ => ?_⟩
  haveI := hC.epi_D
  obtain ⟨X, Y, γ, β, α, hγ, hβ, hα, hc⟩ := hC.factorization φ
  have hαl := (hC.pullback_lb α hα).2
  have hαi := (hC.pullback_lb α hα).1.2
  -- `γ` is linear, `β` is isometric
  have hl' : IsLinear P (γ ≫ β ≫ α) := by rw [hc]; exact hl
  have hγl : IsLinear P γ := (isLinear_of_comp γ (β ≫ α) hl').1
  have hi' : IsIsometric P (γ ≫ β ≫ α) := by rw [hc]; exact hlb.2
  have hβi : IsIsometric P β :=
    (isIsometric_of_comp β α (isIsometric_of_comp γ (β ≫ α) hi').2).1
  -- `β` is an isomorphism by co-angularity, `γ` an LB-invertible pre-step
  haveI : IsIso β := hlb.1 γ β α hc hαl hβi hβ (Or.inr hγ.2)
  haveI : IsIso γ := isIso_of_lbInvertible_preStep γ hγ.1 ⟨hγl, hγ.2⟩
  rw [← hc, ← Category.assoc]
  exact IsPullback.iso_comp (asIso (γ ≫ β)) α hα

end Prop14

/-! ### Propositions 1.8(iii), 1.9(iv), 1.11(iii), 1.12(i) -/

section More

variable (hC : IsFrobenioid P)
include hC

/-- **[FrdI], Proposition 1.8(iii)**: an object is non-group-like iff it is the domain of a
co-angular step. -/
theorem nonGroupLike_iff_exists_step (A : C) :
    ¬ IsGroupLike P A ↔ ∃ (B : C) (φ : A ⟶ B), IsCoangular P φ ∧ IsStep P φ := by
  constructor
  · intro h
    simp only [IsGroupLike, not_forall] at h
    obtain ⟨x, hx, hne⟩ := h
    obtain ⟨B, φ, hco, hp, hd⟩ := hC.coslice_surj A x hx
    refine ⟨B, φ, hco, hp, fun hi => hne ?_⟩
    haveI := hi
    rw [← hd]; exact Div_of_isIso φ
  · rintro ⟨B, φ, hco, hp, hni⟩ hg
    exact hni (isIso_of_lbInvertible_preStep φ ⟨hco, hg _ (Div_mem φ)⟩ hp)

omit hC in
/-- Isotropy is invariant under isomorphism. -/
lemma isIsotropic_of_iso {A A' : C} (e : A ≅ A') (h : IsIsotropic P A') : IsIsotropic P A := by
  intro E ψ hi hp
  have hi' : IsIsometric P (e.inv ≫ ψ) := (isIsometric_of_isIso e.inv).comp _ _ hi
  have hp' : IsPreStep P (e.inv ≫ ψ) := (isPreStep_of_isIso e.inv).comp _ _ hp
  haveI := h E _ hi' hp'
  have : ψ = e.hom ≫ (e.inv ≫ ψ) := by simp
  rw [this]; infer_instance

/-- **[FrdI], Proposition 1.9(iv)**: along a co-angular linear morphism `φ : A → B`, `A` is
isotropic iff `B` is. -/
theorem isIsotropic_iff_of_coangular_linear {A B : C} (φ : A ⟶ B) (hco : IsCoangular P φ)
    (hl : IsLinear P φ) : IsIsotropic P A ↔ IsIsotropic P B := by
  refine ⟨fun h => hC.isotropic_cod φ h, fun hB => ?_⟩
  obtain ⟨A', ι, hι⟩ := hC.isotropicHull A
  obtain ⟨hιi, hιp, hA', huniv⟩ := hι
  obtain ⟨β, hβ, -⟩ := huniv B φ hB
  have hβl : IsLinear P β := (isLinear_of_comp ι β (by rw [hβ]; exact hl)).2
  haveI : IsIso ι := hco (𝟙 A) ι β (by simp [hβ]) hβl hιi hιp (Or.inr (isIso_Base (𝟙 A)))
  exact isIsotropic_of_iso (asIso ι) hA'

omit hC in
/-- **[FrdI], Proposition 1.11(iii)**: along a pull-back morphism `φ : B → A`, an endomorphism
`α` of `A` and an endomorphism `β_D` of `B_D` compatible with `Base(α)` lift uniquely to an
endomorphism `β` of `B` with `β ≫ φ = φ ≫ α`. -/
theorem exists_unique_end_of_isPullback {A B : C} (φ : B ⟶ A) (hφ : IsPullback P φ)
    (α : A ⟶ A) (βD : base P B ⟶ base P B) (h : βD ≫ Base P φ = Base P φ ≫ Base P α) :
    ∃! β : B ⟶ B, β ≫ φ = φ ≫ α ∧ Base P β = βD :=
  hφ B (φ ≫ α) βD (by rw [h, Base_comp])

omit hC in
/-- **[FrdI], Proposition 1.12(i)**: `O^×(A)` is the kernel of `Aut_C(A) → Aut_D(A_D)`. -/
theorem mem_ounits_iff {A : C} (e : A ⟶ A) [IsIso e] :
    e ∈ Ounits P A ↔ IsBaseIdentity P e :=
  ⟨fun h => h.2.1, fun h => ⟨inferInstance, h, degFr_of_isIso e⟩⟩

end More

end Frobenioid

end Iut
