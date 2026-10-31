/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.BaseFrob

/-!
# The base-field-theoretic hull of a tempered Frobenioid ([EtTh], Definition 3.6(iv), Remark 3.6.3)

[EtTh], Definition 3.6(iv): the data `(D, Φ^bs-fld, F, F → (Φ^bs-fld)^gp)` determine a model
Frobenioid `C^bs-fld`, the **base-field-theoretic hull** of the tempered Frobenioid `C` of
`(D, Φ, B, B → Φ^gp)`; "the natural inclusion `Φ^bs-fld(−) ⊆ Φ(−)` determines a natural faithful
functor `C^bs-fld → C`". A morphism of `C` is **base-field-theoretic** if its zero divisor lies in
`Φ^bs-fld(−)`. Remark 3.6.3: the morphisms of the essential image of `C^bs-fld → C` are the
base-field-theoretic morphisms between objects of the essential image; in particular
`C^bs-fld → C` is isomorphism-full.

We work with abstract model data: a natural homomorphism `ι_Φ : Φ'^gp → Φ^gp` mapping `Φ'` into
`Φ` (for the hull: the inclusion `Φ^bs-fld ⊆ Φ`) and a natural homomorphism `ι_B : B' → B`
compatible with the divisor maps (for the hull: `F = F^Λ_0|_D ×_{(Φ^{ℝ-log})^gp} Φ^gp → B`).

* `Model.hullFunctor`: the functor `Model Φ' B' divB' ⥤ Model Φ B divB`,
  `(A, α) ↦ (A, ι α)`, `(n, f, d, u) ↦ (n, f, ι d, ι u)`; faithful for injective `ι`
  (`Model.hullFunctor_faithful`);
* `Model.IsBsFld`: base-field-theoretic morphisms; they contain the identities and are closed
  under composition (`Model.isBsFld_id`, `Model.isBsFld_comp`);
* **Remark 3.6.3** (`Model.exists_hullFunctor_map_iff`): when `ι_Φ` is injective and
  `B' = B ×_{Φ^gp} Φ'^gp` (the fibre product defining `F`), a morphism between objects in the
  image of the hull is in the image of the hull iff it is base-field-theoretic; in particular the
  hull functor is full on base-field-theoretic morphisms and isomorphism-full
  (`Model.hullFunctor_preimage_iso`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w v u

namespace Model

variable {D : Type u} [Category.{v} D]
variable {Φ Φ' : DivMonoid.{w} D} {B B' : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}
  {divB' : DivHom B' Φ'.toGrpOn}

section Hull

variable (ιΦ : DivHom Φ'.toGrpOn Φ.toGrpOn) (ιB : DivHom B' B)
  (hpos : ∀ A x, x ∈ Φ'.pos A → ιΦ.app A x ∈ Φ.pos A)
  (hdiv : ∀ A x, divB.app A (ιB.app A x) = ιΦ.app A (divB'.app A x))

/-- The image `(A, ι α)` of an object of the hull. -/
abbrev hullObj (X : Model Φ' B' divB') : Model Φ B divB := ⟨X.base, ιΦ.app _ X.α⟩

/-- The image `(n, f, ι d, ι u)` of a morphism of the hull. -/
def hullMap {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) : hullObj ιΦ X ⟶ hullObj (divB := divB) ιΦ Y where
  deg := φ.deg
  base := φ.base
  div := ιΦ.app _ φ.div
  div_mem := hpos _ _ φ.div_mem
  u := ιB.app _ φ.u
  rel := by
    have h := congrArg (ιΦ.app X.base) φ.rel
    simp only [map_add, map_nsmul, ιΦ.natural] at h
    change (φ.deg : ℕ) • ιΦ.app _ X.α + ιΦ.app _ φ.div =
      Φ.pb φ.base (ιΦ.app _ Y.α) + divB.app _ (ιB.app _ φ.u)
    rw [hdiv]
    exact h

/-- **The functor `C^bs-fld → C`** ([EtTh], Definition 3.6(iv)) attached to `ι_Φ, ι_B`. -/
def hullFunctor : Model Φ' B' divB' ⥤ Model Φ B divB where
  obj := hullObj ιΦ
  map φ := hullMap ιΦ ιB hpos hdiv φ
  map_id X := by
    ext
    · rfl
    · rfl
    · exact map_zero _
    · exact map_zero _
  map_comp φ ψ := by
    ext
    · rfl
    · rfl
    · change ιΦ.app _ (Φ'.pb φ.base ψ.div + (ψ.deg : ℕ) • φ.div) =
        Φ.pb φ.base (ιΦ.app _ ψ.div) + (ψ.deg : ℕ) • ιΦ.app _ φ.div
      rw [map_add, map_nsmul, ιΦ.natural]
    · change ιB.app _ (B'.pb φ.base ψ.u + (ψ.deg : ℕ) • φ.u) =
        B.pb φ.base (ιB.app _ ψ.u) + (ψ.deg : ℕ) • ιB.app _ φ.u
      rw [map_add, map_nsmul, ιB.natural]

@[simp] lemma hullFunctor_obj_base (X : Model Φ' B' divB') :
    ((hullFunctor ιΦ ιB hpos hdiv).obj X).base = X.base := rfl

@[simp] lemma hullFunctor_obj_α (X : Model Φ' B' divB') :
    ((hullFunctor ιΦ ιB hpos hdiv).obj X).α = ιΦ.app _ X.α := rfl

@[simp] lemma hullFunctor_map_deg {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    ((hullFunctor ιΦ ιB hpos hdiv).map φ).deg = φ.deg := rfl

@[simp] lemma hullFunctor_map_base {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    ((hullFunctor ιΦ ιB hpos hdiv).map φ).base = φ.base := rfl

@[simp] lemma hullFunctor_map_div {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    ((hullFunctor ιΦ ιB hpos hdiv).map φ).div = ιΦ.app _ φ.div := rfl

@[simp] lemma hullFunctor_map_u {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    ((hullFunctor ιΦ ιB hpos hdiv).map φ).u = ιB.app _ φ.u := rfl

/-- **`C^bs-fld → C` is faithful** ([EtTh], Definition 3.6(iv)) when `ι_Φ`, `ι_B` are injective. -/
theorem hullFunctor_faithful (hιΦ : ∀ A, Function.Injective (ιΦ.app A))
    (hιB : ∀ A, Function.Injective (ιB.app A)) : (hullFunctor ιΦ ιB hpos hdiv).Faithful where
  map_injective {X Y} φ ψ h := by
    ext
    · have := congrArg Hom.deg h
      exact this
    · have := congrArg Hom.base h
      exact this
    · have := congrArg Hom.div h
      exact hιΦ _ this
    · have := congrArg Hom.u h
      exact hιB _ this

/-- **Base-field-theoretic morphisms** ([EtTh], Definition 3.6(iv)): the zero divisor lies in the
image of `Φ'` (`= Φ^bs-fld`). -/
def IsBsFld {X Y : Model Φ B divB} (φ : X ⟶ Y) : Prop :=
  ∃ d ∈ Φ'.pos X.base, ιΦ.app _ d = φ.div

lemma isBsFld_id (X : Model Φ B divB) : IsBsFld ιΦ (𝟙 X) :=
  ⟨0, (Φ'.pos _).zero_mem, map_zero _⟩

lemma isBsFld_comp {X Y Z : Model Φ B divB} {φ : X ⟶ Y} {ψ : Y ⟶ Z} (hφ : IsBsFld ιΦ φ)
    (hψ : IsBsFld ιΦ ψ) : IsBsFld ιΦ (φ ≫ ψ) := by
  obtain ⟨d, hd, hφd⟩ := hφ
  obtain ⟨e, he, hψe⟩ := hψ
  refine ⟨Φ'.pb φ.base e + (ψ.deg : ℕ) • d,
    (Φ'.pos _).add_mem (Φ'.pb_mem _ he) ((Φ'.pos _).nsmul_mem hd _), ?_⟩
  rw [comp_div, map_add, map_nsmul, ιΦ.natural, hψe, hφd]

lemma isBsFld_of_isIso {X Y : Model Φ B divB} (φ : X ⟶ Y) [IsIso φ] : IsBsFld ιΦ φ :=
  ⟨0, (Φ'.pos _).zero_mem, by rw [map_zero, ((isIso_iff φ).1 inferInstance).2.2]⟩

lemma hullFunctor_map_isBsFld {X Y : Model Φ' B' divB'} (φ : X ⟶ Y) :
    IsBsFld ιΦ ((hullFunctor ιΦ ιB hpos hdiv).map φ) :=
  ⟨φ.div, φ.div_mem, rfl⟩

/-- **[EtTh], Remark 3.6.3** (morphisms): if `ι_Φ` is injective and
`B' = B ×_{Φ^gp} Φ'^gp` (the fibre product defining `F` in Definition 3.6(ii)(b)), then a morphism
of `C` between objects of the hull comes from the hull iff it is base-field-theoretic. -/
theorem exists_hullFunctor_map_iff (hιΦ : ∀ A, Function.Injective (ιΦ.app A))
    (hfib : ∀ A (b : B.obj A) (y : Φ'.obj A), divB.app A b = ιΦ.app A y →
      ∃ b' : B'.obj A, ιB.app A b' = b) {X Y : Model Φ' B' divB'}
    (φ : hullObj ιΦ X ⟶ hullObj (divB := divB) ιΦ Y) :
    (∃ φ' : X ⟶ Y, (hullFunctor ιΦ ιB hpos hdiv).map φ' = φ) ↔ IsBsFld ιΦ φ := by
  constructor
  · rintro ⟨φ', rfl⟩
    exact hullFunctor_map_isBsFld ιΦ ιB hpos hdiv φ'
  · rintro ⟨d, hd, hdφ⟩
    have hrel : (φ.deg : ℕ) • ιΦ.app X.base X.α + ιΦ.app X.base d =
        ιΦ.app X.base (Φ'.pb φ.base Y.α) + divB.app X.base φ.u := by
      have h := φ.rel
      rw [← hdφ] at h
      rw [ιΦ.natural]
      exact h
    have hu : divB.app X.base φ.u =
        ιΦ.app _ ((φ.deg : ℕ) • X.α + d - Φ'.pb φ.base Y.α) := by
      rw [map_sub, map_add, map_nsmul, hrel]
      abel
    obtain ⟨u', hu'⟩ := hfib _ _ _ hu
    refine ⟨{ deg := φ.deg, base := φ.base, div := d, div_mem := hd, u := u', rel := ?_ }, ?_⟩
    · apply hιΦ
      rw [map_add, map_nsmul, map_add, ← hdiv, hu', hrel]
    · ext
      · rfl
      · rfl
      · exact hdφ
      · exact hu'

/-- **[EtTh], Remark 3.6.3**: `C^bs-fld → C` is isomorphism-full — every isomorphism between
objects of the hull comes from an isomorphism of the hull. -/
theorem hullFunctor_preimage_iso (hιΦ : ∀ A, Function.Injective (ιΦ.app A))
    (hfib : ∀ A (b : B.obj A) (y : Φ'.obj A), divB.app A b = ιΦ.app A y →
      ∃ b' : B'.obj A, ιB.app A b' = b) {X Y : Model Φ' B' divB'}
    (φ : hullObj ιΦ X ⟶ hullObj (divB := divB) ιΦ Y) [IsIso φ] :
    ∃ φ' : X ⟶ Y, IsIso φ' ∧ (hullFunctor ιΦ ιB hpos hdiv).map φ' = φ := by
  obtain ⟨φ', hφ'⟩ := (exists_hullFunctor_map_iff ιΦ ιB hpos hdiv hιΦ hfib φ).2
    (isBsFld_of_isIso ιΦ φ)
  refine ⟨φ', ?_, hφ'⟩
  obtain ⟨h1, h2, h3⟩ := (isIso_iff φ).1 inferInstance
  rw [isIso_iff]
  have h3' : ((hullFunctor ιΦ ιB hpos hdiv).map φ').div = 0 := by rw [hφ']; exact h3
  refine ⟨by rw [← h1, ← hφ']; rfl, by rw [← hφ'] at h2; exact h2,
    hιΦ _ (h3'.trans (map_zero _).symm)⟩

end Hull

end Model

end Frobenioid

end Iut
