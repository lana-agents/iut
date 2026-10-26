/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Thm34iv

/-!
# [FrdI], Theorem 3.4 for model Frobenioids over bases of FSM-type (tempered bases)

`Iut/Frobenioid/Thm34.lean` proves [FrdI], Theorem 3.4(ii), (iii) for model Frobenioids over
base categories of FSM-type **and of Aut-type** (`BaseHyp`). The base category
`B^temp(Π)⁰ = OrbitObj Π` of a tempered Frobenioid ([EtTh], Definition 3.6) is of FSM-type
(`OrbitObj.isIso_of_isFSM`), but in general **not** of Aut-type: if `g⁻¹ H g ⊊ H` for an open
subgroup `H` (possible as soon as an open subgroup of `Π` has a free discrete quotient of rank
`≥ 2`), then `x H ↦ x g H` is a non-invertible endomorphism of `Π/H`. [FrdI], Theorem 3.4 only
asks for bases of FSMFF-type and divisor monoids that are *non-dilating* ("standard type",
[FrdI], Definition 3.1(i)(d), (e)); [EtTh], Proposition 5.1 records that the tempered Frobenioids
of [EtTh] §5 have non-dilating divisor monoids.

This file proves Theorem 3.4(ii)–(v) for model Frobenioids `Model Φ B divB` over bases of
FSM-type, without Aut-type, under the hypotheses

* `IsFSMType D` (every FSM-morphism of `D` is an isomorphism),
* `Φ.NonDilating` ([FrdI], Definition 1.1(i), (ii)),
* `Φ.NowhereGroupLike` (every `Φ(A)` is nonzero; for tempered Frobenioids `Φ(A)` contains the
  cusps),
* `HasAllTorsion B` (as in `Thm34.lean`).

## Category-theoretic characterizations (new)

* `Model.isIsometric_iff_midAdj`: **isometries are the morphisms mid-adjoint to the pre-steps**
  (no hypotheses). This replaces the characterization through Frobenius type and pull-backs.
* `Model.isBaseIso_of_isFrobEndo`: an endomorphism `φ` which is irreducible, isometric and
  satisfies the condition `VCond` below is a base-isomorphism. `VCond` is the condition of
  [FrdI], Proposition 1.14(v) ("for every step `α : A → B` there are an isometry `ψ` and a step `β`
  with `ψ ∘ α = β ∘ α ∘ φ`", with "non-pre-step irreducible" replaced by "isometric"); the proof is
  that of Proposition 1.14(v): a pull-back endomorphism would satisfy `φ^*(x) ≤ x` for all
  `x ∈ Φ(A)`, hence (non-dilating) `φ^* = id`, which forces `β` to be isometric.
* `Model.isFrobEndo_zfrob`: the canonical prime-Frobenius endomorphisms of `(A, 0)` satisfy these
  conditions.
* `Model.isFrobeniusType_iff_frobSq`: **morphisms of Frobenius type are the isometries `φ` that sit
  in two commutative squares** `φ_E ≫ σ' = σ ≫ φ`, `φ_E ≫ τ' = τ ≫ ψ` with pre-steps
  `σ, σ', τ, τ'` and `ψ` a finite composite of such endomorphisms (`FrobSq`).
* `Model.isBaseIso_iff_compOf_frob`: base-isomorphisms are (Frobenius type) ≫ (pre-step)
  ([FrdI], Proposition 1.7(ii)).

The remaining characterizations (pull-backs, linear morphisms) are those of `ModelTypes.lean`.

## Results

* `Model.typeCorresp_fsm`: every equivalence matches all morphism types (Theorem 3.4(ii), (iii));
* `Model.thm34_fsm_preservesFrobeniusStructure`: Theorem 3.4(iii);
* `Model.thm34_fsm_preservesBase`: Theorem 3.4(v) (slim `D₂`);
* `Model.mem_ounits_iff_fsm`, `Model.degFr_map_eq_fsm`: Theorem 3.4(iv).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

/-! ### Hypotheses -/

/-- **Categories of FSM-type** ([FrdI] §0, p. 17): every FSM-morphism is an isomorphism. -/
def IsFSMType (D : Type u) [Category.{v} D] : Prop :=
  ∀ ⦃A B : D⦄ (f : A ⟶ B), IsFSM f → IsIso f

lemma BaseHyp.isFSMType {D : Type u} [Category.{v} D] (h : BaseHyp D) : IsFSMType D := h.fsm

namespace DivMonoid

variable {D : Type u} [Category.{v} D] (Φ : DivMonoid.{w} D)

/-- **Non-dilating divisor monoids** ([FrdI], Definition 1.1(i), (ii)): an endomorphism `f` of an
object of `D` such that `f^*(a) ≼ a` for every primary `a ∈ Φ(A)` acts as the identity on
`Φ(A)` (for the sharp monoid `Φ(A)`, `Φ(A)^char = Φ(A)`). -/
def NonDilating : Prop :=
  ∀ (A : D) (f : A ⟶ A), (∀ a : Φ.obj A, Φ.IsPrimary a → Φ.preceq (Φ.pb f a) a) →
    ∀ x ∈ Φ.pos A, Φ.pb f x = x

/-- **No `Φ(A)` is trivial** (no object of `D` is group-like). -/
def NowhereGroupLike : Prop := ∀ A : D, ∃ x ∈ Φ.pos A, x ≠ 0

end DivMonoid

/-! ### The new category-theoretic classes -/

section Classes

variable {C : Type u} [Category.{v} C]

/-- **The condition of [FrdI], Proposition 1.14(v)** for an endomorphism `φ` of `A`, relative to
classes `S` (pre-steps) and `I` (isometries): there is a step out of `A` (`A` is not group-like),
and for every step `α : A → B` there are `ψ ∈ I` and a step `β` with `α ≫ ψ = φ ≫ α ≫ β`. -/
def VCond (S I : MorClass C) {A : C} (φ : A ⟶ A) : Prop :=
  (∃ (B : C) (α : A ⟶ B), S α ∧ ¬ IsIso α) ∧
    ∀ ⦃B : C⦄ (α : A ⟶ B), S α → ¬ IsIso α →
      ∃ (B' : C) (ψ : B ⟶ B') (β : B ⟶ B'), I ψ ∧ S β ∧ ¬ IsIso β ∧ α ≫ ψ = φ ≫ α ≫ β

/-- Irreducible endomorphisms in `I` satisfying `VCond` (in a model Frobenioid: prime-Frobenius
endomorphisms). -/
def IsFrobEndo (S I : MorClass C) {A : C} (φ : A ⟶ A) : Prop :=
  IsIrreducible φ ∧ I φ ∧ VCond S I φ

/-- Finite composites of endomorphisms satisfying `K`. -/
inductive EndChain (K : ∀ {A : C}, (A ⟶ A) → Prop) : ∀ {A : C}, (A ⟶ A) → Prop
  | id (A : C) : EndChain K (𝟙 A)
  | comp {A : C} (a b : A ⟶ A) : K a → EndChain K b → EndChain K (a ≫ b)

/-- **The class `FrobSq S I`**: morphisms `φ : X → X'` in `I` sitting in commutative squares
`φ_E ≫ σ' = σ ≫ φ`, `φ_E ≫ τ' = τ ≫ ψ` with `σ, σ', τ, τ' ∈ S` and `ψ` a finite composite of
endomorphisms `IsFrobEndo S I`. -/
def FrobSq (S I : MorClass C) : MorClass C := fun X X' φ =>
  I φ ∧ ∃ (E E' A : C) (φE : E ⟶ E') (σ : E ⟶ X) (σ' : E' ⟶ X') (τ : E ⟶ A) (τ' : E' ⟶ A)
    (ψ : A ⟶ A), S σ ∧ S σ' ∧ S τ ∧ S τ' ∧ EndChain (fun e => IsFrobEndo S I e) ψ ∧
      φE ≫ σ' = σ ≫ φ ∧ φE ≫ τ' = τ ≫ ψ

lemma VCond.conj {S I : MorClass C} (hS : RespIso S) {A A₂ : C} {φ : A ⟶ A} (h : VCond S I φ)
    (e : A ≅ A₂) : VCond S I (e.inv ≫ φ ≫ e.hom) := by
  obtain ⟨⟨B, α, hα, hni⟩, h₂⟩ := h
  refine ⟨⟨B, e.inv ≫ α, hS.left e.symm α hα, fun hi => hni ?_⟩, fun B α₂ hα₂ hni₂ => ?_⟩
  · haveI := hi
    have : α = e.hom ≫ (e.inv ≫ α) := by simp
    rw [this]; infer_instance
  · obtain ⟨B', ψ, β, hψ, hβ, hnβ, heq⟩ := h₂ (e.hom ≫ α₂) (hS.left e α₂ hα₂) (fun hi => hni₂ (by
      haveI := hi
      have : α₂ = e.inv ≫ (e.hom ≫ α₂) := by simp
      rw [this]; infer_instance))
    refine ⟨B', ψ, β, hψ, hβ, hnβ, ?_⟩
    have := congrArg (fun t => e.inv ≫ t) heq
    simpa using this

lemma IsFrobEndo.conj {S I : MorClass C} (hS : RespIso S) (hI : RespIso I) {A A₂ : C}
    {φ : A ⟶ A} (h : IsFrobEndo S I φ) (e : A ≅ A₂) : IsFrobEndo S I (e.inv ≫ φ ≫ e.hom) :=
  ⟨isIrreducible_respIso.left e.symm _ (isIrreducible_respIso.right φ e h.1),
    hI.left e.symm _ (hI.right φ e h.2.1), h.2.2.conj hS e⟩

end Classes

/-! ### Transport of the new classes by an equivalence -/

section Transport

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
variable (F : C₁ ⥤ C₂) [F.IsEquivalence]
variable {S I : MorClass C₁} {S' I' : MorClass C₂}

lemma corresp_vcond (hS : Corresp F S S') (hI : Corresp F I I') (hS' : RespIso S')
    (hI' : RespIso I') {A : C₁} (φ : A ⟶ A) : VCond S I φ ↔ VCond S' I' (F.map φ) := by
  constructor
  · rintro ⟨⟨B, α, hα, hni⟩, h₂⟩
    refine ⟨⟨F.obj B, F.map α, (hS α).1 hα, fun hi => hni ((corresp_isIso F α).2 hi)⟩,
      fun B₂ α₂ hα₂ hni₂ => ?_⟩
    let eB := F.objObjPreimageIso B₂
    have hFα : F.map (preimageR F α₂) = α₂ ≫ eB.inv := map_preimageR F α₂
    have hα : S (preimageR F α₂) := by rw [hS, hFα]; exact hS'.right α₂ eB.symm hα₂
    have hniα : ¬ IsIso (preimageR F α₂) := fun hi => hni₂ (by
      have := (corresp_isIso F _).1 hi
      rw [hFα] at this
      exact (isIso_respIso.right_iff α₂ eB.symm).1 this)
    obtain ⟨B', ψ, β, hψ, hβ, hnβ, heq⟩ := h₂ _ hα hniα
    refine ⟨F.obj B', eB.inv ≫ F.map ψ, eB.inv ≫ F.map β, hI'.left eB.symm _ ((hI ψ).1 hψ),
      hS'.left eB.symm _ ((hS β).1 hβ), fun hi => hnβ ((corresp_isIso F β).2 ?_), ?_⟩
    · haveI := hi
      have : F.map β = eB.hom ≫ (eB.inv ≫ F.map β) := by simp
      rw [this]; infer_instance
    · have := congrArg F.map heq
      simpa only [F.map_comp, hFα, Category.assoc] using this
  · rintro ⟨⟨B₂, α₂, hα₂, hni₂⟩, h₂⟩
    let eB := F.objObjPreimageIso B₂
    have hFα : F.map (preimageR F α₂) = α₂ ≫ eB.inv := map_preimageR F α₂
    refine ⟨⟨_, preimageR F α₂, by rw [hS, hFα]; exact hS'.right α₂ eB.symm hα₂,
      fun hi => hni₂ ?_⟩, fun B α hα hni => ?_⟩
    · have := (corresp_isIso F _).1 hi
      rw [hFα] at this
      exact (isIso_respIso.right_iff α₂ eB.symm).1 this
    · obtain ⟨B₂', ψ₂, β₂, hψ₂, hβ₂, hnβ₂, heq⟩ := h₂ (F.map α) ((hS α).1 hα)
        (fun hi => hni ((corresp_isIso F α).2 hi))
      let eB' := F.objObjPreimageIso B₂'
      refine ⟨F.objPreimage B₂', F.preimage (ψ₂ ≫ eB'.inv), F.preimage (β₂ ≫ eB'.inv),
        ?_, ?_, ?_, F.map_injective ?_⟩
      · rw [hI, F.map_preimage]; exact hI'.right ψ₂ eB'.symm hψ₂
      · rw [hS, F.map_preimage]; exact hS'.right β₂ eB'.symm hβ₂
      · intro hi
        have := (corresp_isIso F _).1 hi
        rw [F.map_preimage] at this
        exact hnβ₂ ((isIso_respIso.right_iff β₂ eB'.symm).1 this)
      · simp only [F.map_comp, F.map_preimage]
        rw [← Category.assoc, heq]
        simp

lemma corresp_isFrobEndo (hS : Corresp F S S') (hI : Corresp F I I') (hS' : RespIso S')
    (hI' : RespIso I') {A : C₁} (φ : A ⟶ A) :
    IsFrobEndo S I φ ↔ IsFrobEndo S' I' (F.map φ) :=
  and_congr (corresp_isIrreducible F φ) (and_congr (hI φ) (corresp_vcond F hS hI hS' hI' φ))

lemma endChain_map (hS : Corresp F S S') (hI : Corresp F I I') (hS' : RespIso S')
    (hI' : RespIso I') {A : C₁} {ψ : A ⟶ A} (h : EndChain (fun e => IsFrobEndo S I e) ψ) :
    EndChain (fun e => IsFrobEndo S' I' e) (F.map ψ) := by
  induction h with
  | id => rw [F.map_id]; exact EndChain.id _
  | comp a b ha _ ih =>
    rw [F.map_comp]
    exact EndChain.comp _ _ ((corresp_isFrobEndo F hS hI hS' hI' a).1 ha) ih

lemma endChain_preimage (hS : Corresp F S S') (hI : Corresp F I I') (hS' : RespIso S')
    (hI' : RespIso I') {A₂ : C₂} {ψ₂ : A₂ ⟶ A₂}
    (h : EndChain (fun e => IsFrobEndo S' I' e) ψ₂) (A : C₁) (e : F.obj A ≅ A₂) :
    EndChain (fun e => IsFrobEndo S I e) (F.preimage (e.hom ≫ ψ₂ ≫ e.inv)) := by
  induction h generalizing A with
  | id =>
    have : F.preimage (e.hom ≫ 𝟙 _ ≫ e.inv) = 𝟙 A := F.map_injective (by simp)
    rw [this]; exact EndChain.id _
  | comp a b ha _ ih =>
    have : F.preimage (e.hom ≫ (a ≫ b) ≫ e.inv) =
        F.preimage (e.hom ≫ a ≫ e.inv) ≫ F.preimage (e.hom ≫ b ≫ e.inv) :=
      F.map_injective (by simp)
    rw [this]
    refine EndChain.comp _ _ ?_ (ih A e)
    rw [corresp_isFrobEndo F hS hI hS' hI', F.map_preimage]
    simpa using ha.conj hS' hI' e.symm

lemma corresp_frobSq (hS : Corresp F S S') (hI : Corresp F I I') (hS' : RespIso S')
    (hI' : RespIso I') : Corresp F (FrobSq S I) (FrobSq S' I') := by
  intro X X' φ
  constructor
  · rintro ⟨hφ, E, E', A, φE, σ, σ', τ, τ', ψ, hσ, hσ', hτ, hτ', hψ, h₁, h₂⟩
    exact ⟨(hI φ).1 hφ, F.obj E, F.obj E', F.obj A, F.map φE, F.map σ, F.map σ', F.map τ,
      F.map τ', F.map ψ, (hS σ).1 hσ, (hS σ').1 hσ', (hS τ).1 hτ, (hS τ').1 hτ',
      endChain_map F hS hI hS' hI' hψ, by rw [← F.map_comp, h₁, F.map_comp],
      by rw [← F.map_comp, h₂, F.map_comp]⟩
  · rintro ⟨hφ, E₂, E₂', A₂, φE, σ, σ', τ, τ', ψ, hσ, hσ', hτ, hτ', hψ, h₁, h₂⟩
    let eE := F.objObjPreimageIso E₂
    let eE' := F.objObjPreimageIso E₂'
    let eA := F.objObjPreimageIso A₂
    refine ⟨(hI φ).2 hφ, F.objPreimage E₂, F.objPreimage E₂', F.objPreimage A₂,
      F.preimage (eE.hom ≫ φE ≫ eE'.inv), F.preimage (eE.hom ≫ σ),
      F.preimage (eE'.hom ≫ σ'), F.preimage (eE.hom ≫ τ ≫ eA.inv),
      F.preimage (eE'.hom ≫ τ' ≫ eA.inv), F.preimage (eA.hom ≫ ψ ≫ eA.inv), ?_, ?_, ?_, ?_,
      endChain_preimage F hS hI hS' hI' hψ _ eA, F.map_injective ?_, F.map_injective ?_⟩
    · rw [hS, F.map_preimage]; exact hS'.left eE σ hσ
    · rw [hS, F.map_preimage]; exact hS'.left eE' σ' hσ'
    · rw [hS, F.map_preimage]; exact hS'.left eE _ (hS'.right τ eA.symm hτ)
    · rw [hS, F.map_preimage]; exact hS'.left eE' _ (hS'.right τ' eA.symm hτ')
    · simp only [F.map_comp, F.map_preimage, Category.assoc, Iso.inv_hom_id_assoc]
      rw [h₁]
    · simp only [F.map_comp, F.map_preimage, Category.assoc, Iso.inv_hom_id_assoc,
        reassoc_of% h₂]

end Transport

namespace Model

/-! ### Characterizations in a model Frobenioid -/

section Characterizations

variable {D : Type u} [Category.{v} D] [TotallyEpimorphic D]
variable {Φ : DivMonoid.{w} D} {B : GrpOn.{w} D} {divB : DivHom B Φ.toGrpOn}

local notation "𝐏" => toElem Φ B divB

/-- The class of pre-steps. -/
abbrev preStepC : MorClass (Model Φ B divB) := fun _ _ φ => IsPreStep 𝐏 φ

/-- The class of isometries. -/
abbrev isometricC : MorClass (Model Φ B divB) := fun _ _ φ => IsIsometric 𝐏 φ

omit [TotallyEpimorphic D] in
/-- **Pre-steps are the FSM-morphisms** over a base of FSM-type (`isPreStep_iff_isFSM` without
Aut-type). -/
theorem isPreStep_iff_isFSM_of_fsm (hD : IsFSMType D) (hB : HasAllTorsion B)
    {X Y : Model Φ B divB} (φ : X ⟶ Y) : IsPreStep 𝐏 φ ↔ IsFSM φ := by
  refine ⟨isFSM_of_isPreStep φ, fun ⟨hm, hf⟩ => ?_⟩
  haveI := hm
  have d := deg_eq_one_of_mono hB φ
  exact ⟨d, hD _ ⟨mono_base_of_mono φ d, isFiberwiseSurjective_base φ hf⟩⟩

omit [TotallyEpimorphic D] in
/-- **Isometries are the morphisms mid-adjoint to the pre-steps.** -/
theorem isIsometric_iff_midAdj {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsIsometric 𝐏 φ ↔ MidAdj (fun _ _ ψ => IsPreStep 𝐏 ψ) φ := by
  constructor
  · intro h V W a b c habc hb
    have h0 : φ.div = 0 := h
    have hb1 : b.deg = 1 := hb.1
    haveI : IsIso b.base := hb.2
    rw [← habc, comp_div, comp_div] at h0
    have h₁ := Φ.eq_zero_of_add_eq_zero_left
      (Φ.pb_mem _ ((Φ.pos _).add_mem (Φ.pb_mem _ c.div_mem) ((Φ.pos _).nsmul_mem b.div_mem _)))
      ((Φ.pos _).nsmul_mem a.div_mem _) h0
    have h₂ : Φ.pb b.base c.div + (c.deg : ℕ) • b.div = 0 :=
      Φ.pb_injective a.base (h₁.trans (map_zero _).symm)
    have h₃ : (c.deg : ℕ) • b.div = 0 := Φ.eq_zero_of_add_eq_zero_left
      ((Φ.pos _).nsmul_mem b.div_mem _) (Φ.pb_mem _ c.div_mem) (by rw [add_comm]; exact h₂)
    exact isIso_of b hb1 inferInstance (Φ.eq_zero_of_nsmul_eq_zero c.deg.pos h₃)
  · intro h
    obtain ⟨X', Y', γ, β, α, hγ, hβ, hα, hc⟩ := factorization φ
    haveI := h γ β α hc hβ
    have hβ0 : β.div = 0 := ((isIso_iff β).mp inferInstance).2.2
    have hγ0 : γ.div = 0 := ((isFrobeniusType_iff γ).mp hγ).1
    have hα0 : α.div = 0 := ((isPullback_iff α).mp hα).2
    change φ.div = 0
    rw [← hc]
    simp [hβ0, hγ0, hα0]

omit [TotallyEpimorphic D] in
/-- **Soundness of `IsFrobEndo`**: for a non-dilating `Φ`, an irreducible isometric endomorphism
satisfying `VCond` is a base-isomorphism ([FrdI], Proposition 1.14(v)). -/
theorem isBaseIso_of_isFrobEndo (hΦ : Φ.NonDilating) {A : Model Φ B divB} {φ : A ⟶ A}
    (h : IsFrobEndo preStepC isometricC φ) : IsIso φ.base := by
  obtain ⟨hirr, hI, ⟨⟨B₀, α₀, hα₀, hni₀⟩, hV⟩⟩ := h
  have hφ0 : φ.div = 0 := hI
  -- for every nonzero `x ∈ Φ(A)` and linear `φ`: a step `β` with `x = φ^*(Div β) + φ^* x`
  have key : φ.deg = 1 → ∀ x ∈ Φ.pos A.base, x ≠ 0 → ∃ y ∈ Φ.pos A.base, y ≠ 0 ∧
      x = Φ.pb φ.base y + Φ.pb φ.base x := by
    intro hd x hx hx0
    let α : A ⟶ ⟨A.base, A.α + x⟩ := mk1 (𝟙 _) x hx 0 (by simp)
    have hni : ¬ IsIso α := fun hi => hx0 ((isIso_iff α).mp hi).2.2
    obtain ⟨B', ψ, β, hψ, hβ, hnβ, heq⟩ := hV α (isPreStep_mk1 _ _ _ _ _) hni
    have hβ1 : β.deg = 1 := hβ.1
    have hψ0 : ψ.div = 0 := hψ
    haveI : IsIso β.base := hβ.2
    have hdeg := congrArg Hom.deg heq
    have hdiv := congrArg Hom.div heq
    simp only [comp_deg, comp_div, α, mk1_deg, mk1_base, mk1_div, hβ1, hd, hψ0, hφ0,
      GrpOn.pb_id', map_zero, zero_add, smul_zero, add_zero, mul_one,
      PNat.one_coe, one_smul] at hdeg hdiv
    rw [hdeg, PNat.one_coe, one_smul] at hdiv
    refine ⟨β.div, β.div_mem, fun h0 => hnβ (isIso_of β hβ1 inferInstance h0), ?_⟩
    rw [← map_add]
    convert hdiv using 2
  have hdeg : φ.deg ≠ 1 := by
    intro hd
    have hle : ∀ x ∈ Φ.pos A.base, Φ.le (Φ.pb φ.base x) x := by
      intro x hx
      by_cases hx0 : x = 0
      · subst hx0; rw [map_zero]; exact Φ.le_refl _
      · obtain ⟨y, hy, -, hxy⟩ := key hd x hx hx0
        change x - Φ.pb φ.base x ∈ Φ.pos A.base
        rw [sub_eq_of_eq_add hxy]
        exact Φ.pb_mem _ hy
    have hid := hΦ A.base φ.base (fun a ha => ⟨1, one_pos, by
      rw [one_smul]; exact hle a ha.1⟩)
    have hx0 : α₀.div ≠ 0 := fun h0 =>
      hni₀ (isIso_of α₀ hα₀.1 hα₀.2 h0)
    have hx : Φ.pb (𝟙 _) α₀.div ∈ Φ.pos A.base := by
      rw [GrpOn.pb_id']; exact α₀.div_mem
    obtain ⟨y, hy, hy0, hxy⟩ := key hd α₀.div α₀.div_mem hx0
    rw [hid _ α₀.div_mem, hid _ hy] at hxy
    exact hy0 (by
      have := congrArg (· - α₀.div) hxy
      simpa using this.symm)
  let a : A ⟶ ⟨A.base, (φ.deg : ℕ) • A.α⟩ := mk' φ.deg (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp)
  let b : (⟨A.base, (φ.deg : ℕ) • A.α⟩ : Model Φ B divB) ⟶ A :=
    mk1 φ.base 0 (Φ.pos _).zero_mem φ.u (by simpa [hφ0] using φ.rel)
  have hab : a ≫ b = φ := by ext <;> simp [a, b, hφ0]
  rcases hirr.2 a b hab with ha | hb
  · exact absurd ((isIso_iff a).mp ha).1 hdeg
  · have := ((isIso_iff b).mp hb).2.1
    simpa [b] using this

omit [TotallyEpimorphic D] in
/-- `EndChain` of `IsFrobEndo` endomorphisms are base-isomorphisms. -/
theorem isIso_base_of_endChain (hΦ : Φ.NonDilating) {A : Model Φ B divB} {ψ : A ⟶ A}
    (h : EndChain (fun e => IsFrobEndo preStepC isometricC e) ψ) : IsIso ψ.base := by
  induction h with
  | id => exact inferInstanceAs (IsIso (𝟙 _))
  | comp a b ha _ ih =>
    haveI := isBaseIso_of_isFrobEndo hΦ ha
    haveI := ih
    change IsIso (a.base ≫ b.base)
    infer_instance

variable (Φ B divB) in
/-- The canonical Frobenius endomorphism `(n, id, 0, 0)` of `(A, 0)`. -/
def zfrob (A : D) (n : ℕ+) : zeroObj Φ B divB A ⟶ zeroObj Φ B divB A :=
  mk' n (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp)

omit [TotallyEpimorphic D] in
lemma zfrob_mul (A : D) (m n : ℕ+) : zfrob Φ B divB A (m * n) =
    zfrob Φ B divB A m ≫ zfrob Φ B divB A n := by
  ext <;> simp [zfrob, mul_comm]

omit [TotallyEpimorphic D] in
lemma zfrob_one (A : D) : zfrob Φ B divB A 1 = 𝟙 _ := by
  ext <;> simp [zfrob]

/-- **The prime-Frobenius endomorphisms of `(A, 0)` satisfy `IsFrobEndo`** when `Φ(A) ≠ 0`. -/
theorem isFrobEndo_zfrob (A : D) (hA : ∃ x ∈ Φ.pos A, x ≠ 0) (p : ℕ+) (hp : (p : ℕ).Prime) :
    IsFrobEndo preStepC isometricC (zfrob Φ B divB A p) := by
  have hp1 : (p : ℕ) ≠ 1 := hp.one_lt.ne'
  refine ⟨⟨fun hi => hp1 (by simpa [zfrob] using congrArg PNat.val ((isIso_iff _).mp hi).1),
    fun W a b hab => ?_⟩, rfl, ⟨?_, fun B' α hα hni => ?_⟩⟩
  · -- irreducibility
    have hdeg := congrArg (fun t => ((Hom.deg t : ℕ+) : ℕ)) hab
    have hdiv := congrArg Hom.div hab
    have hbase := congrArg Hom.base hab
    simp only [comp_deg, PNat.mul_coe, zfrob, mk'_deg] at hdeg
    simp only [comp_div, zfrob, mk'_div] at hdiv
    simp only [comp_base, zfrob, mk'_base] at hbase
    have h₁ : Φ.pb a.base b.div = 0 := Φ.eq_zero_of_add_eq_zero_left (Φ.pb_mem _ b.div_mem)
      ((Φ.pos _).nsmul_mem a.div_mem _) hdiv
    have hdiv' : (b.deg : ℕ) • a.div = 0 := by rw [h₁, zero_add] at hdiv; exact hdiv
    have ha0 : a.div = 0 := Φ.eq_zero_of_nsmul_eq_zero b.deg.pos hdiv'
    have hb0 : b.div = 0 := Φ.pb_injective a.base (by rw [h₁, map_zero])
    haveI : IsIso (a.base ≫ b.base) := by rw [hbase]; infer_instance
    haveI := isIso_left_of_isIso_comp a.base b.base
    haveI := isIso_right_of_isIso_comp a.base b.base
    rcases (Nat.dvd_prime hp).mp (Dvd.intro_left _ hdeg) with h | h
    · exact Or.inl (isIso_of a (PNat.coe_eq_one_iff.mp h) inferInstance ha0)
    · have : (b.deg : ℕ) = 1 := by
        rw [h] at hdeg
        exact (Nat.mul_eq_right hp.ne_zero).mp hdeg
      exact Or.inr (isIso_of b (PNat.coe_eq_one_iff.mp this) inferInstance hb0)
  · -- existence of a step out of `(A, 0)`
    obtain ⟨x, hx, hx0⟩ := hA
    exact ⟨⟨A, x⟩, mk1 (𝟙 _) x hx 0 (by simp), isPreStep_mk1 _ _ _ _ _,
      fun hi => hx0 ((isIso_iff _).mp hi).2.2⟩
  · -- the squares
    have hα1 : α.deg = 1 := hα.1
    haveI : IsIso α.base := hα.2
    have hx0 : α.div ≠ 0 := fun h0 => hni (isIso_of α hα1 inferInstance h0)
    have hrel := α.rel
    rw [hα1, PNat.one_coe, one_smul] at hrel
    -- `hrel : 0 + α.div = α.base^* B'.α + Div_B(u_α)`
    let m : ℕ := (p : ℕ) - 1
    have hm : (p : ℕ) = m + 1 := (Nat.succ_pred_eq_of_pos p.pos).symm
    let y : Φ.obj B'.base := Φ.pb (inv α.base) (m • α.div)
    have hy : y ∈ Φ.pos B'.base := Φ.pb_mem _ ((Φ.pos _).nsmul_mem α.div_mem _)
    let uβ : B.obj B'.base := m • B.pb (inv α.base) α.u
    let Bp : Model Φ B divB := ⟨B'.base, (p : ℕ) • B'.α⟩
    let ψ : B' ⟶ Bp := mk' p (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp [Bp])
    let β : B' ⟶ Bp := mk1 (𝟙 _) y hy uβ (by
      apply Φ.pb_injective α.base
      simp only [Bp, y, uβ, map_add, map_nsmul, GrpOn.pb_id', GrpOn.pb_pb_inv, divB.natural]
      rw [hm]
      simp only [zeroObj, zero_add] at hrel
      rw [hrel]
      simp only [add_smul, one_smul, smul_add]
      abel)
    refine ⟨Bp, ψ, β, rfl, isPreStep_mk1 _ _ _ _ _, fun hi => ?_, ?_⟩
    · have hy0 : y = 0 := ((isIso_iff β).mp hi).2.2
      have : m • α.div = 0 := by
        have := congrArg (Φ.pb α.base) hy0
        simpa [y] using this
      have hm0 : 0 < m := by have := hp.two_le; omega
      exact hx0 (Φ.eq_zero_of_nsmul_eq_zero hm0 this)
    · ext
      · simp [ψ, β, zfrob, hα1]
      · simp [ψ, β, zfrob]
      · simp only [comp_div, ψ, β, zfrob, mk'_div, mk'_base, mk1_div, mk1_deg,
          mk'_deg, y, GrpOn.pb_id', GrpOn.pb_pb_inv, map_zero, smul_zero, add_zero,
          zero_add, PNat.one_coe, one_smul]
        rw [hm, add_smul, one_smul]
      · simp only [comp_u, ψ, β, zfrob, mk'_u, mk'_base, mk1_u, mk1_deg,
          mk'_deg, uβ, GrpOn.pb_id', map_nsmul, GrpOn.pb_pb_inv, map_zero, smul_zero,
          add_zero, zero_add, PNat.one_coe, one_smul]
        rw [hm, add_smul, one_smul]

/-- **All canonical Frobenius endomorphisms of `(A, 0)` are finite composites of
prime-Frobenius ones.** -/
theorem endChain_zfrob (A : D) (hA : ∃ x ∈ Φ.pos A, x ≠ 0) (n : ℕ+) :
    EndChain (fun e => IsFrobEndo preStepC isometricC e) (zfrob Φ B divB A n) := by
  suffices h : ∀ k : ℕ, ∀ m : ℕ+, (m : ℕ) = k →
      EndChain (fun e => IsFrobEndo preStepC isometricC e) (zfrob Φ B divB A m) from
    h n n rfl
  intro k
  induction k using induction_on_primes with
  | zero => intro m hm; exact absurd hm m.ne_zero
  | one => intro m hm; rw [PNat.coe_eq_one_iff.mp hm, zfrob_one]; exact EndChain.id _
  | prime_mul p a hp ih =>
    intro m hm
    have ha : 0 < a := Nat.pos_of_mul_pos_left (hm ▸ m.pos)
    have e : m = ⟨p, hp.pos⟩ * ⟨a, ha⟩ := PNat.eq (by simp [hm])
    rw [e, zfrob_mul]
    exact EndChain.comp _ _ (isFrobEndo_zfrob A hA ⟨p, hp.pos⟩ hp) (ih ⟨a, ha⟩ rfl)

omit [TotallyEpimorphic D] in
/-- **Base-isomorphisms are the composites (Frobenius type) ≫ (pre-step)** ([FrdI],
Proposition 1.7(ii)). -/
theorem isBaseIso_iff_compOf_frob {X Y : Model Φ B divB} (φ : X ⟶ Y) :
    IsBaseIso 𝐏 φ ↔
      CompOf (fun _ _ ψ => IsFrobeniusType 𝐏 ψ) (fun _ _ ψ => IsPreStep 𝐏 ψ) φ := by
  constructor
  · intro h
    haveI : IsIso φ.base := h
    refine ⟨⟨X.base, (φ.deg : ℕ) • X.α⟩, mk' φ.deg (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp),
      mk1 φ.base φ.div φ.div_mem φ.u (by simpa using φ.rel),
      (isFrobeniusType_iff _).mpr ⟨rfl, by simp only [mk'_base]; infer_instance⟩,
      isPreStep_mk1 _ _ _ _ _, ?_⟩
    ext <;> simp
  · rintro ⟨W, a, b, ha, hb, rfl⟩
    haveI : IsIso a.base := ha.2
    haveI : IsIso b.base := hb.2
    change IsIso (a ≫ b).base
    rw [comp_base]
    infer_instance

/-- **Morphisms of Frobenius type are the `FrobSq` morphisms** (for non-dilating `Φ` with all
`Φ(A) ≠ 0`). -/
theorem isFrobeniusType_iff_frobSq (hΦ : Φ.NonDilating) (hG : Φ.NowhereGroupLike)
    {X X' : Model Φ B divB} (φ : X ⟶ X') :
    IsFrobeniusType 𝐏 φ ↔ FrobSq preStepC isometricC φ := by
  constructor
  · intro h
    obtain ⟨h0, hb⟩ := (isFrobeniusType_iff φ).mp h
    haveI := hb
    obtain ⟨p, hp, q, hq, he⟩ := Φ.generating X.α
    let E : Model Φ B divB := ⟨X.base, -q⟩
    let E' : Model Φ B divB := ⟨X.base, (φ.deg : ℕ) • (-q)⟩
    let φE : E ⟶ E' := mk' φ.deg (𝟙 _) 0 (Φ.pos _).zero_mem 0 (by simp [E, E'])
    let σ : E ⟶ X := mk1 (𝟙 _) p hp 0 (by simp [E, he]; abel)
    let σ' : E' ⟶ X' := mk1 φ.base ((φ.deg : ℕ) • p) ((Φ.pos _).nsmul_mem hp _) φ.u (by
      have r := φ.rel
      rw [h0, add_zero, he] at r
      simp only [E']
      rw [← r, smul_sub, smul_neg]
      abel)
    let τ : E ⟶ zeroObj Φ B divB X.base := mk1 (𝟙 _) q hq 0 (by simp [E])
    let τ' : E' ⟶ zeroObj Φ B divB X.base :=
      mk1 (𝟙 _) ((φ.deg : ℕ) • q) ((Φ.pos _).nsmul_mem hq _) 0 (by simp [E'])
    refine ⟨h0, E, E', _, φE, σ, σ', τ, τ', zfrob Φ B divB X.base φ.deg,
      isPreStep_mk1 _ _ _ _ _, isPreStep_mk1 _ _ _ _ _, isPreStep_mk1 _ _ _ _ _,
      isPreStep_mk1 _ _ _ _ _, endChain_zfrob _ (hG _) _, ?_, ?_⟩
    · ext <;> simp [φE, σ', σ, h0]
    · ext <;> simp [φE, τ', τ, zfrob]
  · rintro ⟨hI, E, E', A, φE, σ, σ', τ, τ', ψ, hσ, hσ', hτ, hτ', hψ, h₁, h₂⟩
    haveI := isIso_base_of_endChain hΦ hψ
    haveI : IsIso σ.base := hσ.2
    haveI : IsIso σ'.base := hσ'.2
    haveI : IsIso τ.base := hτ.2
    haveI : IsIso τ'.base := hτ'.2
    have b₁ := congrArg Hom.base h₁
    have b₂ := congrArg Hom.base h₂
    simp only [comp_base] at b₁ b₂
    haveI : IsIso φE.base := by
      have : φE.base = (τ.base ≫ ψ.base) ≫ inv τ'.base := by
        rw [← b₂, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [this]; infer_instance
    refine (isFrobeniusType_iff φ).mpr ⟨hI, ?_⟩
    have : φ.base = inv σ.base ≫ φE.base ≫ σ'.base := by
      rw [b₁, IsIso.inv_hom_id_assoc]
    rw [this]; infer_instance

end Characterizations

/-! ### The theorem -/

section Main

variable {D₁ : Type u₁} [Category.{v₁} D₁] [TotallyEpimorphic D₁]
variable {Φ₁ : DivMonoid.{w₁} D₁} {B₁ : GrpOn.{w₁} D₁} {divB₁ : DivHom B₁ Φ₁.toGrpOn}
variable {D₂ : Type u₂} [Category.{v₂} D₂] [TotallyEpimorphic D₂]
variable {Φ₂ : DivMonoid.{w₂} D₂} {B₂ : GrpOn.{w₂} D₂} {divB₂ : DivHom B₂ Φ₂.toGrpOn}

local notation "𝐏₁" => toElem Φ₁ B₁ divB₁
local notation "𝐏₂" => toElem Φ₂ B₂ divB₂

/-- **[FrdI], Theorem 3.4(ii), (iii) (types)** for model Frobenioids over bases of FSM-type (not
necessarily of Aut-type) with non-dilating, nowhere group-like divisor monoids and rational
functions with torsion of every order: an equivalence matches pre-steps, base-isomorphisms,
pull-backs, linear morphisms, morphisms of Frobenius type and isometries. -/
theorem typeCorresp_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁) (hΦ₁ : Φ₁.NonDilating)
    (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂) (hB₂ : HasAllTorsion B₂)
    (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] : TypeCorresp F := by
  have cPre : Corresp F (fun _ _ φ => IsPreStep 𝐏₁ φ) (fun _ _ φ => IsPreStep 𝐏₂ φ) :=
    (corresp_isFSM F).of_iff (fun _ _ φ => isPreStep_iff_isFSM_of_fsm hD₁ hB₁ φ)
      (fun _ _ φ => isPreStep_iff_isFSM_of_fsm hD₂ hB₂ φ)
  have cIsom : Corresp F (fun _ _ φ => IsIsometric 𝐏₁ φ) (fun _ _ φ => IsIsometric 𝐏₂ φ) :=
    (cPre.midAdj (isPreStep_respIso _)).of_iff (fun _ _ φ => isIsometric_iff_midAdj φ)
      (fun _ _ φ => isIsometric_iff_midAdj φ)
  have cFr : Corresp F (fun _ _ φ => IsFrobeniusType 𝐏₁ φ)
      (fun _ _ φ => IsFrobeniusType 𝐏₂ φ) :=
    (corresp_frobSq F cPre cIsom (isPreStep_respIso _) (isIsometric_respIso _)).of_iff
      (fun _ _ φ => isFrobeniusType_iff_frobSq hΦ₁ hG₁ φ)
      (fun _ _ φ => isFrobeniusType_iff_frobSq hΦ₂ hG₂ φ)
  have cBase : Corresp F (fun _ _ φ => IsBaseIso 𝐏₁ φ) (fun _ _ φ => IsBaseIso 𝐏₂ φ) :=
    (cFr.compOf cPre isFrobeniusType_respIso (isPreStep_respIso _)).of_iff
      (fun _ _ φ => isBaseIso_iff_compOf_frob φ) (fun _ _ φ => isBaseIso_iff_compOf_frob φ)
  have cPb : Corresp F (fun _ _ φ => IsPullback 𝐏₁ φ) (fun _ _ φ => IsPullback 𝐏₂ φ) :=
    (cBase.minAdj (isBaseIso_respIso _)).of_iff (fun _ _ φ => isPullback_iff_minAdj φ)
      (fun _ _ φ => isPullback_iff_minAdj φ)
  have cLin : Corresp F (fun _ _ φ => IsLinear 𝐏₁ φ) (fun _ _ φ => IsLinear 𝐏₂ φ) :=
    (cPre.compOf cPb (isPreStep_respIso _) isPullback_respIso).of_iff
      (fun _ _ φ => isLinear_iff_compOf φ) (fun _ _ φ => isLinear_iff_compOf φ)
  exact ⟨cPre, cBase, cPb, cLin, cFr, cIsom⟩

variable [IsConnected D₁] [IsConnected D₂]

/-- **[FrdI], Theorem 3.4(iii)** for model Frobenioids over bases of FSM-type (e.g. the tempered
bases `B^temp(Π)⁰`): every equivalence of categories preserves the Frobenius structure. -/
theorem thm34_fsm_preservesFrobeniusStructure (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesFrobeniusStructure 𝐏₁ 𝐏₂ F := by
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have c' := typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv
  obtain ⟨e, he⟩ := exists_degEquiv F (fun _ _ φ h => (c.linear φ).1 h)
    (fun _ _ φ h => (c'.linear φ).1 h)
  have cCoa : ∀ {A B : Model Φ₁ B₁ divB₁} (φ : A ⟶ B),
      IsCoangular 𝐏₁ φ ↔ IsCoangular 𝐏₂ (F.map φ) :=
    fun φ => ⟨fun _ => isCoangular _, fun _ => isCoangular _⟩
  refine ⟨fun φ => c.frobType φ, fun φ => c.linear φ, fun φ => c.baseIso φ, cCoa,
    fun φ => c.pullback φ, fun φ => c.isometric φ, fun φ => and_congr (cCoa φ) (c.isometric φ),
    e, fun φ => he φ⟩

omit [IsConnected D₁] [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(v)** over bases of FSM-type with `D₂` slim: every equivalence lies
over a functor of base categories. -/
theorem thm34_fsm_preservesBase (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hD : IsSlim D₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] :
    PreservesBase 𝐏₁ 𝐏₂ F :=
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  preservesBase_of F (fun _ _ ψ h => (c.baseIso ψ).1 h)
    (fun _ _ φ φ' h => base_map_eq_of_base_eq F c.pullback c.baseIso φ φ' h hD)

omit [IsConnected D₁] [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(iv)** over bases of FSM-type, both slim: `F` restricts to bijections
`O^▷(A) ≅ O^▷(F A)`. -/
theorem mem_orhd_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
    [F.IsEquivalence] {X : Model Φ₁ B₁ divB₁} (e : X ⟶ X) :
    e ∈ Orhd 𝐏₁ X ↔ F.map e ∈ Orhd 𝐏₂ (F.obj X) := by
  have c := typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F
  have c' := typeCorresp_fsm hD₂ hB₂ hΦ₂ hG₂ hD₁ hB₁ hΦ₁ hG₁ F.inv
  refine ⟨fun he => ⟨base_map_eq_id F c.pullback c.baseIso hS₂ e he.1, (c.linear e).1 he.2⟩,
    fun h => ?_⟩
  have h1 : (F.inv.map (F.map e)).base = 𝟙 _ :=
    base_map_eq_id F.inv c'.pullback c'.baseIso hS₁ _ h.1
  have hn := (F.asEquivalence.unitIso.hom.naturality e)
  simp only [Functor.id_map, Functor.comp_map] at hn
  have hb := congrArg Hom.base hn
  simp only [comp_base] at hb
  change _ = _ ≫ (F.inv.map (F.map e)).base at hb
  rw [h1, Category.comp_id] at hb
  haveI : IsIso (F.asEquivalence.unitIso.hom.app X).base :=
    isIso_base_of_isIso (F.asEquivalence.unitIso.hom.app X)
  exact ⟨(cancel_mono (F.asEquivalence.unitIso.hom.app X).base).mp
    (hb.trans (Category.id_comp _).symm), (c.linear e).2 h.2⟩

omit [IsConnected D₁] [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(iv)** over bases of FSM-type, both slim: `F` restricts to bijections
`O^×(A) ≅ O^×(F A)`. -/
theorem mem_ounits_iff_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hS₁ : IsSlim D₁) (hS₂ : IsSlim D₂) (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂)
    [F.IsEquivalence] {X : Model Φ₁ B₁ divB₁} (e : X ⟶ X) :
    e ∈ Ounits 𝐏₁ X ↔ F.map e ∈ Ounits 𝐏₂ (F.obj X) := by
  have ho := mem_orhd_iff_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ hS₁ hS₂ F e
  exact ⟨fun ⟨hi, hb, hl⟩ => ⟨(corresp_isIso F e).1 hi, (ho.1 ⟨hb, hl⟩).1, (ho.1 ⟨hb, hl⟩).2⟩,
    fun ⟨hi, hb, hl⟩ => ⟨(corresp_isIso F e).2 hi, (ho.2 ⟨hb, hl⟩).1, (ho.2 ⟨hb, hl⟩).2⟩⟩

omit [IsConnected D₂] in
/-- **[FrdI], Theorem 3.4(iv)** over bases of FSM-type: `Ψ_{ℕ≥1}` is the identity when `C₁` has
a unit of infinite order and `D₂` is slim. -/
theorem degFr_map_eq_fsm (hD₁ : IsFSMType D₁) (hB₁ : HasAllTorsion B₁)
    (hΦ₁ : Φ₁.NonDilating) (hG₁ : Φ₁.NowhereGroupLike) (hD₂ : IsFSMType D₂)
    (hB₂ : HasAllTorsion B₂) (hΦ₂ : Φ₂.NonDilating) (hG₂ : Φ₂.NowhereGroupLike)
    (hD : IsSlim D₂) (hnt : HasNonTorsionUnit divB₁)
    (F : Model Φ₁ B₁ divB₁ ⥤ Model Φ₂ B₂ divB₂) [F.IsEquivalence] {X Y : Model Φ₁ B₁ divB₁}
    (φ : X ⟶ Y) : degFr 𝐏₂ (F.map φ) = degFr 𝐏₁ φ :=
  degFr_map_eq_of_typeCorresp F (typeCorresp_fsm hD₁ hB₁ hΦ₁ hG₁ hD₂ hB₂ hΦ₂ hG₂ F) hD hnt φ

end Main

end Model

end Frobenioid

end Iut
