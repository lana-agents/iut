/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Category-theoretic properties of morphisms and their invariance under equivalences

The proof of [FrdI], Theorem 3.4 characterizes the various types of morphisms of a Frobenioid by
properties that refer only to the category structure ([FrdI] §0, p. 17): FSM-morphisms,
irreducible morphisms, morphisms that are *minimal-adjoint*, *minimal-coadjoint* or *mid-adjoint*
to a class of morphisms, composites of morphisms of given classes. This file records these notions
and proves that they are transported by any equivalence of categories `F : C₁ ⥤ C₂`.

The transport statements are phrased with `Corresp F P Q` (`P φ ↔ Q (F φ)` for every morphism `φ`
of `C₁`). For classes defined by quantifying over factorizations through arbitrary objects, the
class on the target side has to be stable under composition with isomorphisms (`RespIso`).

[FrdI] = S. Mochizuki, *The geometry of Frobenioids I: the general theory*, Kyushu J. Math. 62
(2008).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe v₁ v₂ u₁ u₂

section Notions

variable {C : Type u₁} [Category.{v₁} C]

/-- A class of morphisms of `C` (a predicate on all morphisms). -/
abbrev MorClass (C : Type u₁) [Category.{v₁} C] := ∀ ⦃X Y : C⦄, (X ⟶ Y) → Prop

/-- A class of morphisms is **stable under isomorphisms** on both sides. -/
structure RespIso (P : MorClass C) : Prop where
  left : ∀ ⦃X X' Y : C⦄ (e : X' ≅ X) (φ : X ⟶ Y), P φ → P (e.hom ≫ φ)
  right : ∀ ⦃X Y Y' : C⦄ (φ : X ⟶ Y) (e : Y ≅ Y'), P φ → P (φ ≫ e.hom)

lemma RespIso.left_iff {P : MorClass C} (h : RespIso P) {X X' Y : C} (e : X' ≅ X) (φ : X ⟶ Y) :
    P (e.hom ≫ φ) ↔ P φ :=
  ⟨fun hφ => by simpa using h.left e.symm _ hφ, h.left e φ⟩

lemma RespIso.right_iff {P : MorClass C} (h : RespIso P) {X Y Y' : C} (φ : X ⟶ Y) (e : Y ≅ Y') :
    P (φ ≫ e.hom) ↔ P φ :=
  ⟨fun hφ => by simpa using h.right _ e.symm hφ, h.right φ e⟩

/-- **Irreducible morphisms** ([FrdI] §0, p. 17): non-isomorphisms `φ` such that in every
factorization `φ = a ≫ b` one of `a`, `b` is an isomorphism. -/
def IsIrreducible {X Y : C} (φ : X ⟶ Y) : Prop :=
  ¬ IsIso φ ∧ ∀ ⦃W : C⦄ (a : X ⟶ W) (b : W ⟶ Y), a ≫ b = φ → IsIso a ∨ IsIso b

/-- **Minimal-adjoint to `S`** ([FrdI] §0, p. 17): in every factorization `φ = a ≫ b`
(`φ = b ∘ a`) with `a ∈ S`, `a` is an isomorphism. -/
def MinAdj (S : MorClass C) {X Y : C} (φ : X ⟶ Y) : Prop :=
  ∀ ⦃W : C⦄ (a : X ⟶ W) (b : W ⟶ Y), a ≫ b = φ → S a → IsIso a

/-- **Minimal-coadjoint to `S`** ([FrdI] §0, p. 17): in every factorization `φ = a ≫ b` with
`b ∈ S`, `b` is an isomorphism. -/
def MinCoadj (S : MorClass C) {X Y : C} (φ : X ⟶ Y) : Prop :=
  ∀ ⦃W : C⦄ (a : X ⟶ W) (b : W ⟶ Y), a ≫ b = φ → S b → IsIso b

/-- **Mid-adjoint to `S`** ([FrdI] §0, p. 17): in every factorization `φ = a ≫ b ≫ c` with
`b ∈ S`, `b` is an isomorphism. -/
def MidAdj (S : MorClass C) {X Y : C} (φ : X ⟶ Y) : Prop :=
  ∀ ⦃V W : C⦄ (a : X ⟶ V) (b : V ⟶ W) (c : W ⟶ Y), a ≫ b ≫ c = φ → S b → IsIso b

/-- Morphisms which are composites `a ≫ b` with `a ∈ P`, `b ∈ Q`. -/
def CompOf (P Q : MorClass C) {X Y : C} (φ : X ⟶ Y) : Prop :=
  ∃ (W : C) (a : X ⟶ W) (b : W ⟶ Y), P a ∧ Q b ∧ a ≫ b = φ

/-- Two objects are the domain and codomain of a span of morphisms of `S`. -/
def SpanOf (S : MorClass C) (X Y : C) : Prop :=
  ∃ (E : C) (a : E ⟶ X) (b : E ⟶ Y), S a ∧ S b

lemma isIso_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsIso φ) :=
  ⟨fun _ _ _ _ _ h => by haveI := h; infer_instance,
    fun _ _ _ _ _ h => by haveI := h; infer_instance⟩

lemma isFiberwiseSurjective_respIso :
    RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsFiberwiseSurjective φ) := by
  refine ⟨fun X X' Y e φ h => ?_, fun X Y Y' φ e h => ?_⟩
  · intro T γ
    obtain ⟨W, δB, δX, hδ⟩ := h γ
    exact ⟨W, δB ≫ e.inv, δX, by simpa using hδ⟩
  · intro T γ
    obtain ⟨W, δB, δX, hδ⟩ := h (γ ≫ e.inv)
    exact ⟨W, δB, δX, by rw [← Category.assoc, hδ]; simp⟩

lemma isFSM_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsFSM φ) := by
  refine ⟨fun X X' Y e φ h => ⟨?_, isFiberwiseSurjective_respIso.left e φ h.2⟩,
    fun X Y Y' φ e h => ⟨?_, isFiberwiseSurjective_respIso.right φ e h.2⟩⟩
  · haveI := h.1; infer_instance
  · haveI := h.1; infer_instance

lemma isIrreducible_respIso : RespIso (fun (X Y : C) (φ : X ⟶ Y) => IsIrreducible φ) := by
  refine ⟨fun X X' Y e φ h => ⟨fun hi => h.1 ?_, fun W a b hab => ?_⟩,
    fun X Y Y' φ e h => ⟨fun hi => h.1 ?_, fun W a b hab => ?_⟩⟩
  · haveI := hi
    have : φ = e.inv ≫ (e.hom ≫ φ) := by simp
    rw [this]; infer_instance
  · rcases h.2 (e.inv ≫ a) b (by rw [Category.assoc, hab]; simp) with h' | h'
    · left
      haveI := h'
      have : a = e.hom ≫ (e.inv ≫ a) := by simp
      rw [this]; infer_instance
    · exact Or.inr h'
  · haveI := hi
    have : φ = (φ ≫ e.hom) ≫ e.inv := by simp
    rw [this]; infer_instance
  · rcases h.2 a (b ≫ e.inv) (by rw [← Category.assoc, hab]; simp) with h' | h'
    · exact Or.inl h'
    · right
      haveI := h'
      have : b = (b ≫ e.inv) ≫ e.hom := by simp
      rw [this]; infer_instance

end Notions

/-! ### Transport by an equivalence -/

section Transport

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
variable (F : C₁ ⥤ C₂)

/-- `F` **matches** the classes `P` of `C₁` and `Q` of `C₂`: `P φ ↔ Q (F φ)`. -/
def Corresp (P : MorClass C₁) (Q : MorClass C₂) : Prop :=
  ∀ ⦃X Y : C₁⦄ (φ : X ⟶ Y), P φ ↔ Q (F.map φ)

variable [F.IsEquivalence]

/-- Replacement of a morphism `X' ⟶ F Y` by the image of a morphism of `C₁`. -/
noncomputable def preimageL {Y : C₁} {X' : C₂} (φ : X' ⟶ F.obj Y) :
    F.objPreimage X' ⟶ Y :=
  F.preimage ((F.objObjPreimageIso X').hom ≫ φ)

lemma map_preimageL {Y : C₁} {X' : C₂} (φ : X' ⟶ F.obj Y) :
    F.map (preimageL F φ) = (F.objObjPreimageIso X').hom ≫ φ := by
  simp [preimageL]

/-- Replacement of a morphism `F X ⟶ Y'`. -/
noncomputable def preimageR {X : C₁} {Y' : C₂} (φ : F.obj X ⟶ Y') :
    X ⟶ F.objPreimage Y' :=
  F.preimage (φ ≫ (F.objObjPreimageIso Y').inv)

lemma map_preimageR {X : C₁} {Y' : C₂} (φ : F.obj X ⟶ Y') :
    F.map (preimageR F φ) = φ ≫ (F.objObjPreimageIso Y').inv := by
  simp [preimageR]

lemma corresp_isIso : Corresp F (fun _ _ φ => IsIso φ) (fun _ _ φ => IsIso φ) :=
  fun _ _ φ => ⟨fun h => by haveI := h; infer_instance,
    fun h => by haveI := h; exact isIso_of_fully_faithful F φ⟩

lemma corresp_mono : Corresp F (fun _ _ φ => Mono φ) (fun _ _ φ => Mono φ) :=
  fun _ _ φ => ⟨fun h => by haveI := h; infer_instance, fun h => F.mono_of_mono_map h⟩

lemma corresp_isFiberwiseSurjective :
    Corresp F (fun _ _ φ => IsFiberwiseSurjective φ)
      (fun _ _ φ => IsFiberwiseSurjective φ) := by
  intro B A β
  constructor
  · intro h T' γ'
    obtain ⟨Y, δB, δX, hδ⟩ := h (preimageL F γ')
    refine ⟨F.obj Y, F.map δB, F.map δX ≫ (F.objObjPreimageIso T').hom, ?_⟩
    rw [← F.map_comp, hδ, F.map_comp, map_preimageL, Category.assoc]
  · intro h T γ
    obtain ⟨Y', δB', δX', hδ⟩ := h (F.map γ)
    refine ⟨F.objPreimage Y', preimageL F δB', preimageL F δX', F.map_injective ?_⟩
    simp only [F.map_comp, map_preimageL, Category.assoc, hδ]

lemma corresp_isFSM : Corresp F (fun _ _ φ => IsFSM φ) (fun _ _ φ => IsFSM φ) :=
  fun _ _ φ => and_congr (corresp_mono F φ) (corresp_isFiberwiseSurjective F φ)

lemma corresp_isIrreducible :
    Corresp F (fun _ _ φ => IsIrreducible φ) (fun _ _ φ => IsIrreducible φ) := by
  intro X Y φ
  refine and_congr (not_congr (corresp_isIso F φ)) ⟨fun h W' a' b' hab => ?_,
    fun h W a b hab => ?_⟩
  · rcases h (preimageR F a') (preimageL F b')
      (F.map_injective (by simp [map_preimageR, map_preimageL, hab])) with h' | h'
    · left
      have := (corresp_isIso F _).1 h'
      rw [map_preimageR] at this
      exact (isIso_respIso.right_iff a' (F.objObjPreimageIso W').symm).1 this
    · right
      have := (corresp_isIso F _).1 h'
      rw [map_preimageL] at this
      exact (isIso_respIso.left_iff (F.objObjPreimageIso W') b').1 this
  · rcases h (F.map a) (F.map b) (by rw [← F.map_comp, hab]) with h' | h'
    · exact Or.inl ((corresp_isIso F a).2 h')
    · exact Or.inr ((corresp_isIso F b).2 h')

variable {F}

lemma Corresp.minAdj {P : MorClass C₁} {Q : MorClass C₂} (h : Corresp F P Q)
    (hQ : RespIso Q) : Corresp F (fun _ _ φ => MinAdj P φ) (fun _ _ φ => MinAdj Q φ) := by
  intro X Y φ
  constructor
  · intro hm W' a' b' hab ha'
    have hP : P (preimageR F a') := by
      rw [h, map_preimageR]; exact hQ.right a' (F.objObjPreimageIso W').symm ha'
    have hi := hm (preimageR F a') (preimageL F b')
      (F.map_injective (by simp [map_preimageR, map_preimageL, hab])) hP
    have := (corresp_isIso F _).1 hi
    rw [map_preimageR] at this
    exact (isIso_respIso.right_iff a' (F.objObjPreimageIso W').symm).1 this
  · intro hm W a b hab ha
    exact (corresp_isIso F a).2 (hm (F.map a) (F.map b) (by rw [← F.map_comp, hab])
      ((h a).1 ha))

lemma Corresp.minCoadj {P : MorClass C₁} {Q : MorClass C₂} (h : Corresp F P Q)
    (hQ : RespIso Q) : Corresp F (fun _ _ φ => MinCoadj P φ) (fun _ _ φ => MinCoadj Q φ) := by
  intro X Y φ
  constructor
  · intro hm W' a' b' hab hb'
    have hP : P (preimageL F b') := by
      rw [h, map_preimageL]; exact hQ.left _ b' hb'
    have hi := hm (preimageR F a') (preimageL F b')
      (F.map_injective (by simp [map_preimageR, map_preimageL, hab])) hP
    have := (corresp_isIso F _).1 hi
    rw [map_preimageL] at this
    exact (isIso_respIso.left_iff _ b').1 this
  · intro hm W a b hab hb
    exact (corresp_isIso F b).2 (hm (F.map a) (F.map b) (by rw [← F.map_comp, hab])
      ((h b).1 hb))

lemma Corresp.midAdj {P : MorClass C₁} {Q : MorClass C₂} (h : Corresp F P Q)
    (hQ : RespIso Q) : Corresp F (fun _ _ φ => MidAdj P φ) (fun _ _ φ => MidAdj Q φ) := by
  intro X Y φ
  constructor
  · intro hm V' W' a' b' c' habc hb'
    let eV := F.objObjPreimageIso V'
    let eW := F.objObjPreimageIso W'
    let b : F.objPreimage V' ⟶ F.objPreimage W' := F.preimage (eV.hom ≫ b' ≫ eW.inv)
    have hFb : F.map b = eV.hom ≫ b' ≫ eW.inv := by simp [b]
    have hP : P b := by
      rw [h, hFb]
      exact hQ.left eV _ (hQ.right b' eW.symm hb')
    have hi := hm (preimageR F a') b (preimageL F c')
      (F.map_injective (by simp [map_preimageR, map_preimageL, hFb, eV, eW, habc])) hP
    have := (corresp_isIso F b).1 hi
    rw [hFb] at this
    have e : b' = eV.inv ≫ (eV.hom ≫ b' ≫ eW.inv) ≫ eW.hom := by simp
    rw [e]
    haveI := this
    infer_instance
  · intro hm V W a b c habc hb
    exact (corresp_isIso F b).2 (hm (F.map a) (F.map b) (F.map c)
      (by rw [← F.map_comp, ← F.map_comp, habc]) ((h b).1 hb))

lemma Corresp.compOf {P P' : MorClass C₁} {Q Q' : MorClass C₂} (h : Corresp F P Q)
    (h' : Corresp F P' Q') (hQ : RespIso Q) (hQ' : RespIso Q') :
    Corresp F (fun _ _ φ => CompOf P P' φ) (fun _ _ φ => CompOf Q Q' φ) := by
  intro X Y φ
  constructor
  · rintro ⟨W, a, b, ha, hb, hab⟩
    exact ⟨F.obj W, F.map a, F.map b, (h a).1 ha, (h' b).1 hb, by rw [← F.map_comp, hab]⟩
  · rintro ⟨W', a', b', ha', hb', hab⟩
    refine ⟨F.objPreimage W', preimageR F a', preimageL F b', ?_, ?_,
      F.map_injective (by simp [map_preimageR, map_preimageL, hab])⟩
    · rw [h, map_preimageR]; exact hQ.right a' (F.objObjPreimageIso W').symm ha'
    · rw [h', map_preimageL]; exact hQ'.left _ b' hb'

lemma Corresp.spanOf {P : MorClass C₁} {Q : MorClass C₂} (h : Corresp F P Q) (hQ : RespIso Q)
    (X Y : C₁) : SpanOf P X Y ↔ SpanOf Q (F.obj X) (F.obj Y) := by
  constructor
  · rintro ⟨E, a, b, ha, hb⟩
    exact ⟨F.obj E, F.map a, F.map b, (h a).1 ha, (h b).1 hb⟩
  · rintro ⟨E', a', b', ha', hb'⟩
    refine ⟨F.objPreimage E', preimageL F a', preimageL F b', ?_, ?_⟩
    · rw [h, map_preimageL]; exact hQ.left _ a' ha'
    · rw [h, map_preimageL]; exact hQ.left _ b' hb'

omit [F.IsEquivalence] in
lemma Corresp.and {P P' : MorClass C₁} {Q Q' : MorClass C₂} (h : Corresp F P Q)
    (h' : Corresp F P' Q') : Corresp F (fun _ _ φ => P φ ∧ P' φ) (fun _ _ φ => Q φ ∧ Q' φ) :=
  fun _ _ φ => and_congr (h φ) (h' φ)

omit [F.IsEquivalence] in
lemma Corresp.of_iff {P P' : MorClass C₁} {Q Q' : MorClass C₂} (h : Corresp F P Q)
    (hP : ∀ ⦃X Y : C₁⦄ (φ : X ⟶ Y), P' φ ↔ P φ) (hQ : ∀ ⦃X Y : C₂⦄ (φ : X ⟶ Y), Q' φ ↔ Q φ) :
    Corresp F P' Q' :=
  fun _ _ φ => (hP φ).trans ((h φ).trans (hQ _).symm)

end Transport

end Frobenioid

end Iut
