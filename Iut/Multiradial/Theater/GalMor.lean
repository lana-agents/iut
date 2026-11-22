/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.OuterHom

/-!
# Morphisms and poly-morphisms of Galois categories (MR22 T1, part 2)

IUT I, §0 (l.1973–2087 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`):

* a **morphism** `C₁ → C₂` of connected temperoids (or of their subcategories of connected
  objects) is an isomorphism class of functors `C₂ → C₁` preserving finite limits and countable
  colimits; for `C_i ≅ B^temp(Π_i)⁰` these are in natural bijection with the continuous **outer
  homomorphisms** `Π₁ → Π₂` (Remark 2.5.3 (ii), (E7); [SemiAnbd], Proposition 3.2);
* an **isomorphism** `C₁ → C₂` is an isomorphism class of equivalences (`PrimeStrip.CatIsom`);
* a **poly-morphism** is a set of morphisms; composition is the set of composites; the **full
  poly-isomorphism** is the set of all isomorphisms.

Following the lead decision 2 of `MR22-plan.md`, a morphism is represented group-theoretically,
transported along equivalences with the models: for categories `C_i` that have equivalences
`e_i : C_i ≌ B(G_i)⁰` with fixed model groups `G_i`, a **presentation** (`GalTriple`) is a triple
`(e₁, e₂, f)` with `f : G₁ → G₂` a continuous homomorphism, and two presentations are identified
(`tripleSetoid`) when they differ by automorphisms `σ` of `G₁`, `τ` of `G₂` and conjugation:
`e₁' ≅ e₁ ⋙ σ_*`, `e₂' ≅ e₂ ⋙ τ_*`, `f' ∘ σ = γ (τ ∘ f) γ⁻¹`. A morphism `C₁ → C₂`
(`GalMor C₁ C₂ G₁ G₂`) is a class of presentations. That this depends only on the categories (any
two equivalences `C_i ≌ B(G_i)⁰` differ by an automorphism of `G_i`) is the functorial
reconstruction `OrbitEquivRecon` (MR21's `OrbitIsoRecon`).

Results:

* composition (`IsComp`): existence of composites from `OrbitEquivRecon G₂ G₂`
  (`exists_isComp`), uniqueness from the rigidity of `G₂` (`isComp_unique`: `G₂` Hausdorff, with a
  basis of open normal subgroups and complete for them);
* the morphism induced by an equivalence (`Induces`): existence (`exists_induces`), uniqueness
  (`induces_unique`), invariance under natural isomorphism (`Induces.of_iso`), and injectivity on
  isomorphism classes (`iso_of_induces`); hence isomorphisms `C₁ → C₂` in the sense of IUT I, §0
  are exactly the morphisms induced by equivalences (`IsIsom`);
* poly-morphisms (`PolyMor`), their composition (`PolyMor.comp`), the full poly-isomorphism
  (`PolyMor.full`) and the poly-isomorphism of a set of isomorphism classes
  (`PolyMor.ofCatIsoms`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace Theater

open CategoryTheory Iut.Frobenioid

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ### Twisting by automorphisms -/

section Twist

variable {C : Type u₁} [Category.{v₁} C] {G : Type} [Group G] [TopologicalSpace G]

/-- `e'` is `e` followed by the automorphism `σ` of `G`: `e' ≅ e ⋙ σ_*`. -/
def Twist (e e' : C ⥤ OrbitObj G) (σ : G ≃ₜ* G) : Prop :=
  Nonempty (e' ≅ e ⋙ OrbitObj.isoFunctor σ)

lemma Twist.rfl' (e : C ⥤ OrbitObj G) : Twist e e (ContinuousMulEquiv.refl G) :=
  ⟨(Functor.rightUnitor e).symm ≪≫ Functor.isoWhiskerLeft e isoFunctorRefl.symm⟩

lemma Twist.symm {e e' : C ⥤ OrbitObj G} {σ : G ≃ₜ* G} (h : Twist e e' σ) :
    Twist e' e σ.symm := by
  obtain ⟨i⟩ := h
  exact ⟨((Functor.isoWhiskerRight i _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e (isoFunctorSymmComp σ) ≪≫ Functor.rightUnitor e)).symm⟩

lemma Twist.trans {e e' e'' : C ⥤ OrbitObj G} {σ σ' : G ≃ₜ* G} (h : Twist e e' σ)
    (h' : Twist e' e'' σ') : Twist e e'' (σ.trans σ') := by
  obtain ⟨i⟩ := h
  obtain ⟨i'⟩ := h'
  exact ⟨i' ≪≫ Functor.isoWhiskerRight i _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft e (isoFunctorTrans σ σ').symm⟩

/-- Cancelling an equivalence on the left. -/
def cancelLeft {D : Type u₂} [Category.{v₂} D] {X : Type u₃} [Category.{v₃} X] (e : C ≌ D)
    {F F' : D ⥤ X} (h : e.functor ⋙ F ≅ e.functor ⋙ F') : F ≅ F' :=
  (Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.counitIso.symm F ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse h ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e.counitIso F' ≪≫
    Functor.leftUnitor F'

/-- Cancelling an equivalence on the right. -/
def cancelRight {D : Type u₂} [Category.{v₂} D] {X : Type u₃} [Category.{v₃} X] (e : D ≌ X)
    {F F' : C ⥤ D} (h : F ⋙ e.functor ≅ F' ⋙ e.functor) : F ≅ F' :=
  (Functor.rightUnitor F).symm ≪≫ Functor.isoWhiskerLeft F e.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h e.inverse ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F' e.unitIso.symm ≪≫
    Functor.rightUnitor F'

/-- Any two equivalences `C ≌ B(G)⁰` differ by a twist (from `OrbitEquivRecon G G`). -/
lemma twist_of_recon (h : OrbitEquivRecon G G) (e e' : C ≌ OrbitObj G) :
    ∃ σ : G ≃ₜ* G, Twist e.functor e'.functor σ := by
  obtain ⟨σ, ⟨i⟩⟩ := h (e.symm.trans e')
  exact ⟨σ, ⟨(Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.functor i⟩⟩

end Twist

/-! ### Twisted homomorphisms -/

section TwistHom

variable {G₁ G₂ G₃ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [Group G₃] [TopologicalSpace G₃]

/-- `f' ∘ σ = γ (τ ∘ f) γ⁻¹` for some `γ`. -/
def TwistHom (f f' : G₁ →ₜ* G₂) (σ : G₁ ≃ₜ* G₁) (τ : G₂ ≃ₜ* G₂) : Prop :=
  ∃ γ : G₂, ∀ x, f' (σ x) = γ * τ (f x) * γ⁻¹

lemma TwistHom.rfl' (f : G₁ →ₜ* G₂) :
    TwistHom f f (ContinuousMulEquiv.refl G₁) (ContinuousMulEquiv.refl G₂) :=
  ⟨1, fun x => by simp⟩

lemma TwistHom.symm {f f' : G₁ →ₜ* G₂} {σ : G₁ ≃ₜ* G₁} {τ : G₂ ≃ₜ* G₂}
    (h : TwistHom f f' σ τ) : TwistHom f' f σ.symm τ.symm := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨(τ.symm γ)⁻¹, fun y => ?_⟩
  have h1 := hγ (σ.symm y)
  rw [ContinuousMulEquiv.apply_symm_apply] at h1
  rw [h1, map_mul, map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply]
  group

lemma TwistHom.trans {f f' f'' : G₁ →ₜ* G₂} {σ σ' : G₁ ≃ₜ* G₁} {τ τ' : G₂ ≃ₜ* G₂}
    (h : TwistHom f f' σ τ) (h' : TwistHom f' f'' σ' τ') :
    TwistHom f f'' (σ.trans σ') (τ.trans τ') := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨δ, hδ⟩ := h'
  refine ⟨δ * τ' γ, fun x => ?_⟩
  change f'' (σ' (σ x)) = _ * τ' (τ (f x)) * _
  rw [hδ, hγ, map_mul, map_mul, map_inv]
  group

/-- Twisted homomorphisms compose. -/
lemma TwistHom.comp {f f' : G₁ →ₜ* G₂} {g g' : G₂ →ₜ* G₃} {σ : G₁ ≃ₜ* G₁} {τ : G₂ ≃ₜ* G₂}
    {ρ : G₃ ≃ₜ* G₃} (hf : TwistHom f f' σ τ) (hg : TwistHom g g' τ ρ) :
    TwistHom (g.comp f) (g'.comp f') σ ρ := by
  obtain ⟨γ, hγ⟩ := hf
  obtain ⟨δ, hδ⟩ := hg
  refine ⟨g' γ * δ, fun x => ?_⟩
  change g' (f' (σ x)) = _ * ρ (g (f x)) * _
  rw [hγ, map_mul, map_mul, map_inv, hδ]
  group

end TwistHom

/-! ### Presentations and morphisms -/

section Mor

variable (C₁ : Type u₁) [Category.{v₁} C₁] (C₂ : Type u₂) [Category.{v₂} C₂]
  (C₃ : Type u₃) [Category.{v₃} C₃]
  (G₁ G₂ G₃ : Type) [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [Group G₃] [TopologicalSpace G₃]

/-- **A presentation of a morphism `C₁ → C₂`**: equivalences `e_i : C_i ≌ B(G_i)⁰` and a
continuous homomorphism `f : G₁ → G₂`. -/
structure GalTriple where
  /-- `C₁ ≌ B(G₁)⁰`. -/
  e₁ : C₁ ≌ OrbitObj G₁
  /-- `C₂ ≌ B(G₂)⁰`. -/
  e₂ : C₂ ≌ OrbitObj G₂
  /-- The homomorphism `G₁ → G₂`. -/
  f : G₁ →ₜ* G₂

variable {C₁ C₂ C₃ G₁ G₂ G₃}

/-- Two presentations are equivalent when they differ by automorphisms of `G₁`, `G₂` and
conjugation. -/
def TripleRel (t t' : GalTriple C₁ C₂ G₁ G₂) : Prop :=
  ∃ (σ : G₁ ≃ₜ* G₁) (τ : G₂ ≃ₜ* G₂), Twist t.e₁.functor t'.e₁.functor σ ∧
    Twist t.e₂.functor t'.e₂.functor τ ∧ TwistHom t.f t'.f σ τ

variable (C₁ C₂ G₁ G₂) in
/-- The equivalence of presentations. -/
def tripleSetoid : Setoid (GalTriple C₁ C₂ G₁ G₂) where
  r := TripleRel
  iseqv := ⟨fun _ => ⟨_, _, Twist.rfl' _, Twist.rfl' _, TwistHom.rfl' _⟩,
    fun ⟨σ, τ, h₁, h₂, h₃⟩ => ⟨σ.symm, τ.symm, h₁.symm, h₂.symm, h₃.symm⟩,
    fun ⟨σ, τ, h₁, h₂, h₃⟩ ⟨σ', τ', h₁', h₂', h₃'⟩ =>
      ⟨σ.trans σ', τ.trans τ', h₁.trans h₁', h₂.trans h₂', h₃.trans h₃'⟩⟩

variable (C₁ C₂ G₁ G₂) in
/-- **A morphism `C₁ → C₂` of Galois categories with models `B(G₁)⁰`, `B(G₂)⁰`** (IUT I, §0;
transported outer homomorphisms, see the module docstring). -/
def GalMor : Type _ := Quotient (tripleSetoid C₁ C₂ G₁ G₂)

/-- The morphism of a presentation. -/
def GalMor.mk (t : GalTriple C₁ C₂ G₁ G₂) : GalMor C₁ C₂ G₁ G₂ :=
  Quotient.mk (tripleSetoid C₁ C₂ G₁ G₂) t

lemma GalMor.mk_eq_mk {t t' : GalTriple C₁ C₂ G₁ G₂} :
    GalMor.mk t = GalMor.mk t' ↔ TripleRel t t' :=
  Quotient.eq

lemma GalMor.mk_surjective : Function.Surjective (GalMor.mk : GalTriple C₁ C₂ G₁ G₂ → _) :=
  Quotient.mk_surjective

/-- With the equivalences fixed, conjugate homomorphisms give the same morphism. -/
lemma GalMor.mk_eq_of_conj (e₁ : C₁ ≌ OrbitObj G₁) (e₂ : C₂ ≌ OrbitObj G₂) {f f' : G₁ →ₜ* G₂}
    (h : ConjRel f f') : GalMor.mk ⟨e₁, e₂, f⟩ = GalMor.mk ⟨e₁, e₂, f'⟩ := by
  obtain ⟨γ, hγ⟩ := h
  exact GalMor.mk_eq_mk.2 ⟨_, _, Twist.rfl' _, Twist.rfl' _, γ, fun x => hγ x⟩

/-- With the equivalences fixed, the morphisms are the outer homomorphisms
(`OrbitEquivRecon G₁ G₁` and `OrbitEquivRecon G₂ G₂`: every morphism has a presentation with any
given equivalences). -/
lemma GalMor.exists_mk_eq (h₁ : OrbitEquivRecon G₁ G₁) (h₂ : OrbitEquivRecon G₂ G₂)
    (e₁ : C₁ ≌ OrbitObj G₁) (e₂ : C₂ ≌ OrbitObj G₂) (m : GalMor C₁ C₂ G₁ G₂) :
    ∃ f : G₁ →ₜ* G₂, GalMor.mk ⟨e₁, e₂, f⟩ = m := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective m
  obtain ⟨σ, hσ⟩ := twist_of_recon h₁ t.e₁ e₁
  obtain ⟨τ, hτ⟩ := twist_of_recon h₂ t.e₂ e₂
  refine ⟨(ContinuousMonoidHom.toContinuousMonoidHom τ).comp
    (t.f.comp (ContinuousMonoidHom.toContinuousMonoidHom σ.symm)), ?_⟩
  refine (GalMor.mk_eq_mk.2 ⟨σ, τ, hσ, hτ, 1, fun x => ?_⟩).symm
  simp

/-! ### Composition -/

/-- **`c` is a composite of `a` and `b`**: presentations of `a` and `b` whose middle equivalences
are isomorphic, and `c` is presented by the composite homomorphism. -/
def IsComp (a : GalMor C₁ C₂ G₁ G₂) (b : GalMor C₂ C₃ G₂ G₃) (c : GalMor C₁ C₃ G₁ G₃) : Prop :=
  ∃ (t : GalTriple C₁ C₂ G₁ G₂) (s : GalTriple C₂ C₃ G₂ G₃), GalMor.mk t = a ∧ GalMor.mk s = b ∧
    Nonempty (s.e₁.functor ≅ t.e₂.functor) ∧ c = GalMor.mk ⟨t.e₁, s.e₂, s.f.comp t.f⟩

/-- **Composites exist** (`OrbitEquivRecon G₂ G₂`). -/
theorem exists_isComp (h : OrbitEquivRecon G₂ G₂) (a : GalMor C₁ C₂ G₁ G₂)
    (b : GalMor C₂ C₃ G₂ G₃) : ∃ c, IsComp a b c := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective a
  obtain ⟨s, rfl⟩ := GalMor.mk_surjective b
  obtain ⟨τ, ⟨i⟩⟩ := twist_of_recon h t.e₂ s.e₁
  let t' : GalTriple C₁ C₂ G₁ G₂ :=
    ⟨t.e₁, s.e₁, (ContinuousMonoidHom.toContinuousMonoidHom τ).comp t.f⟩
  have ht : GalMor.mk t = GalMor.mk t' :=
    GalMor.mk_eq_mk.2 ⟨ContinuousMulEquiv.refl G₁, τ, Twist.rfl' _, ⟨i⟩, 1, fun x => by
      change τ (t.f x) = 1 * τ (t.f x) * 1⁻¹
      group⟩
  exact ⟨_, t', s, ht.symm, rfl, ⟨Iso.refl _⟩, rfl⟩

/-- **Composites are unique** (`G₂` Hausdorff, with a basis of open normal subgroups, complete for
them: rigidity, `conj_of_isoFunctor_iso`). -/
theorem isComp_unique [IsTopologicalGroup G₂] [T2Space G₂] (hb : HasONSBasis G₂)
    (hc : IsONSComplete G₂) {a : GalMor C₁ C₂ G₁ G₂} {b : GalMor C₂ C₃ G₂ G₃}
    {c c' : GalMor C₁ C₃ G₁ G₃} (h : IsComp a b c) (h' : IsComp a b c') : c = c' := by
  obtain ⟨t, s, rfl, rfl, ⟨i⟩, rfl⟩ := h
  obtain ⟨t', s', ht, hs, ⟨i'⟩, rfl⟩ := h'
  obtain ⟨σ, τ, h₁, ⟨j₂⟩, h₃⟩ := GalMor.mk_eq_mk.1 ht.symm
  obtain ⟨τ', ρ, ⟨j₁⟩, h₂', h₃'⟩ := GalMor.mk_eq_mk.1 hs.symm
  -- `t.e₂ ⋙ τ_* ≅ t'.e₂ ≅ s'.e₁ ≅ s.e₁ ⋙ τ'_* ≅ t.e₂ ⋙ τ'_*`
  have k : OrbitObj.isoFunctor τ ≅ OrbitObj.isoFunctor τ' :=
    cancelLeft t.e₂ (j₂.symm ≪≫ i'.symm ≪≫ j₁ ≪≫ Functor.isoWhiskerRight i _)
  obtain ⟨κ, hκ⟩ := conj_of_isoFunctor_iso hb hc τ τ' k
  refine GalMor.mk_eq_mk.2 ⟨σ, ρ, h₁, h₂', ?_⟩
  -- `s'.f ∘ τ = (s'.f κ)⁻¹ (s'.f ∘ τ') (s'.f κ)`
  have h₃'' : TwistHom s.f s'.f τ ρ := by
    obtain ⟨δ, hδ⟩ := h₃'
    refine ⟨(s'.f κ)⁻¹ * δ, fun y => ?_⟩
    have e : τ y = κ⁻¹ * τ' y * κ := by rw [hκ]; group
    rw [e, map_mul, map_mul, map_inv, hδ]
    group
  exact h₃.comp h₃''

/-! ### Morphisms induced by equivalences -/

/-- **`m` is induced by the equivalence `E : C₁ ≌ C₂`**: a presentation `(e₁, e₂, σ)` of `m` with
`σ` an isomorphism and `E ⋙ e₂ ≅ e₁ ⋙ σ_*`. -/
def Induces (E : C₁ ≌ C₂) (m : GalMor C₁ C₂ G₁ G₂) : Prop :=
  ∃ (t : GalTriple C₁ C₂ G₁ G₂) (σ : G₁ ≃ₜ* G₂), GalMor.mk t = m ∧ (∀ x, t.f x = σ x) ∧
    Nonempty (E.functor ⋙ t.e₂.functor ≅ t.e₁.functor ⋙ OrbitObj.isoFunctor σ)

/-- The induced morphism depends only on the isomorphism class of `E`. -/
lemma Induces.of_iso {E E' : C₁ ≌ C₂} (i : E.functor ≅ E'.functor) {m : GalMor C₁ C₂ G₁ G₂}
    (h : Induces E m) : Induces E' m := by
  obtain ⟨t, σ, hm, hf, ⟨j⟩⟩ := h
  exact ⟨t, σ, hm, hf, ⟨Functor.isoWhiskerRight i.symm _ ≪≫ j⟩⟩

/-- **Equivalences induce morphisms** (`OrbitEquivRecon G₁ G₂`, given equivalences with the
models). -/
theorem exists_induces (h : OrbitEquivRecon G₁ G₂) (e₁ : C₁ ≌ OrbitObj G₁)
    (e₂ : C₂ ≌ OrbitObj G₂) (E : C₁ ≌ C₂) : ∃ m : GalMor C₁ C₂ G₁ G₂, Induces E m := by
  obtain ⟨σ, ⟨i⟩⟩ := h ((e₁.symm.trans E).trans e₂)
  refine ⟨_, ⟨e₁, e₂, ContinuousMonoidHom.toContinuousMonoidHom σ⟩, σ, rfl, fun _ => rfl, ⟨?_⟩⟩
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight e₁.unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e₁.functor
      ((Functor.associator _ _ _).symm ≪≫ i)

/-- **The induced morphism is unique** (`OrbitEquivRecon` for `G₁` and `G₂`; rigidity of `G₂`). -/
theorem induces_unique [IsTopologicalGroup G₂] [T2Space G₂]
    (h₁ : OrbitEquivRecon G₁ G₁) (h₂ : OrbitEquivRecon G₂ G₂) (hb : HasONSBasis G₂)
    (hc : IsONSComplete G₂) {E : C₁ ≌ C₂} {m m' : GalMor C₁ C₂ G₁ G₂} (h : Induces E m)
    (h' : Induces E m') : m = m' := by
  obtain ⟨t, σ, rfl, hf, ⟨i⟩⟩ := h
  obtain ⟨t', σ', rfl, hf', ⟨i'⟩⟩ := h'
  obtain ⟨α, ⟨a⟩⟩ := twist_of_recon h₁ t.e₁ t'.e₁
  obtain ⟨β, ⟨b⟩⟩ := twist_of_recon h₂ t.e₂ t'.e₂
  -- `t.e₁ ⋙ α_* ⋙ σ'_* ≅ E ⋙ t'.e₂ ≅ E ⋙ t.e₂ ⋙ β_* ≅ t.e₁ ⋙ σ_* ⋙ β_*`
  have k : OrbitObj.isoFunctor (α.trans σ') ≅ OrbitObj.isoFunctor (σ.trans β) :=
    cancelLeft t.e₁ (Functor.isoWhiskerLeft _ (isoFunctorTrans α σ') ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight a.symm _ ≪≫ i'.symm ≪≫
      Functor.isoWhiskerLeft _ b ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight i _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (isoFunctorTrans σ β).symm)
  obtain ⟨κ, hκ⟩ := conj_of_isoFunctor_iso hb hc _ _ k
  refine GalMor.mk_eq_mk.2 ⟨α, β, ⟨a⟩, ⟨b⟩, κ⁻¹, fun x => ?_⟩
  have e := hκ x
  change β (σ x) = κ * σ' (α x) * κ⁻¹ at e
  rw [hf', hf, e]
  group

/-- **Equivalences inducing the same morphism are isomorphic.** -/
theorem iso_of_induces {E E' : C₁ ≌ C₂} {m : GalMor C₁ C₂ G₁ G₂} (h : Induces E m)
    (h' : Induces E' m) : Nonempty (E.functor ≅ E'.functor) := by
  obtain ⟨t, σ, rfl, hf, ⟨i⟩⟩ := h
  obtain ⟨t', σ', ht, hf', ⟨i'⟩⟩ := h'
  obtain ⟨α, β, ⟨a⟩, ⟨b⟩, γ, hγ⟩ := GalMor.mk_eq_mk.1 ht.symm
  -- `σ' ∘ α = γ (β ∘ σ) γ⁻¹`, hence `α_* ⋙ σ'_* ≅ σ_* ⋙ β_*`
  have hconj : ∀ x, (α.trans σ') x = γ * (σ.trans β) x * γ⁻¹ := fun x => by
    change σ' (α x) = γ * β (σ x) * γ⁻¹
    rw [← hf', hγ, hf]
  have k : OrbitObj.isoFunctor (α.trans σ') ≅ OrbitObj.isoFunctor (σ.trans β) :=
    OrbitObj.mapFunctorConjIso _ _ _ _ γ hconj
  -- `E' ⋙ t.e₂ ⋙ β_* ≅ E' ⋙ t'.e₂ ≅ t'.e₁ ⋙ σ'_* ≅ t.e₁ ⋙ α_* ⋙ σ'_* ≅ t.e₁ ⋙ σ_* ⋙ β_*`
  --   `≅ E ⋙ t.e₂ ⋙ β_*`
  have k' : E'.functor ⋙ (t.e₂.functor ⋙ OrbitObj.isoFunctor β) ≅
      E.functor ⋙ (t.e₂.functor ⋙ OrbitObj.isoFunctor β) :=
    Functor.isoWhiskerLeft _ b.symm ≪≫ i' ≪≫ Functor.isoWhiskerRight a _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ((isoFunctorTrans α σ').symm ≪≫ k ≪≫
        isoFunctorTrans σ β) ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight i.symm _ ≪≫ Functor.associator _ _ _
  exact ⟨(cancelRight (t.e₂.trans (OrbitObj.equivOfIso β)) k').symm⟩

/-- **`m` is an isomorphism** (IUT I, §0): it is induced by an equivalence. -/
def IsIsom (m : GalMor C₁ C₂ G₁ G₂) : Prop := ∃ E : C₁ ≌ C₂, Induces E m

/-! ### Poly-morphisms -/

variable (C₁ C₂ G₁ G₂) in
/-- **A poly-morphism `C₁ → C₂`** (IUT I, §0): a set of morphisms. -/
abbrev PolyMor : Type _ := Set (GalMor C₁ C₂ G₁ G₂)

/-- **Composition of poly-morphisms**: the set of composites (IUT I, §0). -/
def PolyMor.comp (P : PolyMor C₁ C₂ G₁ G₂) (Q : PolyMor C₂ C₃ G₂ G₃) : PolyMor C₁ C₃ G₁ G₃ :=
  {c | ∃ a ∈ P, ∃ b ∈ Q, IsComp a b c}

variable (C₁ C₂ G₁ G₂) in
/-- **The full poly-isomorphism `C₁ ⥲ C₂`**: all isomorphisms. -/
def PolyMor.full : PolyMor C₁ C₂ G₁ G₂ := {m | IsIsom m}

/-- The poly-isomorphism given by a set of isomorphism classes of equivalences. -/
def PolyMor.ofCatIsoms (S : Set (PrimeStrip.CatIsom C₁ C₂)) : PolyMor C₁ C₂ G₁ G₂ :=
  {m | ∃ E : C₁ ≌ C₂, PrimeStrip.CatIsom.mk E ∈ S ∧ Induces E m}

lemma PolyMor.ofCatIsoms_univ : PolyMor.ofCatIsoms (G₁ := G₁) (G₂ := G₂) Set.univ =
    PolyMor.full C₁ C₂ G₁ G₂ := by
  ext m
  exact ⟨fun ⟨E, _, h⟩ => ⟨E, h⟩, fun ⟨E, h⟩ => ⟨E, Set.mem_univ _, h⟩⟩

end Mor

end Theater

end Multiradial

end Iut
