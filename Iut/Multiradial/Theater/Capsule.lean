/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Multiradial.Theater.LocalToGlobal
import Iut.HodgeTheater.Labels

/-!
# Composition of poly-morphisms, capsules and the poly-morphisms `φ^NF_v`, `φ^NF_⋇` (MR22 T7)

IUT I, §0 (l.1973–2014 of `~/iut-scratch/papers/txt/Inter-universal Teichmuller Theory I.txt`):
the composite of poly-morphisms is the set of composites; a **capsule** is a finite family of
objects; a **morphism of capsules** `{A_j}_{j∈J} → {A'_j'}_{j'∈J'}` is an injection `ι : J ↪ J'`
with morphisms `A_j → A'_{ι(j)}`; the **capsule-full poly-morphism** for `ι` consists of all
families of isomorphisms, a **capsule-full poly-isomorphism** is one with `ι` bijective.

* composition of morphisms of Galois categories (`IsComp`, `GalMor.lean`) is associative
  (`isComp_assoc`) with units `GalMor.id` (`isComp_id_left`, `isComp_id_right`); hence
  `PolyMor.comp` is associative (`PolyMor.comp_assoc`) with units `{GalMor.id e}`; composites of
  isomorphisms are isomorphisms (`isIsom_of_isComp`), so `full ∘ full ⊆ full`
  (`PolyMor.full_comp_full_subset`, with equality when the target is an automorphism);
* capsules: morphisms for a fixed injection (`CapMor`), their composition (`CapIsComp`), capsule
  poly-morphisms (`CapPolyMor`), the capsule-full poly-morphism (`capFull`, `capFullIso`) and
  `capFull ι ∘ capFull ι' ⊆ capFull (ι' ∘ ι)` (`capFull_comp_subset`); the finiteness of the
  index sets plays no role in these statements and is not imposed;
* poly-morphisms from a prime-strip (resp. a capsule of prime-strips) to a category (IUT I,
  Definition 4.1 (vi), l.6492–6503): `StripPolyMor`, `CapStripPolyMor`, with pre- and
  post-composition;
* the model poly-morphisms `φ^NF_v = β ∘ φ^NF_{•,v} ∘ α` (IUT I, Example 4.3 (ii), l.6631–6642;
  `phiNF`) and `φ^Θell_v` (Example 6.3 (i), l.11050–11060; `phiEll`), for a poly-automorphism
  `A` of `D^⊚` (resp. `D^⊚±`) standing for `Aut_ϵ(D^⊚)` (resp. `Aut_csp(D^⊚±)`), and the
  stabilisation of `φ^NF_v` by `A` (Example 4.3 (iv), l.6668: "`φ^NF_1` is stabilized by the
  action of `Aut_ϵ(C_K)`"; `phiNF_comp_subset`);
* `φ^NF_⋇ : D^⋇ → D^⊚` for a poly-action `act` of `F_ℓ^⋇` on `D^⊚` (Example 4.3 (iv),
  l.6670–6690; `phiNFStar`) and its equivariance (`phiNFStar_postcomp`).

Here `B ∘ A` in IUT's notation is `A.comp B` (`PolyMor.comp` is written in diagrammatic order).
Only the non-archimedean places are formalised (`V` is the set of finite places of `K`).
-/

noncomputable section

namespace Iut

namespace Multiradial

namespace Theater

open CategoryTheory NumberField Iut.Frobenioid PrimeStrip

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

/-! ### Associativity and units -/

section Assoc

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
  {G₁ G₂ G₃ G₄ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]
  [Group G₃] [TopologicalSpace G₃] [Group G₄] [TopologicalSpace G₄]

/-- A morphism has a presentation with any given source equivalence (`OrbitEquivRecon G₁ G₁`). -/
lemma GalMor.exists_mk_eq_e₁ (h : OrbitEquivRecon G₁ G₁) (m : GalMor C₁ C₂ G₁ G₂)
    (e : C₁ ≌ OrbitObj G₁) :
    ∃ (e₂ : C₂ ≌ OrbitObj G₂) (f : G₁ →ₜ* G₂), GalMor.mk ⟨e, e₂, f⟩ = m := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective m
  obtain ⟨ρ, hρ⟩ := twist_of_recon h t.e₁ e
  exact ⟨t.e₂, t.f.comp (ContinuousMonoidHom.toContinuousMonoidHom ρ.symm),
    (GalMor.mk_eq_mk (t := t) (t' := ⟨e, t.e₂, _⟩)).2
      ⟨ρ, ContinuousMulEquiv.refl G₂, hρ, Twist.rfl' _, 1, fun x => by simp⟩ |>.symm⟩

/-- Presentations with matching middle equivalences compose. -/
lemma isComp_mk (t : GalTriple C₁ C₂ G₁ G₂) (s : GalTriple C₂ C₃ G₂ G₃)
    (h : Nonempty (s.e₁.functor ≅ t.e₂.functor)) :
    IsComp (GalMor.mk t) (GalMor.mk s) (GalMor.mk ⟨t.e₁, s.e₂, s.f.comp t.f⟩) :=
  ⟨t, s, rfl, rfl, h, rfl⟩

/-- **Composition of morphisms is associative** (`OrbitEquivRecon` and rigidity for the middle
groups `G₂`, `G₃`). -/
theorem isComp_assoc (h₂ : OrbitEquivRecon G₂ G₂) (h₃ : OrbitEquivRecon G₃ G₃)
    [IsTopologicalGroup G₂] [T2Space G₂] (hb₂ : HasONSBasis G₂) (hc₂ : IsONSComplete G₂)
    [IsTopologicalGroup G₃] [T2Space G₃] (hb₃ : HasONSBasis G₃) (hc₃ : IsONSComplete G₃)
    {a : GalMor C₁ C₂ G₁ G₂} {b : GalMor C₂ C₃ G₂ G₃} {c : GalMor C₃ C₄ G₃ G₄}
    {ab : GalMor C₁ C₃ G₁ G₃} {bc : GalMor C₂ C₄ G₂ G₄} {abc a_bc : GalMor C₁ C₄ G₁ G₄}
    (hab : IsComp a b ab) (habc : IsComp ab c abc) (hbc : IsComp b c bc)
    (ha_bc : IsComp a bc a_bc) : abc = a_bc := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective a
  obtain ⟨e₃, g, rfl⟩ := GalMor.exists_mk_eq_e₁ h₂ b t.e₂
  obtain ⟨e₄, k, rfl⟩ := GalMor.exists_mk_eq_e₁ h₃ c e₃
  have h1 : ab = GalMor.mk ⟨t.e₁, e₃, g.comp t.f⟩ :=
    isComp_unique hb₂ hc₂ hab (isComp_mk t ⟨t.e₂, e₃, g⟩ ⟨Iso.refl _⟩)
  have h2 : bc = GalMor.mk ⟨t.e₂, e₄, k.comp g⟩ :=
    isComp_unique hb₃ hc₃ hbc (isComp_mk ⟨t.e₂, e₃, g⟩ ⟨e₃, e₄, k⟩ ⟨Iso.refl _⟩)
  subst h1 h2
  exact (isComp_unique hb₃ hc₃ habc (isComp_mk _ ⟨e₃, e₄, k⟩ ⟨Iso.refl _⟩)).trans
    (isComp_unique hb₂ hc₂ (isComp_mk t _ ⟨Iso.refl _⟩) ha_bc)

variable (C₁ G₁) in
/-- **The identity morphism** `C₁ → C₁`, presented by `(e, e, id)`. -/
def GalMor.id (e : C₁ ≌ OrbitObj G₁) : GalMor C₁ C₁ G₁ G₁ :=
  GalMor.mk ⟨e, e, ContinuousMonoidHom.id G₁⟩

/-- The identity does not depend on the equivalence (`OrbitEquivRecon G₁ G₁`). -/
lemma GalMor.id_eq (h : OrbitEquivRecon G₁ G₁) (e e' : C₁ ≌ OrbitObj G₁) :
    GalMor.id C₁ G₁ e = GalMor.id C₁ G₁ e' := by
  obtain ⟨σ, hσ⟩ := twist_of_recon h e e'
  exact GalMor.mk_eq_mk.2 ⟨σ, σ, hσ, hσ, 1, fun x => by simp⟩

lemma isComp_id_left (h : OrbitEquivRecon G₁ G₁) (e : C₁ ≌ OrbitObj G₁)
    (a : GalMor C₁ C₂ G₁ G₂) : IsComp (GalMor.id C₁ G₁ e) a a := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective a
  rw [GalMor.id_eq h e t.e₁]
  exact isComp_mk ⟨t.e₁, t.e₁, ContinuousMonoidHom.id G₁⟩ t ⟨Iso.refl _⟩

lemma isComp_id_right (h : OrbitEquivRecon G₂ G₂) (e : C₂ ≌ OrbitObj G₂)
    (a : GalMor C₁ C₂ G₁ G₂) : IsComp a (GalMor.id C₂ G₂ e) a := by
  obtain ⟨t, rfl⟩ := GalMor.mk_surjective a
  rw [GalMor.id_eq h e t.e₂]
  exact isComp_mk t ⟨t.e₂, t.e₂, ContinuousMonoidHom.id G₂⟩ ⟨Iso.refl _⟩

/-- The identity is an isomorphism (induced by the identity equivalence). -/
lemma isIsom_id (e : C₁ ≌ OrbitObj G₁) : IsIsom (GalMor.id C₁ G₁ e) :=
  ⟨CategoryTheory.Equivalence.refl, ⟨e, e, ContinuousMonoidHom.id G₁⟩,
    ContinuousMulEquiv.refl G₁, rfl, fun _ => rfl,
    ⟨Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ isoFunctorRefl.symm⟩⟩

/-- An induced morphism has a presentation with any given source equivalence. -/
lemma Induces.exists_e₁ (h : OrbitEquivRecon G₁ G₁) {E : C₁ ≌ C₂} {m : GalMor C₁ C₂ G₁ G₂}
    (hm : Induces E m) (e : C₁ ≌ OrbitObj G₁) :
    ∃ (e₂ : C₂ ≌ OrbitObj G₂) (f : G₁ →ₜ* G₂) (σ : G₁ ≃ₜ* G₂), GalMor.mk ⟨e, e₂, f⟩ = m ∧
      (∀ x, f x = σ x) ∧ Nonempty (E.functor ⋙ e₂.functor ≅ e.functor ⋙ OrbitObj.isoFunctor σ) := by
  obtain ⟨t, τ, rfl, hf, ⟨i⟩⟩ := hm
  obtain ⟨ρ, ⟨k⟩⟩ := twist_of_recon h t.e₁ e
  refine ⟨t.e₂, t.f.comp (ContinuousMonoidHom.toContinuousMonoidHom ρ.symm), ρ.symm.trans τ,
    ((GalMor.mk_eq_mk (t := t) (t' := ⟨e, t.e₂, _⟩)).2
      ⟨ρ, ContinuousMulEquiv.refl G₂, ⟨k⟩, Twist.rfl' _, 1, fun x => by simp⟩).symm,
    fun x => hf _, ⟨?_⟩⟩
  exact i ≪≫ Functor.isoWhiskerLeft t.e₁.functor ((Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (isoFunctorSymmComp ρ).symm _ ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight k.symm _ ≪≫
    Functor.isoWhiskerLeft e.functor (isoFunctorTrans ρ.symm τ).symm

/-- **Composites of isomorphisms are isomorphisms** (`OrbitEquivRecon` and rigidity of `G₂`). -/
theorem isIsom_of_isComp (h : OrbitEquivRecon G₂ G₂) [IsTopologicalGroup G₂] [T2Space G₂]
    (hb : HasONSBasis G₂) (hc : IsONSComplete G₂) {a : GalMor C₁ C₂ G₁ G₂}
    {b : GalMor C₂ C₃ G₂ G₃} {c : GalMor C₁ C₃ G₁ G₃} (ha : IsIsom a) (hbi : IsIsom b)
    (hab : IsComp a b c) : IsIsom c := by
  obtain ⟨E, t, σ, rfl, hf, ⟨i⟩⟩ := ha
  obtain ⟨F, hF⟩ := hbi
  obtain ⟨e₃, g, τ, rfl, hg, ⟨k⟩⟩ := hF.exists_e₁ h t.e₂
  have hc' : c = GalMor.mk ⟨t.e₁, e₃, g.comp t.f⟩ :=
    isComp_unique hb hc hab (isComp_mk t _ ⟨Iso.refl _⟩)
  refine ⟨E.trans F, _, σ.trans τ, hc'.symm, fun x => ?_, ⟨?_⟩⟩
  · change g (t.f x) = τ (σ x)
    rw [hf, hg]
  · exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.functor k ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight i _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (isoFunctorTrans σ τ).symm

/-! #### Poly-morphisms -/

lemma PolyMor.comp_mono {P P' : PolyMor C₁ C₂ G₁ G₂} {Q Q' : PolyMor C₂ C₃ G₂ G₃}
    (hP : P ⊆ P') (hQ : Q ⊆ Q') : P.comp Q ⊆ P'.comp Q' :=
  fun _ ⟨a, ha, b, hb, h⟩ => ⟨a, hP ha, b, hQ hb, h⟩

/-- **Composition of poly-morphisms is associative** (IUT I, §0; `OrbitEquivRecon` and rigidity
for the middle groups `G₂`, `G₃`). -/
theorem PolyMor.comp_assoc (h₂ : OrbitEquivRecon G₂ G₂) (h₃ : OrbitEquivRecon G₃ G₃)
    [IsTopologicalGroup G₂] [T2Space G₂] (hb₂ : HasONSBasis G₂) (hc₂ : IsONSComplete G₂)
    [IsTopologicalGroup G₃] [T2Space G₃] (hb₃ : HasONSBasis G₃) (hc₃ : IsONSComplete G₃)
    (P : PolyMor C₁ C₂ G₁ G₂) (Q : PolyMor C₂ C₃ G₂ G₃) (R : PolyMor C₃ C₄ G₃ G₄) :
    (P.comp Q).comp R = P.comp (Q.comp R) := by
  ext c
  constructor
  · rintro ⟨ab, ⟨a, ha, b, hb, hab⟩, r, hr, habc⟩
    obtain ⟨bc, hbc⟩ := exists_isComp h₃ b r
    obtain ⟨d, hd⟩ := exists_isComp h₂ a bc
    obtain rfl := isComp_assoc h₂ h₃ hb₂ hc₂ hb₃ hc₃ hab habc hbc hd
    exact ⟨a, ha, bc, ⟨b, hb, r, hr, hbc⟩, hd⟩
  · rintro ⟨a, ha, bc, ⟨b, hb, r, hr, hbc⟩, ha_bc⟩
    obtain ⟨ab, hab⟩ := exists_isComp h₂ a b
    obtain ⟨d, hd⟩ := exists_isComp h₃ ab r
    obtain rfl := isComp_assoc h₂ h₃ hb₂ hc₂ hb₃ hc₃ hab hd hbc ha_bc
    exact ⟨ab, ⟨a, ha, b, hb, hab⟩, r, hr, hd⟩

/-- `{id} ∘ P = P` (`OrbitEquivRecon` and rigidity of `G₁`). -/
theorem PolyMor.id_comp (h : OrbitEquivRecon G₁ G₁) [IsTopologicalGroup G₁] [T2Space G₁]
    (hb : HasONSBasis G₁) (hc : IsONSComplete G₁) (e : C₁ ≌ OrbitObj G₁)
    (P : PolyMor C₁ C₂ G₁ G₂) : PolyMor.comp {GalMor.id C₁ G₁ e} P = P := by
  ext c
  refine ⟨?_, fun hc' => ⟨_, rfl, c, hc', isComp_id_left h e c⟩⟩
  rintro ⟨_, rfl, a, ha, hac⟩
  rwa [← isComp_unique hb hc (isComp_id_left h e a) hac]

/-- `P ∘ {id} = P` (`OrbitEquivRecon` and rigidity of `G₂`). -/
theorem PolyMor.comp_id (h : OrbitEquivRecon G₂ G₂) [IsTopologicalGroup G₂] [T2Space G₂]
    (hb : HasONSBasis G₂) (hc : IsONSComplete G₂) (e : C₂ ≌ OrbitObj G₂)
    (P : PolyMor C₁ C₂ G₁ G₂) : P.comp {GalMor.id C₂ G₂ e} = P := by
  ext c
  refine ⟨?_, fun hc' => ⟨c, hc', _, rfl, isComp_id_right h e c⟩⟩
  rintro ⟨a, ha, _, rfl, hac⟩
  rwa [← isComp_unique hb hc (isComp_id_right h e a) hac]

/-- **`full ∘ full ⊆ full`** (`OrbitEquivRecon` and rigidity of `G₂`). -/
theorem PolyMor.full_comp_full_subset (h : OrbitEquivRecon G₂ G₂) [IsTopologicalGroup G₂]
    [T2Space G₂] (hb : HasONSBasis G₂) (hc : IsONSComplete G₂) :
    (PolyMor.full C₁ C₂ G₁ G₂).comp (PolyMor.full C₂ C₃ G₂ G₃) ⊆ PolyMor.full C₁ C₃ G₁ G₃ :=
  fun _ ⟨_, ha, _, hb', hab⟩ => isIsom_of_isComp h hb hc ha hb' hab

/-- **`full ∘ full_aut = full`** (given an equivalence `C₂ ≌ B(G₂)⁰`). -/
theorem PolyMor.full_comp_full (h : OrbitEquivRecon G₂ G₂) [IsTopologicalGroup G₂]
    [T2Space G₂] (hb : HasONSBasis G₂) (hc : IsONSComplete G₂) (e : C₂ ≌ OrbitObj G₂) :
    (PolyMor.full C₁ C₂ G₁ G₂).comp (PolyMor.full C₂ C₂ G₂ G₂) = PolyMor.full C₁ C₂ G₁ G₂ :=
  (PolyMor.full_comp_full_subset h hb hc).antisymm fun m hm =>
    ⟨m, hm, _, isIsom_id e, isComp_id_right h e m⟩

/-- A poly-automorphism closed under composition stabilises poly-morphisms ending in it:
`(X ∘ A) ∘ A ⊆ X ∘ A`. -/
theorem PolyMor.comp_comp_subset (h : OrbitEquivRecon G₂ G₂) [IsTopologicalGroup G₂]
    [T2Space G₂] (hb : HasONSBasis G₂) (hc : IsONSComplete G₂) (X : PolyMor C₁ C₂ G₁ G₂)
    {A : PolyMor C₂ C₂ G₂ G₂} (hA : A.comp A ⊆ A) : (X.comp A).comp A ⊆ X.comp A := by
  rw [PolyMor.comp_assoc h h hb hc hb hc]
  exact PolyMor.comp_mono subset_rfl hA

end Assoc

/-! ### Capsules (IUT I, §0) -/

section Capsule

variable {J J' J'' : Type}
  {C : J → Type u₁} [∀ j, Category.{v₁} (C j)] {C' : J' → Type u₂} [∀ j, Category.{v₂} (C' j)]
  {C'' : J'' → Type u₃} [∀ j, Category.{v₃} (C'' j)]
  {G : J → Type} [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)]
  {G' : J' → Type} [∀ j, Group (G' j)] [∀ j, TopologicalSpace (G' j)]
  {G'' : J'' → Type} [∀ j, Group (G'' j)] [∀ j, TopologicalSpace (G'' j)]

variable (C C' G G') in
/-- **A morphism of capsules over the injection `ι`** (IUT I, §0): a morphism
`C_j → C'_{ι(j)}` for each `j`. -/
def CapMor (ι : J ↪ J') : Type _ := ∀ j, GalMor (C j) (C' (ι j)) (G j) (G' (ι j))

variable (C C' G G') in
/-- **A morphism of capsules** (IUT I, §0): an injection `ι : J ↪ J'` with a `CapMor` over it. -/
def CapMorS : Type _ := Σ ι : J ↪ J', CapMor C C' G G' ι

/-- `c` is a composite of the capsule morphisms `a`, `b` (componentwise `IsComp`). -/
def CapIsComp {ι : J ↪ J'} {ι' : J' ↪ J''} (a : CapMor C C' G G' ι) (b : CapMor C' C'' G' G'' ι')
    (c : CapMor C C'' G G'' (ι.trans ι')) : Prop :=
  ∀ j, IsComp (a j) (b (ι j)) (c j)

/-- Composites of capsule morphisms exist (`OrbitEquivRecon` for the middle groups). -/
lemma exists_capIsComp (h : ∀ j, OrbitEquivRecon (G' j) (G' j)) {ι : J ↪ J'} {ι' : J' ↪ J''}
    (a : CapMor C C' G G' ι) (b : CapMor C' C'' G' G'' ι') : ∃ c, CapIsComp a b c :=
  ⟨fun j => (exists_isComp (h (ι j)) (a j) (b (ι j))).choose,
    fun j => (exists_isComp (h (ι j)) (a j) (b (ι j))).choose_spec⟩

/-- Composites of capsule morphisms are unique (rigidity of the middle groups). -/
lemma capIsComp_unique [∀ j, IsTopologicalGroup (G' j)] [∀ j, T2Space (G' j)]
    (hb : ∀ j, HasONSBasis (G' j)) (hc : ∀ j, IsONSComplete (G' j)) {ι : J ↪ J'}
    {ι' : J' ↪ J''} {a : CapMor C C' G G' ι} {b : CapMor C' C'' G' G'' ι'}
    {c c' : CapMor C C'' G G'' (ι.trans ι')} (h : CapIsComp a b c) (h' : CapIsComp a b c') :
    c = c' :=
  funext fun j => isComp_unique (hb (ι j)) (hc (ι j)) (h j) (h' j)

variable (C C' G G') in
/-- **A capsule poly-morphism**: a set of morphisms of capsules. -/
abbrev CapPolyMor : Type _ := Set (CapMorS C C' G G')

/-- Composition of capsule poly-morphisms: the set of composites. -/
def CapPolyMor.comp (P : CapPolyMor C C' G G') (Q : CapPolyMor C' C'' G' G'') :
    CapPolyMor C C'' G G'' :=
  {c | ∃ a ∈ P, ∃ b ∈ Q, ∃ m : CapMor C C'' G G'' (a.1.trans b.1), CapIsComp a.2 b.2 m ∧
    c = ⟨_, m⟩}

variable (C C' G G') in
/-- **The capsule-full poly-morphism for `ι`** (IUT I, §0): all families of isomorphisms
`C_j ⥲ C'_{ι(j)}`. -/
def capFull (ι : J ↪ J') : CapPolyMor C C' G G' :=
  {c | ∃ m : CapMor C C' G G' ι, (∀ j, IsIsom (m j)) ∧ c = ⟨ι, m⟩}

variable (C C' G G') in
/-- **The capsule-full poly-isomorphism for the bijection `σ`** (IUT I, §0). -/
def capFullIso (σ : J ≃ J') : CapPolyMor C C' G G' := capFull C C' G G' σ.toEmbedding

/-- **Composites of capsule-full poly-morphisms are capsule-full**: `capFull ι' ∘ capFull ι ⊆
capFull (ι' ∘ ι)` (`OrbitEquivRecon` and rigidity of the middle groups). -/
theorem capFull_comp_subset (h : ∀ j, OrbitEquivRecon (G' j) (G' j))
    [∀ j, IsTopologicalGroup (G' j)] [∀ j, T2Space (G' j)] (hb : ∀ j, HasONSBasis (G' j))
    (hc : ∀ j, IsONSComplete (G' j)) (ι : J ↪ J') (ι' : J' ↪ J'') :
    (capFull C C' G G' ι).comp (capFull C' C'' G' G'' ι') ⊆ capFull C C'' G G'' (ι.trans ι') := by
  rintro _ ⟨_, ⟨m, hm, rfl⟩, _, ⟨n, hn, rfl⟩, k, hk, rfl⟩
  exact ⟨k, fun j => isIsom_of_isComp (h (ι j)) (hb _) (hc _) (hm j) (hn (ι j)) (hk j), rfl⟩

end Capsule

/-! ### Poly-morphisms from prime-strips and capsules of prime-strips (IUT I, Def. 4.1 (vi)) -/

section Strip

variable {V : Type} {C : V → Type u₁} [∀ v, Category.{v₁} (C v)]
  {G : V → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  {C₀ : V → Type u₄} [∀ v, Category.{v₄} (C₀ v)]
  {G₀ : V → Type} [∀ v, Group (G₀ v)] [∀ v, TopologicalSpace (G₀ v)]
  {C' : Type u₂} [Category.{v₂} C'] {G' : Type} [Group G'] [TopologicalSpace G']
  {C'' : Type u₃} [Category.{v₃} C''] {G'' : Type} [Group G''] [TopologicalSpace G'']

variable (C G C' G') in
/-- **A poly-morphism from a strip `{C_v}_v` to `C'`** (IUT I, Definition 4.1 (vi)): a
poly-morphism `C_v → C'` for each `v`. -/
abbrev StripPolyMor : Type _ := ∀ v, PolyMor (C v) C' (G v) G'

/-- Post-composition of a strip poly-morphism with a poly-morphism `C' → C''`. -/
def StripPolyMor.postcomp (P : StripPolyMor C G C' G') (A : PolyMor C' C'' G' G'') :
    StripPolyMor C G C'' G'' :=
  fun v => (P v).comp A

/-- Pre-composition of a strip poly-morphism with poly-morphisms `C₀_v → C_v`. -/
def StripPolyMor.precomp (B : ∀ v, PolyMor (C₀ v) (C v) (G₀ v) (G v))
    (P : StripPolyMor C G C' G') : StripPolyMor C₀ G₀ C' G' :=
  fun v => (B v).comp (P v)

/-- Post-composition is compatible with composition (`OrbitEquivRecon` and rigidity of `G'`,
`G''`). -/
theorem StripPolyMor.postcomp_postcomp {C''' : Type u₄} [Category.{v₄} C'''] {G''' : Type}
    [Group G'''] [TopologicalSpace G'''] (h' : OrbitEquivRecon G' G')
    (h'' : OrbitEquivRecon G'' G'') [IsTopologicalGroup G'] [T2Space G'] (hb' : HasONSBasis G')
    (hc' : IsONSComplete G') [IsTopologicalGroup G''] [T2Space G''] (hb'' : HasONSBasis G'')
    (hc'' : IsONSComplete G'') (P : StripPolyMor C G C' G') (A : PolyMor C' C'' G' G'')
    (B : PolyMor C'' C''' G'' G''') : (P.postcomp A).postcomp B = P.postcomp (A.comp B) :=
  funext fun v => PolyMor.comp_assoc h' h'' hb' hc' hb'' hc'' (P v) A B

/-- Pre- and post-composition commute (`OrbitEquivRecon` and rigidity of the `G_v` and `G'`). -/
theorem StripPolyMor.precomp_postcomp (h : ∀ v, OrbitEquivRecon (G v) (G v))
    (h' : OrbitEquivRecon G' G') [∀ v, IsTopologicalGroup (G v)] [∀ v, T2Space (G v)]
    (hb : ∀ v, HasONSBasis (G v)) (hc : ∀ v, IsONSComplete (G v)) [IsTopologicalGroup G']
    [T2Space G'] (hb' : HasONSBasis G') (hc' : IsONSComplete G')
    (B : ∀ v, PolyMor (C₀ v) (C v) (G₀ v) (G v)) (P : StripPolyMor C G C' G')
    (A : PolyMor C' C'' G' G'') : (P.precomp B).postcomp A = (P.postcomp A).precomp B :=
  funext fun v => PolyMor.comp_assoc (h v) h' (hb v) (hc v) hb' hc' (B v) (P v) A

end Strip

section CapStrip

variable {E V : Type} {C : E → V → Type u₁} [∀ e v, Category.{v₁} (C e v)]
  {G : E → V → Type} [∀ e v, Group (G e v)] [∀ e v, TopologicalSpace (G e v)]
  {C' : Type u₂} [Category.{v₂} C'] {G' : Type} [Group G'] [TopologicalSpace G']
  {C'' : Type u₃} [Category.{v₃} C''] {G'' : Type} [Group G''] [TopologicalSpace G'']

variable (C G C' G') in
/-- **A poly-morphism from a capsule of strips `{{C_{e,v}}_v}_e` to `C'`** (IUT I, Definition 4.1
(vi)): a strip poly-morphism for each `e`. -/
abbrev CapStripPolyMor : Type _ := ∀ e, StripPolyMor (C e) (G e) C' G'

/-- Post-composition of a capsule-strip poly-morphism with a poly-morphism `C' → C''`. -/
def CapStripPolyMor.postcomp (P : CapStripPolyMor C G C' G') (A : PolyMor C' C'' G' G'') :
    CapStripPolyMor C G C'' G'' :=
  fun e => (P e).postcomp A

end CapStrip

/-! ### The model poly-morphisms `φ^NF_v`, `φ^Θell_v` and `φ^NF_⋇` -/

section Model

/-- The prime `ℓ` of initial Θ-data is an odd prime (as in `Iut.HodgeTheater.HodgeTheater`). -/
local instance oddPrimeEllCap (D : InitialThetaData.{0}) : HodgeTheater.OddPrime D.ℓ :=
  ⟨D.prime.ℓ_prime, by have := D.prime.five_le; change 2 < D.prime.ℓ; omega⟩

variable (D : InitialThetaData.{0})

/-- **`φ^NF_v : D_v → D^⊚`** (IUT I, Example 4.3 (ii)): the morphisms `β ∘ φ^NF_{•,v} ∘ α` with
`α ∈ Aut(D_v)` and `β ∈ A` (`A` standing for `Aut_ϵ(D^⊚)`). -/
def phiNF (A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D))
    (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    PolyMor (Dv D v) (dCircModel D) (Piv D v).carrier (PiCK D) :=
  ((PolyMor.full (Dv D v) (Dv D v) (Piv D v).carrier (Piv D v).carrier).comp
    {phiNFDot D v}).comp A

/-- **`φ^Θell_v : D_v → D^⊚±`** (IUT I, Example 6.3 (i)): the morphisms `β ∘ φ^Θell_{•,v} ∘ α`
with `α ∈ Aut(D_v)` and `β ∈ A` (`A` standing for `Aut_csp(D^⊚±)`). -/
def phiEll (A : PolyMor (dCircPmModel D) (dCircPmModel D) (PiXK D) (PiXK D))
    (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    PolyMor (Dv D v) (dCircPmModel D) (Piv D v).carrier (PiXK D) :=
  ((PolyMor.full (Dv D v) (Dv D v) (Piv D v).carrier (Piv D v).carrier).comp
    {phiEllDot D v}).comp A

/-- **`φ^NF_v` is stabilised by `A`** when `A` is closed under composition (IUT I, Example 4.3
(iv): "`φ^NF_1` is stabilized by the action of `Aut_ϵ(C_K)`"). -/
theorem phiNF_comp_subset {A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D)}
    (hA : A.comp A ⊆ A) (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    (phiNF D A v).comp A ⊆ phiNF D A v :=
  PolyMor.comp_comp_subset (orbitEquivRecon_profinite D.orb.CKu.genuinePi1 D.orb.CKu.genuinePi1)
    (hasONSBasis_profinite D.orb.CKu.genuinePi1) (isONSComplete_profinite D.orb.CKu.genuinePi1)
    _ hA

/-- **`φ^Θell_v` is stabilised by `A`** when `A` is closed under composition. -/
theorem phiEll_comp_subset {A : PolyMor (dCircPmModel D) (dCircPmModel D) (PiXK D) (PiXK D)}
    (hA : A.comp A ⊆ A) (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    (phiEll D A v).comp A ⊆ phiEll D A v :=
  PolyMor.comp_comp_subset (orbitEquivRecon_profinite D.orb.XKu.genuinePi1 D.orb.XKu.genuinePi1)
    (hasONSBasis_profinite D.orb.XKu.genuinePi1) (isONSComplete_profinite D.orb.XKu.genuinePi1)
    _ hA

/-- **`φ^NF : D → D^⊚`** on the tautological prime-strip `D = {D_v}_v` (IUT I, Example 4.3 (iv),
`φ^NF_1`; non-archimedean places only). -/
def phiNFStrip (A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D)) :
    StripPolyMor (fun v => Dv D v) (fun v => (Piv D v).carrier) (dCircModel D) (PiCK D) :=
  phiNF D A

/-- **`φ^NF_⋇ : D^⋇ → D^⊚`** (IUT I, Example 4.3 (iv)): on the capsule `D^⋇ = {D_j}_{j ∈ F_ℓ^⋇}`
of copies of the tautological prime-strip, the component at `j` is `φ^NF_1` post-composed with the
poly-action `act j` of `j` on `D^⊚`. -/
def phiNFStar (A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D))
    (act : HodgeTheater.FlStar D.ℓ → PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D)) :
    CapStripPolyMor (fun (_ : HodgeTheater.FlStar D.ℓ) v => Dv D v)
      (fun _ v => (Piv D v).carrier) (dCircModel D) (PiCK D) :=
  fun j => (phiNFStrip D A).postcomp (act j)

/-- **Equivariance of `φ^NF_⋇`** (IUT I, Example 4.3 (iv)): if the poly-action is multiplicative
at `j, j'` (`act j' ∘ act j = act (j j')`), post-composing the component at `j` with `act j'` gives
the component at `j j'`. -/
theorem phiNFStar_postcomp (A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D))
    (act : HodgeTheater.FlStar D.ℓ → PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D))
    (j j' : HodgeTheater.FlStar D.ℓ) (hact : (act j).comp (act j') = act (j * j')) :
    (phiNFStar D A act j).postcomp (act j') = phiNFStar D A act (j * j') := by
  have hr := orbitEquivRecon_profinite D.orb.CKu.genuinePi1 D.orb.CKu.genuinePi1
  have hb := hasONSBasis_profinite D.orb.CKu.genuinePi1
  have hc := isONSComplete_profinite D.orb.CKu.genuinePi1
  exact (StripPolyMor.postcomp_postcomp hr hr hb hc hb hc _ _ _).trans
    (congrArg (StripPolyMor.postcomp (phiNFStrip D A)) hact)

/-- **The component of `φ^NF_⋇` at `1` lies in `φ^NF_1`** when `act 1 ⊆ A` and `A` is closed
under composition. -/
theorem phiNFStar_one_subset {A : PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D)}
    (hA : A.comp A ⊆ A)
    {act : HodgeTheater.FlStar D.ℓ → PolyMor (dCircModel D) (dCircModel D) (PiCK D) (PiCK D)}
    (h1 : act 1 ⊆ A) (v : FinitePlace ↥(fieldOfModuli D.F D.E)) :
    phiNFStar D A act 1 v ⊆ phiNF D A v :=
  (PolyMor.comp_mono subset_rfl h1).trans (phiNF_comp_subset D hA v)

end Model

end Theater

end Multiradial

end Iut
