/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Complex.Basic

/-!
# Aut-holomorphic spaces ([AbsTopIII], Definition 2.1(i), (ii))

[AbsTopIII], §2, replaces the "model-explicit" notion of a holomorphic structure (local comparison
with a fixed copy of `ℂ`) by a "model-implicit" one (Remark 2.7.4): an **Aut-holomorphic
structure** on a topological space `X` is an assignment `U ↦ A_X(U)`, for `U ⊆ X` a connected open
subset, of a subgroup `A_X(U) ⊆ Aut(U^top)` of the group of self-homeomorphisms of `U`
(Definition 2.1(i)). For a Riemann surface `X`, `A_X(U) = Aut^hol(U)`.

## Contents

* `AutHolStr X`: an Aut-holomorphic structure (the assignment is recorded on all open subsets;
  only its values on connected ones enter the definitions of morphisms, as in Definition 2.1).
* `LocalStructure X` and `IsLocalMorphism`: the `(𝒰, 𝒱)`-local morphisms of Definition 2.1(ii) (a
  local homeomorphism `φ` such that for every `U ∈ 𝒰` mapped homeomorphically onto some `V ∈ 𝒱`,
  conjugation by `φ|_U` carries `A_X(U)` onto `A_Y(V)`); `IsMorphism` is the case where `𝒰`, `𝒱`
  consist of all connected open subsets.
* `IsIso`: isomorphisms of Aut-holomorphic spaces (homeomorphisms that are morphisms), closed under
  identity, inverse and composition (`IsIso.refl`, `IsIso.symm`, `IsIso.trans`; cf. Remark 2.3.3).
* `AutHolStr.global`: the group `A_X(X)` of global automorphisms, viewed inside `Aut(X^top)`; an
  isomorphism `φ` of connected Aut-holomorphic spaces conjugates `A_X(X)` onto `A_Y(Y)`
  (`IsIso.global_eq`).
* `ofEmbedding ι`: the Aut-holomorphic structure determined by a map `ι : X → ℂ` (for an open
  embedding, the Riemann surface structure of an open subset of `ℂ`): `A(U)` consists of the
  homeomorphisms `g` of `U` such that `g` and `g⁻¹` are given in the coordinate `ι` by functions
  holomorphic on `ι(U)`.

Not formalised here: co-orientations and co-holomorphicizations (Definition 2.1(iii), (iv)), which
use the local fundamental groups `Orn(Z, p) = lim π₁(W ∖ {p})^ab`.
-/

namespace Iut

namespace AutHol

open TopologicalSpace Set

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ### Conjugation by homeomorphisms -/

/-- **Conjugation** `g ↦ e ∘ g ∘ e⁻¹` by a homeomorphism `e : X ≃ₜ Y`. -/
def conj (e : X ≃ₜ Y) : (X ≃ₜ X) ≃* (Y ≃ₜ Y) where
  toFun g := (e.symm.trans g).trans e
  invFun g := (e.trans g).trans e.symm
  left_inv g := by ext x; simp
  right_inv g := by ext x; simp
  map_mul' g h := by ext x; simp

@[simp]
theorem conj_apply (e : X ≃ₜ Y) (g : X ≃ₜ X) (y : Y) : conj e g y = e (g (e.symm y)) := rfl

theorem conj_trans (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) :
    (conj (e.trans e')).toMonoidHom = (conj e').toMonoidHom.comp (conj e).toMonoidHom := by
  ext g z
  rfl

theorem conj_symm_comp (e : X ≃ₜ Y) :
    (conj e.symm).toMonoidHom.comp (conj e).toMonoidHom = MonoidHom.id _ := by
  ext g x
  simp

theorem map_conj_trans (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) (H : Subgroup (X ≃ₜ X)) :
    (H.map (conj e).toMonoidHom).map (conj e').toMonoidHom = H.map (conj (e.trans e')).toMonoidHom
    := by
  rw [Subgroup.map_map, conj_trans]

theorem map_conj_symm (e : X ≃ₜ Y) (H : Subgroup (X ≃ₜ X)) :
    (H.map (conj e).toMonoidHom).map (conj e.symm).toMonoidHom = H := by
  rw [Subgroup.map_map, conj_symm_comp, Subgroup.map_id]

theorem mem_map_conj {e : X ≃ₜ Y} {H : Subgroup (X ≃ₜ X)} {g : Y ≃ₜ Y} :
    g ∈ H.map (conj e).toMonoidHom ↔ conj e.symm g ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : conj e.symm (conj e h) = h := by ext x; simp
    change conj e.symm (conj e h) ∈ H
    rwa [this]
  · intro hg
    refine ⟨_, hg, ?_⟩
    ext y
    simp

/-! ### Aut-holomorphic structures -/

/-- **An Aut-holomorphic structure** on `X` ([AbsTopIII], Definition 2.1(i)): an assignment of a
subgroup `A_X(U) ⊆ Aut(U^top)` to each open `U ⊆ X`. Only the values on connected `U` enter the
notion of morphism (`IsMorphism`), as in loc. cit. -/
structure AutHolStr (X : Type*) [TopologicalSpace X] where
  /-- The group `A_X(U)` of distinguished self-homeomorphisms of `U`. -/
  aut : ∀ U : Opens X, Subgroup (U ≃ₜ U)

/-- A **local structure** on `X` ([AbsTopIII], Definition 2.1(i)): a collection of connected open
subsets forming a basis of the topology, and containing every connected open subset of each of
its members. -/
structure LocalStructure (X : Type*) [TopologicalSpace X] where
  /-- The members of the local structure. -/
  sets : Set (Opens X)
  isConnected : ∀ U ∈ sets, IsConnected (U : Set X)
  isBasis : IsTopologicalBasis ((↑) '' sets : Set (Set X))
  mem_of_le : ∀ U ∈ sets, ∀ V : Opens X, V ≤ U → IsConnected (V : Set X) → V ∈ sets

/-- **`(𝒰, 𝒱)`-local morphisms** ([AbsTopIII], Definition 2.1(ii)): a local homeomorphism `φ` such
that, whenever `U ∈ 𝒰` is mapped homeomorphically by `φ` onto `V ∈ 𝒱`, conjugation by `φ|_U`
induces a bijection `A_X(U) ≅ A_Y(V)`. -/
def IsLocalMorphism (A : AutHolStr X) (B : AutHolStr Y) (𝒰 : Set (Opens X)) (𝒱 : Set (Opens Y))
    (φ : X → Y) : Prop :=
  IsLocalHomeomorph φ ∧ ∀ U ∈ 𝒰, ∀ V ∈ 𝒱, ∀ e : U ≃ₜ V, (∀ x : U, (e x : Y) = φ x) →
    B.aut V = (A.aut U).map (conj e).toMonoidHom

/-- The connected open subsets. -/
def connOpens (X : Type*) [TopologicalSpace X] : Set (Opens X) := {U | IsConnected (U : Set X)}

/-- **Morphisms of Aut-holomorphic spaces** ([AbsTopIII], Definition 2.1(ii)): the `(𝒰, 𝒱)`-local
morphisms for `𝒰`, `𝒱` the sets of all connected open subsets. -/
def IsMorphism (A : AutHolStr X) (B : AutHolStr Y) (φ : X → Y) : Prop :=
  IsLocalMorphism A B (connOpens X) (connOpens Y) φ

/-- **Isomorphisms of Aut-holomorphic spaces**: homeomorphisms which are morphisms. -/
def IsIso (A : AutHolStr X) (B : AutHolStr Y) (φ : X ≃ₜ Y) : Prop := IsMorphism A B φ

theorem isConnected_of_homeomorph {U : Set X} {V : Set Y} (e : U ≃ₜ V) (hU : IsConnected U) :
    IsConnected V := by
  rw [isConnected_iff_connectedSpace] at hU ⊢
  exact e.surjective.connectedSpace e.continuous

namespace IsIso

variable {A : AutHolStr X} {B : AutHolStr Y} {C : AutHolStr Z}

/-- The isomorphism condition, for a homeomorphism: for every connected open `U` and every open `V`
onto which `φ` maps `U`, conjugation carries `A_X(U)` onto `A_Y(V)`. -/
theorem iff (φ : X ≃ₜ Y) : IsIso A B φ ↔ ∀ U : Opens X, IsConnected (U : Set X) →
    ∀ V : Opens Y, ∀ e : U ≃ₜ V, (∀ x : U, (e x : Y) = φ x) →
      B.aut V = (A.aut U).map (conj e).toMonoidHom := by
  constructor
  · intro h U hU V e he
    exact h.2 U hU V (isConnected_of_homeomorph e hU) e he
  · intro h
    exact ⟨φ.isLocalHomeomorph, fun U hU V _ e he => h U hU V e he⟩

theorem refl (A : AutHolStr X) : IsIso A A (Homeomorph.refl X) := by
  rw [iff]
  intro U _ V e he
  have hUV : U = V := by
    ext x
    constructor
    · intro hx
      have := (e ⟨x, hx⟩).2
      rwa [he] at this
    · intro hx
      have h1 := he (e.symm ⟨x, hx⟩)
      simp only [Homeomorph.apply_symm_apply, Homeomorph.refl_apply, id_eq] at h1
      rw [h1]
      exact (e.symm ⟨x, hx⟩).2
  subst hUV
  have he' : e = Homeomorph.refl U := by
    ext x
    exact he x
  subst he'
  ext g
  rw [mem_map_conj]
  rfl

theorem symm {φ : X ≃ₜ Y} (h : IsIso A B φ) : IsIso B A φ.symm := by
  rw [iff] at h ⊢
  intro V hV U e he
  have hU : IsConnected (U : Set X) := isConnected_of_homeomorph e hV
  have he' : ∀ x : U, (e.symm x : Y) = φ x := by
    intro x
    have h1 := he (e.symm x)
    rw [Homeomorph.apply_symm_apply] at h1
    rw [h1, Homeomorph.apply_symm_apply]
  rw [h U hU V e.symm he', map_conj_trans]
  have : e.symm.trans e = Homeomorph.refl U := by ext; simp
  rw [this]
  ext g
  rw [mem_map_conj]
  rfl

theorem trans {φ : X ≃ₜ Y} {ψ : Y ≃ₜ Z} (h : IsIso A B φ) (h' : IsIso B C ψ) :
    IsIso A C (φ.trans ψ) := by
  rw [iff] at h h' ⊢
  intro U hU W e he
  let V : Opens Y := ⟨φ '' U, φ.isOpenMap _ U.2⟩
  let e₁ : U ≃ₜ V := φ.image U
  have he₁ : ∀ x : U, (e₁ x : Y) = φ x := fun _ => rfl
  let e₂ : V ≃ₜ W := e₁.symm.trans e
  have he₂ : ∀ y : V, (e₂ y : Z) = ψ y := by
    intro y
    change (e (e₁.symm y) : Z) = ψ y
    rw [he]
    have : (e₁ (e₁.symm y) : Y) = y := by rw [Homeomorph.apply_symm_apply]
    rw [← this, he₁]
    rfl
  have hV : IsConnected (V : Set Y) := isConnected_of_homeomorph e₁ hU
  rw [h' V hV W e₂ he₂, h U hU V e₁ he₁, map_conj_trans]
  congr
  ext x
  simp [e₂]

end IsIso

/-! ### The global automorphism group `A_X(X)` -/

/-- `X` as the open subset `⊤`. -/
def topHomeo (X : Type*) [TopologicalSpace X] : (⊤ : Opens X) ≃ₜ X where
  toFun x := x.1
  invFun x := ⟨x, by simp⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

namespace AutHolStr

/-- **The group `A_X(X)`** of global automorphisms, inside `Aut(X^top)`. -/
def global (A : AutHolStr X) : Subgroup (X ≃ₜ X) :=
  (A.aut ⊤).map (conj (topHomeo X)).toMonoidHom

theorem mem_global {A : AutHolStr X} {g : X ≃ₜ X} :
    g ∈ A.global ↔ conj (topHomeo X).symm g ∈ A.aut ⊤ :=
  mem_map_conj

end AutHolStr

/-- **An isomorphism of connected Aut-holomorphic spaces conjugates `A_X(X)` onto `A_Y(Y)`.** -/
theorem IsIso.global_eq {A : AutHolStr X} {B : AutHolStr Y} {φ : X ≃ₜ Y} (h : IsIso A B φ)
    (hX : IsConnected (univ : Set X)) : B.global = A.global.map (conj φ).toMonoidHom := by
  rw [IsIso.iff] at h
  let e : (⊤ : Opens X) ≃ₜ (⊤ : Opens Y) := (topHomeo X).trans (φ.trans (topHomeo Y).symm)
  have hX' : IsConnected ((⊤ : Opens X) : Set X) := by simpa using hX
  have := h ⊤ hX' ⊤ e (fun _ => rfl)
  rw [AutHolStr.global, AutHolStr.global, this, map_conj_trans, map_conj_trans]
  congr

/-! ### Aut-holomorphic structures from coordinates in `ℂ` -/

/-- `g : U → U` is **holomorphic in the coordinate `ι : X → ℂ`**: it is given by a function
holomorphic on `ι(U)`. -/
def HolIn (ι : X → ℂ) (U : Set X) (g : U → U) : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ι '' U) ∧ ∀ x : U, ι (g x) = F (ι x)

omit [TopologicalSpace X] in
theorem HolIn.id (ι : X → ℂ) (U : Set X) : HolIn ι U _root_.id :=
  ⟨_root_.id, differentiableOn_id, fun _ => rfl⟩

omit [TopologicalSpace X] in
theorem HolIn.comp {ι : X → ℂ} {U : Set X} {g h : U → U} (hg : HolIn ι U g) (hh : HolIn ι U h) :
    HolIn ι U (g ∘ h) := by
  obtain ⟨F, hF, hFg⟩ := hg
  obtain ⟨G, hG, hGh⟩ := hh
  refine ⟨F ∘ G, hF.comp hG ?_, fun x => by simp [hFg, hGh]⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← hGh ⟨x, hx⟩]
  exact ⟨_, (h ⟨x, hx⟩).2, rfl⟩

/-- **The Aut-holomorphic structure in a coordinate `ι : X → ℂ`** ([AbsTopIII], Definition 2.1(i)
for an open subset of `ℂ`, or for `X` embedded in `ℂ` by an open embedding `ι`): `A(U)` consists
of the homeomorphisms `g` of `U` with `g`, `g⁻¹` holomorphic in the coordinate `ι`. -/
def ofEmbedding (ι : X → ℂ) : AutHolStr X where
  aut U :=
    { carrier := {g | HolIn ι U g ∧ HolIn ι U g.symm}
      mul_mem' := fun hg hh => ⟨hg.1.comp hh.1, hh.2.comp hg.2⟩
      one_mem' := ⟨HolIn.id ι U, HolIn.id ι U⟩
      inv_mem' := fun hg => ⟨hg.2, hg.1⟩ }

theorem mem_ofEmbedding_aut {ι : X → ℂ} {U : Opens X} {g : U ≃ₜ U} :
    g ∈ (ofEmbedding ι).aut U ↔ HolIn ι U g ∧ HolIn ι U g.symm := Iff.rfl

end AutHol

end Iut
