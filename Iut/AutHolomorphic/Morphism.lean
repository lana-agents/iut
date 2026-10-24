/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.OfCover

/-!
# Composition and corestriction of morphisms of Aut-holomorphic spaces

[AbsTopIII] Definition 2.1 (ii) defines morphisms of Aut-holomorphic spaces as local
homeomorphisms that, on every connected open `U` mapped homeomorphically onto some `V`, induce a
bijection `A_X(U) ≅ A_Y(V)` by conjugation. Here:

* `imageHomeo`: a local homeomorphism that is injective on an open `U` maps `U` homeomorphically
  onto `φ(U)`;
* `IsMorphism.comp`: morphisms compose;
* `IsMorphism.codRestrict`: a morphism with values in an open `W ⊆ Y` is a morphism into the
  Aut-holomorphic space `W` (`AutHolStr.restrict`); `IsMorphism.restrict`: restriction to an
  open subset of the source;
* `isIso_of_isMorphism`: a homeomorphism onto an open `W ⊆ Y` that is a morphism into `Y` is an
  isomorphism onto `W`; `isIso_openImageHomeo`: restricting in two steps.
-/

namespace Iut

namespace AutHol

open Set Topology TopologicalSpace

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {A : AutHolStr X} {B : AutHolStr Y} {C : AutHolStr Z}

/-- A local homeomorphism `φ` that is injective on an open `U` maps `U` homeomorphically onto
`φ(U)`. -/
noncomputable def imageHomeo {φ : X → Y} (hφ : IsLocalHomeomorph φ) {U : Set X} (hU : IsOpen U)
    (hinj : InjOn φ U) : U ≃ₜ (φ '' U) :=
  ((hφ.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph).isOpenEmbedding_of_injective
    (fun x y h => Subtype.ext (hinj x.2 y.2 h))).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext y; simp))

@[simp]
theorem imageHomeo_apply {φ : X → Y} (hφ : IsLocalHomeomorph φ) {U : Set X} (hU : IsOpen U)
    (hinj : InjOn φ U) (x : U) : (imageHomeo hφ hU hinj x : Y) = φ x := rfl

theorem injOn_of_homeomorph {φ : X → Y} {U : Set X} {V : Set Y} (e : U ≃ₜ V)
    (he : ∀ x : U, (e x : Y) = φ x) : InjOn φ U := by
  intro x hx y hy hxy
  have : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext (by rw [he, he]; exact hxy)
  exact congrArg Subtype.val (e.injective this)

/-- **Morphisms of Aut-holomorphic spaces compose.** -/
theorem IsMorphism.comp {φ : X → Y} {ψ : Y → Z} (hψ : IsMorphism B C ψ)
    (hφ : IsMorphism A B φ) : IsMorphism A C (ψ ∘ φ) := by
  refine ⟨hψ.1.comp hφ.1, ?_⟩
  intro U hU W hW e he
  have hinj : InjOn φ U := by
    intro x hx y hy hxy
    exact injOn_of_homeomorph e he hx hy (by simp [hxy])
  let V : Opens Y := ⟨φ '' U, hφ.1.isOpenMap _ U.2⟩
  let e₁ : U ≃ₜ V := imageHomeo hφ.1 U.2 hinj
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
  rw [hψ.2 V hV W hW e₂ he₂, hφ.2 U hU V hV e₁ he₁, map_conj_trans]
  congr
  ext x
  simp [e₂]

/-- **Corestriction**: a morphism with values in an open `W` is a morphism into the
Aut-holomorphic space `W`. -/
theorem IsMorphism.codRestrict {φ : X → Y} (hφ : IsMorphism A B φ) (W : Opens Y)
    (h : ∀ x, φ x ∈ W) : IsMorphism A (B.restrict W) (fun x => (⟨φ x, h x⟩ : W)) := by
  refine ⟨IsLocalHomeomorph.of_comp (g := Subtype.val) hφ.1 W.isOpenEmbedding'.isLocalHomeomorph
    (hφ.1.continuous.subtype_mk _), ?_⟩
  intro U hU V _ e he
  let e' : U ≃ₜ AutHolStr.openImage W V := e.trans (AutHolStr.openImageHomeo W V)
  have he' : ∀ x : U, (e' x : Y) = φ x := by
    intro x
    change ((e x : W) : Y) = φ x
    rw [he]
  have hV' := isConnected_of_homeomorph e' hU
  change (B.aut (AutHolStr.openImage W V)).map
    (conj (AutHolStr.openImageHomeo W V).symm).toMonoidHom = _
  rw [hφ.2 U hU _ hV' e' he', map_conj_trans]
  congr
  ext x
  simp [e']

/-- **Restriction to an open subset of the source.** -/
theorem IsMorphism.restrict {φ : X → Y} (hφ : IsMorphism A B φ) (W : Opens X) :
    IsMorphism (A.restrict W) B (fun x : W => φ x) :=
  hφ.comp (AutHolStr.isMorphism_val A W)

/-- A homeomorphism onto an open `W ⊆ Y` that is a morphism into `Y` is an isomorphism onto the
Aut-holomorphic space `W`. -/
theorem isIso_of_isMorphism {φ : X → Y} (hφ : IsMorphism A B φ) {W : Opens Y} (e : X ≃ₜ W)
    (he : ∀ x, (e x : Y) = φ x) : IsIso A (B.restrict W) e := by
  have h := hφ.codRestrict W fun x => by rw [← he]; exact (e x).2
  have : (fun x => (⟨φ x, by rw [← he]; exact (e x).2⟩ : W)) = ⇑e := by
    funext x
    exact Subtype.ext (he x).symm
  unfold IsIso
  rwa [← this]

/-- **Restriction in two steps**: the open `V ⊆ W ⊆ X`, as an Aut-holomorphic space restricted
from `W`, is isomorphic to `V` as an open subset of `X`. -/
theorem isIso_openImageHomeo (A : AutHolStr X) (W : Opens X) (V : Opens W) :
    IsIso ((A.restrict W).restrict V) (A.restrict (AutHolStr.openImage W V))
      (AutHolStr.openImageHomeo W V) :=
  isIso_of_isMorphism ((AutHolStr.isMorphism_val A W).comp
    (AutHolStr.isMorphism_val (A.restrict W) V)) _ fun _ => rfl

end AutHol

end Iut
