/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EqToHom

/-!
# Self-equivalences isomorphic to the identity ([EtTh], Lemma 5.11)

[EtTh], Lemma 5.11 ("Non-category-theoreticity of Particular Morphisms in an Abstract Equivalence
Class"): for distinct objects `G, H, I` of a category `E` and automorphisms `α_G, α_H, α_I`,
there is a self-equivalence `Ξ` of `E`, the identity on objects, isomorphic to the identity via an
isomorphism with components `α_G, α_H, α_I` at `G, H, I` and the identity elsewhere; in particular
`Ξ` maps `f : G → H` to `α_H ∘ f ∘ α_G⁻¹` and `g : G → G` to `α_G ∘ g ∘ α_G⁻¹`.

We prove the general form: for **any** family of automorphisms `α_J` (`J ∈ Ob(E)`),
`conjFamilyFunctor α` (`f ↦ α_J⁻¹ ≫ f ≫ α_{J'}` in diagrammatic order, i.e.
`α_{J'} ∘ f ∘ α_J⁻¹`) is a self-equivalence, the identity on objects, with
`conjFamilyIso α : 𝟭 E ≅ conjFamilyFunctor α` whose component at `J` is `α_J`. Lemma 5.11 is the
case of the family `lemma511Family` which is `α_G, α_H, α_I` at
`G, H, I` and the identity elsewhere (`lemma511`).

This is the "general nonsense" behind [EtTh], Corollary 5.12 (the indeterminacy of projective
systems of theta environments up to multiplication by elements of the base field), cited in IUT III,
Remark 2.1.1.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe v u

variable {E : Type u} [Category.{v} E]

/-- **The self-functor conjugating every morphism by a family of automorphisms**:
`f : J ⟶ J'` goes to `α_J⁻¹ ≫ f ≫ α_{J'}`. -/
@[simps obj]
def conjFamilyFunctor (α : ∀ J : E, J ≅ J) : E ⥤ E where
  obj J := J
  map {J J'} f := (α J).inv ≫ f ≫ (α J').hom
  map_id J := by simp
  map_comp f g := by simp

@[simp] lemma conjFamilyFunctor_map (α : ∀ J : E, J ≅ J) {J J' : E} (f : J ⟶ J') :
    (conjFamilyFunctor α).map f = (α J).inv ≫ f ≫ (α J').hom := rfl

/-- **The isomorphism `𝟭 ≅ conjFamilyFunctor α`** with component `α_J` at `J`. -/
@[simps!]
def conjFamilyIso (α : ∀ J : E, J ≅ J) : 𝟭 E ≅ conjFamilyFunctor α :=
  NatIso.ofComponents α (fun _ => (Iso.hom_inv_id_assoc _ _).symm)

instance (α : ∀ J : E, J ≅ J) : (conjFamilyFunctor α).IsEquivalence :=
  Functor.isEquivalence_of_iso (conjFamilyIso α)

/-- The family of [EtTh], Lemma 5.11: `α_G, α_H, α_I` at the (distinct) objects `G, H, I`, the
identity elsewhere. -/
noncomputable def lemma511Family (G H I : E) (αG : G ≅ G) (αH : H ≅ H) (αI : I ≅ I) :
    ∀ J : E, J ≅ J := by
  classical
  exact fun J =>
    if hG : J = G then eqToIso hG ≪≫ αG ≪≫ eqToIso hG.symm
    else if hH : J = H then eqToIso hH ≪≫ αH ≪≫ eqToIso hH.symm
    else if hI : J = I then eqToIso hI ≪≫ αI ≪≫ eqToIso hI.symm
    else Iso.refl J

lemma lemma511Family_G (G H I : E) (αG : G ≅ G) (αH : H ≅ H) (αI : I ≅ I) :
    lemma511Family G H I αG αH αI G = αG := by
  simp [lemma511Family]

lemma lemma511Family_H {G H I : E} (hGH : G ≠ H) (αG : G ≅ G) (αH : H ≅ H) (αI : I ≅ I) :
    lemma511Family G H I αG αH αI H = αH := by
  simp [lemma511Family, hGH.symm]

lemma lemma511Family_I {G H I : E} (hGI : G ≠ I) (hHI : H ≠ I) (αG : G ≅ G) (αH : H ≅ H)
    (αI : I ≅ I) : lemma511Family G H I αG αH αI I = αI := by
  simp [lemma511Family, hGI.symm, hHI.symm]

lemma lemma511Family_other {G H I J : E} (hG : J ≠ G) (hH : J ≠ H) (hI : J ≠ I) (αG : G ≅ G)
    (αH : H ≅ H) (αI : I ≅ I) : lemma511Family G H I αG αH αI J = Iso.refl J := by
  simp [lemma511Family, hG, hH, hI]

/-- **[EtTh], Lemma 5.11**: for distinct objects `G, H, I` and automorphisms `α_G, α_H, α_I`,
the self-equivalence `Ξ = conjFamilyFunctor (lemma511Family …)` (the identity on objects) is
isomorphic to the identity via `conjFamilyIso`, whose components are `α_G, α_H, α_I` at `G, H, I`
and the identity at every other object; `Ξ` maps `f : G → H` to `α_H ∘ f ∘ α_G⁻¹` and `g : G → G`
to `α_G ∘ g ∘ α_G⁻¹`. -/
theorem lemma511 {G H I : E} (hGH : G ≠ H) (hGI : G ≠ I) (hHI : H ≠ I) (αG : G ≅ G)
    (αH : H ≅ H) (αI : I ≅ I) :
    (conjFamilyIso (lemma511Family G H I αG αH αI)).app G = αG ∧
      (conjFamilyIso (lemma511Family G H I αG αH αI)).app H = αH ∧
      (conjFamilyIso (lemma511Family G H I αG αH αI)).app I = αI ∧
      (∀ J, J ≠ G → J ≠ H → J ≠ I →
        (conjFamilyIso (lemma511Family G H I αG αH αI)).app J = Iso.refl J) ∧
      (∀ f : G ⟶ H, (conjFamilyFunctor (lemma511Family G H I αG αH αI)).map f =
        αG.inv ≫ f ≫ αH.hom) ∧
      (∀ g : G ⟶ G, (conjFamilyFunctor (lemma511Family G H I αG αH αI)).map g =
        αG.inv ≫ g ≫ αG.hom) :=
  ⟨lemma511Family_G G H I αG αH αI, lemma511Family_H hGH αG αH αI,
    lemma511Family_I hGI hHI αG αH αI, fun _ hG hH hI => lemma511Family_other hG hH hI αG αH αI,
    fun f => by rw [conjFamilyFunctor_map, lemma511Family_G, lemma511Family_H hGH],
    fun g => by rw [conjFamilyFunctor_map, lemma511Family_G]⟩

end Frobenioid

end Iut
