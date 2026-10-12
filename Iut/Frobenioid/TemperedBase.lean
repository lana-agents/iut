/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Topology.Algebra.Group.Basic

/-!
# The base category `B^temp(Π)⁰` of a tempered Frobenioid ([EtTh], §3)

For a topological group `Π` (the tempered fundamental group `Π^tp_X`), [EtTh] §3 takes as base
category of the tempered Frobenioid the category `B^temp(Π)⁰` of *connected* objects of
`B^temp(Π)` (discrete sets with a continuous `Π`-action): the transitive `Π`-sets with open
stabilizers, i.e. (up to equivalence) the quotients `Π/H` by open subgroups `H`, with
`Π`-equivariant maps. In Galois-theoretic terms these are the connected tempered coverings of
`X`.

`OrbitObj Π` is this category, presented by the open subgroups (so that it is small). We prove
the two category-theoretic hypotheses of [FrdI], Definition 1.1(iv):

* `OrbitObj.isConnected`: it is connected (every object maps to the terminal object `Π/Π`);
* `OrbitObj.totallyEpimorphic`: every morphism is an epimorphism (equivariant maps between
  transitive `Π`-sets are surjective, `OrbitHom.surjective`);

and the description of FSM-morphisms used by the monoids on it: `OrbitHom.bijective_of_isFSM`
(a monomorphism is injective, `OrbitHom.injective_of_mono`, so FSM-morphisms are bijections).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory

universe u

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- **The connected objects of `B^temp(G)`**: the transitive `G`-sets `G/H` for open subgroups
`H` (the connected tempered coverings, [EtTh] §3). -/
structure OrbitObj where
  /-- The open subgroup `H`. -/
  H : Subgroup G
  isOpen : IsOpen (H : Set G)

variable {G}

/-- **Morphisms of `B^temp(G)⁰`**: `G`-equivariant maps `G/H → G/H'`. -/
@[ext]
structure OrbitHom (A B : OrbitObj G) where
  /-- The underlying map. -/
  toFun : G ⧸ A.H → G ⧸ B.H
  map_smul : ∀ (g : G) (x : G ⧸ A.H), toFun (g • x) = g • toFun x

instance : Category (OrbitObj G) where
  Hom := OrbitHom
  id A := ⟨id, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun x y => by simp [f.map_smul, g.map_smul]⟩

namespace OrbitHom

variable {A B C : OrbitObj G}

@[simp] lemma id_toFun (A : OrbitObj G) : (𝟙 A : A ⟶ A).toFun = id := rfl

@[simp] lemma comp_toFun (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).toFun = g.toFun ∘ f.toFun := rfl

@[ext] lemma hom_ext {f g : A ⟶ B} (h : f.toFun = g.toFun) : f = g := OrbitHom.ext h

lemma mk_eq_smul (g : G) :
    (QuotientGroup.mk g : G ⧸ A.H) = g • (QuotientGroup.mk 1 : G ⧸ A.H) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

lemma apply_mk (f : A ⟶ B) (g : G) :
    f.toFun (QuotientGroup.mk g) = g • f.toFun (QuotientGroup.mk 1) := by
  rw [mk_eq_smul, f.map_smul]

/-- `f(gH) = g·g₀·H'` for any representative `g₀` of `f(H)`. -/
lemma apply_mk_of_eq (f : A ⟶ B) {g₀ : G}
    (h₀ : f.toFun (QuotientGroup.mk 1) = QuotientGroup.mk g₀) (g : G) :
    f.toFun (QuotientGroup.mk g) = QuotientGroup.mk (g * g₀) := by
  rw [apply_mk, h₀, MulAction.Quotient.smul_mk, smul_eq_mul]

/-- **Equivariant maps between transitive `G`-sets are surjective.** -/
theorem surjective (f : A ⟶ B) : Function.Surjective f.toFun := by
  intro y
  obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (f.toFun (QuotientGroup.mk 1))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨QuotientGroup.mk (g * g₀⁻¹), ?_⟩
  rw [apply_mk_of_eq f hg₀.symm, inv_mul_cancel_right]

instance epi (f : A ⟶ B) : Epi f where
  left_cancellation g h e := by
    ext y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact congrFun (congrArg OrbitHom.toFun e) x

end OrbitHom

namespace OrbitObj

/-- The terminal object `G/G` (the base `X` itself). -/
abbrev top : OrbitObj G := ⟨⊤, isOpen_univ⟩

/-- The structure morphism to `G/G`. -/
def toTop (A : OrbitObj G) : A ⟶ top where
  toFun _ := QuotientGroup.mk 1
  map_smul g _ := by
    change (QuotientGroup.mk 1 : G ⧸ (⊤ : Subgroup G)) = g • QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk]
    exact QuotientGroup.eq.2 (Subgroup.mem_top _)

/-- **`B^temp(G)⁰` is connected** ([FrdI], Definition 1.1(iv)). -/
instance isConnected : IsConnected (OrbitObj G) :=
  haveI : Nonempty (OrbitObj G) := ⟨top⟩
  zigzag_isConnected fun A B => Zigzag.of_hom_inv (toTop A) (toTop B)

/-- **`B^temp(G)⁰` is totally epimorphic** ([FrdI], Definition 1.1(iv)). -/
instance totallyEpimorphic : TotallyEpimorphic (OrbitObj G) where
  epi f := OrbitHom.epi f

end OrbitObj

/-! ### Monomorphisms and FSM-morphisms -/

section Mono

variable [IsTopologicalGroup G]

/-- The stabilizer of a point of `G/H` is open. -/
lemma isOpen_stabilizer (A : OrbitObj G) (x : G ⧸ A.H) :
    IsOpen (MulAction.stabilizer G x : Set G) := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
  have : (MulAction.stabilizer G (QuotientGroup.mk g₀ : G ⧸ A.H) : Set G) =
      (fun g => (g * g₀)⁻¹ * g₀) ⁻¹' (A.H : Set G) := by
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAction.Quotient.smul_mk,
      smul_eq_mul, Set.mem_preimage]
    rw [QuotientGroup.eq]
  rw [this]
  exact A.isOpen.preimage (by fun_prop)

/-- The equivariant map `G/K → X`, `gK ↦ g·x`, for `K` fixing `x`. -/
def pointHom (C A : OrbitObj G) (x : G ⧸ A.H) (h : C.H ≤ MulAction.stabilizer G x) : C ⟶ A where
  toFun := Quotient.lift (fun g : G => g • x) (fun a b hab => by
    have hab' : a⁻¹ * b ∈ C.H := QuotientGroup.leftRel_apply.mp hab
    have := h hab'
    rw [MulAction.mem_stabilizer_iff, mul_smul] at this
    calc a • x = a • ((a⁻¹ * b) • x) := by rw [mul_smul, this]
      _ = b • x := by rw [← mul_smul, mul_inv_cancel_left])
  map_smul g y := by
    induction y using QuotientGroup.induction_on with
    | H a =>
      change (g * a) • x = g • a • x
      rw [mul_smul]

omit [IsTopologicalGroup G] in
lemma pointHom_mk (C A : OrbitObj G) (x : G ⧸ A.H) (h : C.H ≤ MulAction.stabilizer G x)
    (g : G) : (pointHom C A x h).toFun (QuotientGroup.mk g) = g • x := rfl

/-- **Monomorphisms of `B^temp(G)⁰` are injective.** -/
theorem OrbitHom.injective_of_mono {A B : OrbitObj G} (f : A ⟶ B) [Mono f] :
    Function.Injective f.toFun := by
  intro x y hxy
  let C : OrbitObj G := ⟨MulAction.stabilizer G x ⊓ MulAction.stabilizer G y,
    (isOpen_stabilizer A x).inter (isOpen_stabilizer A y)⟩
  have h : pointHom C A x inf_le_left ≫ f = pointHom C A y inf_le_right ≫ f := by
    ext z
    induction z using QuotientGroup.induction_on with
    | H g =>
      simp only [OrbitHom.comp_toFun, Function.comp_apply, pointHom_mk, f.map_smul, hxy]
  have h' := congrArg (fun φ => φ.toFun (QuotientGroup.mk 1)) (cancel_mono f |>.1 h)
  simpa [pointHom_mk] using h'

/-- **FSM-morphisms of `B^temp(G)⁰` are bijective.** -/
theorem OrbitHom.bijective_of_isFSM {A B : OrbitObj G} {f : A ⟶ B} (hf : IsFSM f) :
    Function.Bijective f.toFun :=
  haveI := hf.1
  ⟨f.injective_of_mono, f.surjective⟩

end Mono

end Frobenioid

end Iut
