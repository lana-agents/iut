/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Functorial group-theoretic algorithms by transport ([EtTh], Cor. 2.18(i))

[EtTh], Cor. 2.18(i) asserts the existence of a *functorial group-theoretic algorithm* which,
from any topological group `Π^•` isomorphic to `Π^tp_X̲`, constructs subgroups (`Π^•_Y̲`, `Π^•_Ÿ̲`,
`Ker(Π^• ↠ G^•_K)`, the preimages of the theta subquotients, the cuspidal decomposition groups of
a given label) such that every isomorphism `Π^• ≅ Π^tp_X̲` maps them to the corresponding
subgroups of `Π^tp_X̲`. The *content* of such a statement is that the reference subgroups are
preserved by every automorphism of `Π^tp_X̲` (in [EtTh]: the proofs of Props. 1.8, 2.4 and
[Mzk2], Lemma 1.3.8, i.e. tempered anabelian geometry); the algorithm itself is then formal:
transport the reference subgroup along any isomorphism.

This file makes that formal step precise, so that Cor. 2.18(i) becomes a statement of the form
"these subgroups of `Π^tp_X̲` are characteristic" (`IsCharacteristicT`), whose proof is a
Layer-B obligation (Prop. 2.4 with the inputs of MR13/MR7):

* `transportSub S₀ e`: the subgroup of `P` corresponding to `S₀ ≤ P₀` under `e : P ≃ₜ* P₀`;
* `transportSub_indep`: if `S₀` is preserved by all automorphisms of `P₀` (`IsCharacteristicT`),
  the result does not depend on `e` — it is an invariant of the abstract topological group `P`
  once `P` is known to be isomorphic to `P₀`;
* `transportSub_map`: functoriality: every isomorphism `f : P ≃ₜ* P'` maps the subgroup of `P`
  onto the subgroup of `P'`; `transportSub_self`: on `P₀` itself the algorithm returns `S₀`.
-/

namespace Iut.EtaleTheta.Env

variable {P P' P₀ : Type*} [Group P] [Group P'] [Group P₀] [TopologicalSpace P]
  [TopologicalSpace P'] [TopologicalSpace P₀]

/-- A subgroup preserved by every automorphism of the topological group (the content of a
"functorial group-theoretic algorithm", [EtTh], Cor. 2.18(i)). -/
def IsCharacteristicT (S₀ : Subgroup P₀) : Prop :=
  ∀ α : P₀ ≃ₜ* P₀, S₀.map α.toMulEquiv.toMonoidHom = S₀

/-- The subgroup of `P` obtained by transporting `S₀ ≤ P₀` along `e : P ≃ₜ* P₀`. -/
def transportSub (S₀ : Subgroup P₀) (e : P ≃ₜ* P₀) : Subgroup P :=
  S₀.comap e.toMulEquiv.toMonoidHom

lemma mem_transportSub (S₀ : Subgroup P₀) (e : P ≃ₜ* P₀) (x : P) :
    x ∈ transportSub S₀ e ↔ e x ∈ S₀ := Iff.rfl

lemma map_transportSub (S₀ : Subgroup P₀) (e : P ≃ₜ* P₀) :
    (transportSub S₀ e).map e.toMulEquiv.toMonoidHom = S₀ := by
  ext y
  simp only [Subgroup.mem_map, mem_transportSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨e.symm y, by simpa using hy, e.apply_symm_apply y⟩

/-- **Independence of the choice of isomorphism**: for a characteristic `S₀`, the transported
subgroup does not depend on `e`. -/
theorem transportSub_indep {S₀ : Subgroup P₀} (hS : IsCharacteristicT S₀) (e e' : P ≃ₜ* P₀) :
    transportSub S₀ e = transportSub S₀ e' := by
  ext x
  rw [mem_transportSub, mem_transportSub]
  have h := hS (e.symm.trans e')
  have key : ∀ y, y ∈ S₀ ↔ (e.symm.trans e') y ∈ S₀ := by
    intro y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := (e.symm.trans e').injective hzy
      exact this ▸ hz
  rw [key (e x)]
  simp

/-- **Functoriality**: an isomorphism `f : P ≃ₜ* P'` maps the transported subgroup of `P`
(along `f ≫ e'`) onto the transported subgroup of `P'` (along `e'`). -/
theorem transportSub_map (S₀ : Subgroup P₀) (f : P ≃ₜ* P') (e' : P' ≃ₜ* P₀) :
    (transportSub S₀ (f.trans e')).map f.toMulEquiv.toMonoidHom = transportSub S₀ e' := by
  ext y
  simp only [Subgroup.mem_map, mem_transportSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨f.symm y, by simpa using hy, f.apply_symm_apply y⟩

/-- **Functoriality for arbitrary choices**: for characteristic `S₀`, every isomorphism
`f : P ≃ₜ* P'` maps the subgroup of `P` (for any choice of `e`) onto that of `P'` (for any
choice of `e'`). -/
theorem transportSub_map_of_char {S₀ : Subgroup P₀} (hS : IsCharacteristicT S₀) (f : P ≃ₜ* P')
    (e : P ≃ₜ* P₀) (e' : P' ≃ₜ* P₀) :
    (transportSub S₀ e).map f.toMulEquiv.toMonoidHom = transportSub S₀ e' := by
  rw [transportSub_indep hS e (f.trans e'), transportSub_map]

/-- On the reference group itself the algorithm returns the reference subgroup. -/
theorem transportSub_self {S₀ : Subgroup P₀} (hS : IsCharacteristicT S₀) (e : P₀ ≃ₜ* P₀) :
    transportSub S₀ e = S₀ := by
  rw [transportSub_indep hS e (ContinuousMulEquiv.refl P₀)]
  rfl

end Iut.EtaleTheta.Env
