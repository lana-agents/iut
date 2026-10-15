/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Basic
import Iut.AutHolomorphic.EntireAut

/-!
# The Aut-holomorphic plane

The Aut-holomorphic space associated to the Riemann surface `ℂ` ([AbsTopIII], Definition 2.1(i);
it is the Aut-holomorphic structure that a complex archimedean field `k` carries, Definition
4.1(i)): `plane = ofEmbedding id`.

* `mem_global_plane`: **`A_ℂ(ℂ)` is the affine group** `{z ↦ a z + b | a ≠ 0}` (via
  `exists_affine_of_homeomorph`: entire homeomorphisms are affine).
* `affine`: the affine homeomorphisms; `affine_mem_global`.
-/

namespace Iut

namespace AutHol

open Set TopologicalSpace

/-- **The Aut-holomorphic plane** `ℂ`. -/
noncomputable def plane : AutHolStr ℂ := ofEmbedding id

/-- The affine homeomorphism `z ↦ a z + b`. -/
noncomputable def affine (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * z + b
  invFun z := (z - b) / a
  left_inv z := by field_simp; ring
  right_inv z := by field_simp; ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem affine_apply (a b : ℂ) (ha : a ≠ 0) (z : ℂ) : affine a b ha z = a * z + b := rfl

@[simp]
theorem affine_symm_apply (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    (affine a b ha).symm z = (z - b) / a := rfl

theorem holIn_top_iff {g : (⊤ : Opens ℂ) → (⊤ : Opens ℂ)} :
    HolIn id ((⊤ : Opens ℂ) : Set ℂ) g ↔ Differentiable ℂ (fun z => (g ⟨z, by simp⟩ : ℂ)) := by
  constructor
  · rintro ⟨F, hF, hFg⟩
    have hF' : Differentiable ℂ F := by
      intro z
      exact (hF z (by simp)).differentiableAt (by simp)
    have : (fun z => (g ⟨z, by simp⟩ : ℂ)) = F := by
      ext z
      exact hFg ⟨z, by simp⟩
    rw [this]
    exact hF'
  · intro h
    exact ⟨_, h.differentiableOn, fun x => rfl⟩

/-- **`A_ℂ(ℂ)` is the affine group.** -/
theorem mem_global_plane {g : ℂ ≃ₜ ℂ} :
    g ∈ plane.global ↔ ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, g z = a * z + b := by
  rw [AutHolStr.mem_global]
  constructor
  · rintro ⟨h1, -⟩
    rw [holIn_top_iff] at h1
    exact exists_affine_of_homeomorph g h1
  · rintro ⟨a, b, ha, hg⟩
    refine ⟨holIn_top_iff.2 ?_, holIn_top_iff.2 ?_⟩
    · have : (fun z => ((conj (topHomeo ℂ).symm g) ⟨z, by simp⟩ : ℂ)) = fun z => a * z + b := by
        ext z
        exact hg z
      rw [this]
      fun_prop
    · have hs : ∀ z, g.symm z = (z - b) / a := by
        intro z
        have := hg (g.symm z)
        rw [Homeomorph.apply_symm_apply] at this
        rw [eq_div_iff ha]
        linear_combination -this
      have : (fun z => ((conj (topHomeo ℂ).symm g).symm ⟨z, by simp⟩ : ℂ)) =
          fun z => (z - b) / a := by
        ext z
        exact hs z
      rw [this]
      fun_prop

theorem affine_mem_global (a b : ℂ) (ha : a ≠ 0) : affine a b ha ∈ plane.global :=
  mem_global_plane.2 ⟨a, b, ha, fun _ => rfl⟩

theorem isConnected_univ_complex : IsConnected (univ : Set ℂ) := isConnected_univ

end AutHol

end Iut
