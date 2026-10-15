/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Transport
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Automorphisms of the Aut-holomorphic plane ([AbsTopIII], Corollary 2.3(i) for `X = Y = ℂ`)

**Theorem** (`isIso_plane_iff`). A homeomorphism `ψ : ℂ ≃ₜ ℂ` is an automorphism of the
Aut-holomorphic plane (i.e. conjugation by `ψ|_U` carries `Aut^hol(U)` onto `Aut^hol(ψ(U))` for
every connected open `U`) **iff it is RC-holomorphic**: `ψ z = a z + b` or `ψ z = a z̄ + b` with
`a ≠ 0`.

This is the planar case of [AbsTopIII], Corollary 2.3(i) ("every morphism of Aut-holomorphic
spaces arises from a unique étale RC-holomorphic morphism"), and of Proposition 2.2(ii) (the
RC-holomorphic automorphisms contain the holomorphic ones with index two). The proof of "⇒" is
model-implicit: `ψ` induces an automorphism of the reconstructed field `RecField plane 0 ≅ ℂ`
(`transportEquiv`), continuous, hence the identity or the conjugation
(`induced_eq_id_or_conj`), and this determines `ψ`.

The converse (`isIso_plane_of_preservesHol`) checks the local condition on every open subset:
conjugation by an affine or anti-affine map preserves holomorphy (`preservesHol_affine`,
`preservesHol_antiAffine`, via `DifferentiableAt.conj_conj`).
-/

namespace Iut

namespace AutHol

open Set ComplexConjugate

instance : Fact (IsPlane plane) := ⟨⟨Homeomorph.refl ℂ, IsIso.refl plane⟩⟩

/-! ### Automorphisms are RC-holomorphic -/

/-- **Every automorphism of the Aut-holomorphic plane is affine or anti-affine.** -/
theorem exists_affine_of_isIso {ψ : ℂ ≃ₜ ℂ} (h : IsIso plane plane ψ) :
    ∃ a b : ℂ, a ≠ 0 ∧ ((∀ z, ψ z = a * z + b) ∨ (∀ z, ψ z = a * conj z + b)) := by
  have h0 := IsIso.refl plane
  set q := ψ 0
  set w := ψ.symm (q + 1)
  have hw : w ≠ 0 := by
    intro hw0
    have := congrArg ψ hw0
    simp only [w, Homeomorph.apply_symm_apply] at this
    have h1 : q + 1 = q := this
    simp at h1
  set θ := ((recEquiv h0 0).symm.trans (transportEquiv h 0)).trans (recEquiv h0 (ψ 0))
  have hθ : ∀ c, θ c = ψ (c * w) - q := by
    intro c
    change ψ (0 + c * (ψ.symm (ψ 0 + 1) - 0)) - ψ 0 = _
    simp [w, q]
  have key : ∀ z, ψ z = q + (θ : ℂ →+* ℂ) z / (θ : ℂ →+* ℂ) w := by
    intro z
    have h1 : ψ z = ψ (z / w * w) := by rw [div_mul_cancel₀ _ hw]
    rw [h1, ← map_div₀]
    change _ = q + θ (z / w)
    rw [hθ]
    ring
  have hθw : (θ : ℂ →+* ℂ) w ≠ 0 := by
    change θ w ≠ 0
    rw [map_ne_zero_iff _ θ.injective]
    exact hw
  rcases induced_eq_id_or_conj h 0 h0 h0 with hid | hconj
  · refine ⟨((θ : ℂ →+* ℂ) w)⁻¹, q, inv_ne_zero hθw, Or.inl fun z => ?_⟩
    rw [key, hid]
    simp only [RingHom.id_apply]
    ring
  · refine ⟨((θ : ℂ →+* ℂ) w)⁻¹, q, inv_ne_zero hθw, Or.inr fun z => ?_⟩
    rw [key, hconj]
    ring

/-! ### RC-holomorphic maps are automorphisms -/

/-- `ψ` **preserves holomorphy under conjugation**: `ψ⁻¹ ∘ F ∘ ψ` is holomorphic on `ψ⁻¹(W)`
whenever `F` is holomorphic on the open set `W`. -/
def PreservesHol (ψ : ℂ ≃ₜ ℂ) : Prop :=
  ∀ W : Set ℂ, IsOpen W → ∀ F : ℂ → ℂ, DifferentiableOn ℂ F W →
    DifferentiableOn ℂ (fun z => ψ.symm (F (ψ z))) (ψ ⁻¹' W)

theorem coe_symm_of_eq {U V : Set ℂ} {ψ : ℂ ≃ₜ ℂ} (e : U ≃ₜ V) (he : ∀ x : U, (e x : ℂ) = ψ x)
    (y : V) : (e.symm y : ℂ) = ψ.symm y := by
  have := he (e.symm y)
  rw [Homeomorph.apply_symm_apply] at this
  rw [this, Homeomorph.symm_apply_apply]

theorem holIn_conj_iff {U V : TopologicalSpace.Opens ℂ} {ψ : ℂ ≃ₜ ℂ} (h1 : PreservesHol ψ)
    (h2 : PreservesHol ψ.symm) (e : U ≃ₜ V) (he : ∀ x : U, (e x : ℂ) = ψ x) (g : V ≃ₜ V) :
    HolIn id (V : Set ℂ) g ↔ HolIn id (U : Set ℂ) (AutHol.conj e.symm g) := by
  constructor
  · rintro ⟨F, hF, hFg⟩
    refine ⟨fun z => ψ.symm (F (ψ z)), ?_, fun x => ?_⟩
    · rw [image_id] at hF ⊢
      refine (h1 V V.2 F hF).mono ?_
      intro x hx
      change ψ x ∈ V
      rw [← he ⟨x, hx⟩]
      exact (e ⟨x, hx⟩).2
    · simp only [id, AutHol.conj_apply, Homeomorph.symm_symm]
      rw [coe_symm_of_eq e he]
      have := hFg (e x)
      simp only [id] at this
      rw [this, he]
  · rintro ⟨G, hG, hGg⟩
    refine ⟨fun z => ψ (G (ψ.symm z)), ?_, fun y => ?_⟩
    · rw [image_id] at hG ⊢
      have := h2 U U.2 G hG
      simp only [Homeomorph.symm_symm] at this
      refine this.mono ?_
      intro y hy
      change ψ.symm y ∈ U
      rw [← coe_symm_of_eq e he ⟨y, hy⟩]
      exact (e.symm _).2
    · have : g y = e (AutHol.conj e.symm g (e.symm y)) := by simp
      rw [this, he]
      have h3 := hGg (e.symm y)
      simp only [id] at h3 ⊢
      rw [h3, coe_symm_of_eq e he]

/-- A homeomorphism preserving holomorphy under conjugation (together with its inverse) is an
automorphism of the Aut-holomorphic plane. -/
theorem isIso_plane_of_preservesHol {ψ : ℂ ≃ₜ ℂ} (h1 : PreservesHol ψ)
    (h2 : PreservesHol ψ.symm) : IsIso plane plane ψ := by
  rw [IsIso.iff]
  intro U _ V e he
  ext g
  rw [mem_map_conj]
  change g ∈ (ofEmbedding id).aut V ↔ AutHol.conj e.symm g ∈ (ofEmbedding id).aut U
  rw [mem_ofEmbedding_aut, mem_ofEmbedding_aut]
  have hinv : (AutHol.conj e.symm g).symm = AutHol.conj e.symm g.symm :=
    (map_inv (AutHol.conj e.symm) g).symm
  rw [hinv]
  exact and_congr (holIn_conj_iff h1 h2 e he g) (holIn_conj_iff h1 h2 e he g.symm)

theorem preservesHol_of_differentiable {ψ : ℂ ≃ₜ ℂ} (hψ : Differentiable ℂ ψ)
    (hψs : Differentiable ℂ ψ.symm) : PreservesHol ψ := by
  intro W _ F hF
  exact hψs.differentiableOn.comp (hF.comp hψ.differentiableOn (mapsTo_preimage ψ W))
    (mapsTo_univ _ _)

theorem preservesHol_of_anti {ψ : ℂ ≃ₜ ℂ} (P Q : ℂ → ℂ) (hP : Differentiable ℂ P)
    (hQ : Differentiable ℂ Q) (hψ : ∀ z, ψ z = P (conj z)) (hψs : ∀ w, ψ.symm w = conj (Q w)) :
    PreservesHol ψ := by
  intro W hW F hF z hz
  have hFz : DifferentiableAt ℂ F (P (conj z)) := by
    rw [← hψ]
    exact hF.differentiableAt (hW.mem_nhds hz)
  have hH : DifferentiableAt ℂ (Q ∘ F ∘ P) (conj z) :=
    (hQ _).comp _ (hFz.comp _ (hP _))
  have := hH.conj_conj
  rw [Complex.conj_conj] at this
  have heq : (fun z => ψ.symm (F (ψ z))) = (conj ∘ (Q ∘ F ∘ P) ∘ conj) := by
    ext z
    simp [hψ, hψs]
  rw [heq]
  exact this.differentiableWithinAt

/-- The anti-affine homeomorphism `z ↦ a z̄ + b`. -/
noncomputable def antiAffine (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a * conj z + b
  invFun w := conj ((w - b) / a)
  left_inv z := by
    simp only [add_sub_cancel_right]
    rw [mul_div_cancel_left₀ _ ha, Complex.conj_conj]
  right_inv w := by
    simp only [Complex.conj_conj]
    rw [mul_div_cancel₀ _ ha, sub_add_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem antiAffine_apply (a b : ℂ) (ha : a ≠ 0) (z : ℂ) : antiAffine a b ha z = a * conj z + b :=
  rfl

theorem preservesHol_affine (a b : ℂ) (ha : a ≠ 0) : PreservesHol (affine a b ha) :=
  preservesHol_of_differentiable (by
    change Differentiable ℂ fun z => a * z + b
    fun_prop) (by
    change Differentiable ℂ fun z => (z - b) / a
    fun_prop)

theorem preservesHol_affine_symm (a b : ℂ) (ha : a ≠ 0) : PreservesHol (affine a b ha).symm :=
  preservesHol_of_differentiable (by
    change Differentiable ℂ fun z => (z - b) / a
    fun_prop) (by
    change Differentiable ℂ fun z => a * z + b
    fun_prop)

theorem preservesHol_antiAffine (a b : ℂ) (ha : a ≠ 0) : PreservesHol (antiAffine a b ha) :=
  preservesHol_of_anti (fun u => a * u + b) (fun w => (w - b) / a) (by fun_prop) (by fun_prop)
    (fun _ => rfl) (fun _ => rfl)

theorem preservesHol_antiAffine_symm (a b : ℂ) (ha : a ≠ 0) :
    PreservesHol (antiAffine a b ha).symm :=
  preservesHol_of_anti (fun v => (v - conj b) / conj a) (fun w => conj a * w + conj b)
    (by fun_prop) (by fun_prop)
    (fun z => by
      change conj ((z - b) / a) = _
      simp [map_div₀, map_sub])
    (fun w => by
      change a * conj w + b = _
      simp [map_add, map_mul])

/-- **Automorphisms of the Aut-holomorphic plane = RC-holomorphic automorphisms of `ℂ`**
([AbsTopIII], Corollary 2.3(i), Proposition 2.2(ii), for `ℂ`). -/
theorem isIso_plane_iff (ψ : ℂ ≃ₜ ℂ) : IsIso plane plane ψ ↔
    ∃ a b : ℂ, a ≠ 0 ∧ ((∀ z, ψ z = a * z + b) ∨ (∀ z, ψ z = a * conj z + b)) := by
  refine ⟨exists_affine_of_isIso, ?_⟩
  rintro ⟨a, b, ha, h | h⟩
  · have : ψ = affine a b ha := by
      ext z
      exact h z
    subst this
    exact isIso_plane_of_preservesHol (preservesHol_affine a b ha)
      (preservesHol_affine_symm a b ha)
  · have : ψ = antiAffine a b ha := by
      ext z
      exact h z
    subst this
    exact isIso_plane_of_preservesHol (preservesHol_antiAffine a b ha)
      (preservesHol_antiAffine_symm a b ha)

end AutHol

end Iut
