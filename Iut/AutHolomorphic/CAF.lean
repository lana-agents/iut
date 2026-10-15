/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.PlaneAut
import Iut.LogLink.GaloisArch

/-!
# Complex archimedean fields and their Kummer structures ([AbsTopIII], Definition 4.1)

A **complex archimedean field** (CAF) is a topological field `k` isomorphic to `ℂ`
([AbsTopIII], §0). By [AbsTopIII], Definition 4.1(i), "`k` … [is] equipped with [a] natural
Aut-holomorphic structure", and a `k`-Kummer structure is an isomorphism of topological fields
`κ_k : k ≅ A_X`.

* `isIso_ofEmbedding ψ`: for a homeomorphism `ψ : X ≃ₜ ℂ`, `ψ` is an isomorphism of
  Aut-holomorphic spaces from `(X, ofEmbedding ψ)` to the plane.
* `cafStr κ`: the Aut-holomorphic structure of a CAF `k`, transported along any isomorphism of
  topological fields `κ : k ≅ ℂ`; **it does not depend on `κ`** (`cafStr_eq`, since two such `κ`
  differ by `id` or the complex conjugation, which preserve holomorphy up to conjugation).
* `tautEquiv κ : k ≃+* RecField (cafStr κ) 0`, the **tautological Kummer structure**: it sends
  `c ∈ k` to the multiplication map `x ↦ c x` (`tautEquiv_val`) — the field `k` is recovered from
  its own Aut-holomorphic structure, with no choice.
* `kummer_transition_archPolyIso`: the transition between two Kummer structures `ψ, ψ'` belongs to
  the archimedean poly-isomorphism of IUT III, Proposition 1.2(vii) (`ArchPolyIso`), and hence
  preserves the archimedean log-shell (the closed disc of radius `π`).
-/

namespace Iut

namespace AutHol

open Set ComplexConjugate

variable {X : Type*} [TopologicalSpace X]

theorem coe_symm_of_eq' {U : Set X} {V : Set ℂ} {ψ : X ≃ₜ ℂ} (e : U ≃ₜ V)
    (he : ∀ x : U, (e x : ℂ) = ψ x) (y : V) : ψ (e.symm y : X) = y := by
  rw [← he (e.symm y), Homeomorph.apply_symm_apply]

theorem image_eq_of_eq {U : Set X} {V : Set ℂ} {ψ : X ≃ₜ ℂ} (e : U ≃ₜ V)
    (he : ∀ x : U, (e x : ℂ) = ψ x) : ψ '' U = V := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← he ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).2
  · intro hy
    exact ⟨_, (e.symm ⟨y, hy⟩).2, coe_symm_of_eq' e he ⟨y, hy⟩⟩

/-- **`ψ : X ≃ₜ ℂ` is an isomorphism `(X, ofEmbedding ψ) ≅ plane`.** -/
theorem isIso_ofEmbedding (ψ : X ≃ₜ ℂ) : IsIso (ofEmbedding ψ) plane ψ := by
  rw [IsIso.iff]
  intro U _ V e he
  have key : ∀ h : V ≃ₜ V, HolIn id (V : Set ℂ) h ↔ HolIn ψ (U : Set X) (AutHol.conj e.symm h) := by
    intro h
    rw [HolIn, HolIn, image_id, image_eq_of_eq e he]
    refine exists_congr fun F => and_congr Iff.rfl ⟨fun hF x => ?_, fun hF y => ?_⟩
    · rw [AutHol.conj_apply, Homeomorph.symm_symm, coe_symm_of_eq' e he, ← he]
      simpa using hF (e x)
    · have h1 := hF (e.symm y)
      rw [AutHol.conj_apply, Homeomorph.symm_symm, Homeomorph.apply_symm_apply,
        coe_symm_of_eq' e he] at h1
      rw [id, h1, ← he, Homeomorph.apply_symm_apply]
      rfl
  ext g
  rw [mem_map_conj]
  change g ∈ (ofEmbedding id).aut V ↔ _
  rw [mem_ofEmbedding_aut, mem_ofEmbedding_aut]
  have hinv : (AutHol.conj e.symm g).symm = AutHol.conj e.symm g.symm :=
    (map_inv (AutHol.conj e.symm) g).symm
  rw [hinv]
  exact and_congr (key g) (key g.symm)

theorem isPlane_ofEmbedding (ψ : X ≃ₜ ℂ) : IsPlane (ofEmbedding ψ) := ⟨ψ, isIso_ofEmbedding ψ⟩

/-! ### Complex archimedean fields -/

variable {k : Type*} [Field k] [TopologicalSpace k]

/-- An isomorphism of topological fields `k ≅ ℂ`. -/
structure CAFIso (k : Type*) [Field k] [TopologicalSpace k] where
  /-- The ring isomorphism. -/
  toRingEquiv : k ≃+* ℂ
  continuous_toFun : Continuous toRingEquiv
  continuous_invFun : Continuous toRingEquiv.symm

namespace CAFIso

/-- The underlying homeomorphism. -/
def toHomeomorph (κ : CAFIso k) : k ≃ₜ ℂ where
  toEquiv := κ.toRingEquiv.toEquiv
  continuous_toFun := κ.continuous_toFun
  continuous_invFun := κ.continuous_invFun

theorem toHomeomorph_apply (κ : CAFIso k) (x : k) : κ.toHomeomorph x = κ.toRingEquiv x := rfl

theorem toHomeomorph_symm_apply (κ : CAFIso k) (z : ℂ) :
    κ.toHomeomorph.symm z = κ.toRingEquiv.symm z := rfl

end CAFIso

/-- **The natural Aut-holomorphic structure of a CAF** ([AbsTopIII], Definition 4.1(i)). -/
noncomputable def cafStr (κ : CAFIso k) : AutHolStr k := ofEmbedding κ.toHomeomorph

omit [TopologicalSpace X] in
theorem holIn_conj_comp {U : Set X} {ι : X → ℂ} (hU : IsOpen (ι '' U)) {g : U → U}
    (h : HolIn ι U g) : HolIn (fun x => conj (ι x)) U g := by
  obtain ⟨F, hF, hFg⟩ := h
  refine ⟨conj ∘ F ∘ conj, ?_, fun x => by simp [hFg]⟩
  rintro _ ⟨x, hx, rfl⟩
  have hFd : DifferentiableAt ℂ F (ι x) := hF.differentiableAt (hU.mem_nhds ⟨x, hx, rfl⟩)
  have := hFd.conj_conj
  exact this.differentiableWithinAt

/-- **The Aut-holomorphic structure of a CAF does not depend on the chosen `κ : k ≅ ℂ`.** -/
theorem cafStr_eq (κ κ' : CAFIso k) : cafStr κ = cafStr κ' := by
  have hτ : Continuous ((κ.toRingEquiv.symm.trans κ'.toRingEquiv : ℂ ≃+* ℂ) : ℂ →+* ℂ) :=
    κ'.continuous_toFun.comp κ.continuous_invFun
  have key : ∀ (κ₁ κ₂ : CAFIso k),
      ((κ₁.toRingEquiv.symm.trans κ₂.toRingEquiv : ℂ ≃+* ℂ) : ℂ →+* ℂ) = RingHom.id ℂ ∨
      ((κ₁.toRingEquiv.symm.trans κ₂.toRingEquiv : ℂ ≃+* ℂ) : ℂ →+* ℂ) = starRingEnd ℂ →
      ∀ U : TopologicalSpace.Opens k, ∀ g : U → U,
        HolIn κ₁.toHomeomorph U g → HolIn κ₂.toHomeomorph U g := by
    intro κ₁ κ₂ hc U g hg
    have hx : ∀ x : k, κ₂.toRingEquiv x =
        ((κ₁.toRingEquiv.symm.trans κ₂.toRingEquiv : ℂ ≃+* ℂ) : ℂ →+* ℂ) (κ₁.toRingEquiv x) := by
      intro x
      simp
    have hopen : IsOpen (κ₁.toHomeomorph '' (U : Set k)) := κ₁.toHomeomorph.isOpenMap _ U.2
    rcases hc with h | h
    · have hfun : (κ₂.toHomeomorph : k → ℂ) = κ₁.toHomeomorph := by
        ext x
        rw [CAFIso.toHomeomorph_apply, CAFIso.toHomeomorph_apply, hx, h, RingHom.id_apply]
      rw [hfun]
      exact hg
    · have hfun : (κ₂.toHomeomorph : k → ℂ) = fun x => conj (κ₁.toHomeomorph x) := by
        ext x
        rw [CAFIso.toHomeomorph_apply, CAFIso.toHomeomorph_apply, hx, h]
      rw [hfun]
      exact holIn_conj_comp hopen hg
  have h12 := Complex.ringHom_eq_id_or_conj_of_continuous hτ
  have hτ' : Continuous ((κ'.toRingEquiv.symm.trans κ.toRingEquiv : ℂ ≃+* ℂ) : ℂ →+* ℂ) :=
    κ.continuous_toFun.comp κ'.continuous_invFun
  have h21 := Complex.ringHom_eq_id_or_conj_of_continuous hτ'
  unfold cafStr ofEmbedding
  congr 1
  ext U g
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, mem_setOf_eq]
  exact ⟨fun hg => ⟨key κ κ' h12 U _ hg.1, key κ κ' h12 U _ hg.2⟩,
    fun hg => ⟨key κ' κ h21 U _ hg.1, key κ' κ h21 U _ hg.2⟩⟩

theorem isIso_cafStr (κ : CAFIso k) : IsIso (cafStr κ) plane κ.toHomeomorph :=
  isIso_ofEmbedding _

instance (κ : CAFIso k) : Fact (IsPlane (cafStr κ)) := ⟨⟨_, isIso_cafStr κ⟩⟩

/-- **The tautological Kummer structure** `k ≅ RecField (cafStr κ) 0`. -/
noncomputable def tautEquiv (κ : CAFIso k) : k ≃+* RecField (cafStr κ) 0 :=
  κ.toRingEquiv.trans (recEquiv (isIso_cafStr κ) 0).symm

/-- **The tautological Kummer structure sends `c` to the multiplication by `c`** (independently of
`κ`). -/
theorem tautEquiv_val (κ : CAFIso k) (c : k) : (tautEquiv κ c).val = fun x => c * x := by
  ext x
  change κ.toHomeomorph.symm (κ.toHomeomorph 0 + κ.toRingEquiv c *
    (κ.toHomeomorph x - κ.toHomeomorph 0)) = c * x
  rw [CAFIso.toHomeomorph_symm_apply, CAFIso.toHomeomorph_apply, CAFIso.toHomeomorph_apply,
    map_zero, zero_add, sub_zero, ← map_mul, RingEquiv.symm_apply_apply]

/-- **The transition between two Kummer structures lies in the archimedean poly-isomorphism**
(IUT III, Proposition 1.2(vii)) and preserves the archimedean log-shell. -/
theorem kummer_transition_archPolyIso {A : AutHolStr X} [Fact (IsPlane A)] (p : X)
    {ψ ψ' : X ≃ₜ ℂ} (hψ : IsIso A plane ψ) (hψ' : IsIso A plane ψ') :
    ∃ L : ℂ ≃ₗ[ℝ] ℂ, (∀ z, L z = ((recEquiv hψ p).symm.trans (recEquiv hψ' p)) z) ∧
      LogLink.ArchPolyIso L ∧
      L '' Metric.closedBall 0 Real.pi = Metric.closedBall 0 Real.pi := by
  obtain ⟨L, hL, hpoly⟩ := LogLink.archPolyIso_of_ringEquiv
    ((recEquiv hψ p).symm.trans (recEquiv hψ' p))
    ((recEquiv_continuous hψ').comp (recEquiv_symm_continuous hψ))
  exact ⟨L, hL, hpoly, hpoly.image_closedBall Real.pi⟩

end AutHol

end Iut
