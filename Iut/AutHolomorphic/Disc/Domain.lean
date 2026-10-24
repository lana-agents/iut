/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Disc.Normalizer
import Iut.AutHolomorphic.OfCover

/-!
# Aut-holomorphic discs ([AbsTopIII] Proposition 2.2 (i))

For an open `Ω ⊆ ℂ`:

* `HolOn Ω g`: a self-map of `Ω` is holomorphic; `holAutOn Ω`: the holomorphic automorphisms
  (`holAutOn Dk = holAut`);
* `IsBihol Ω₁ Ω₂ F G`: `F : Ω₁ → Ω₂` is biholomorphic with inverse `G`; `IsBihol.homeo`;
  `IsBihol.conj_mem`: conjugation by a biholomorphism carries `holAutOn Ω₁` onto `holAutOn Ω₂`;
* `rc_of_normalizes_bihol` (**[AbsTopIII] Proposition 2.2 (i)**): if `Ω₁`, `Ω₂` are
  biholomorphic to the unit disc ("Aut-holomorphic discs") and a homeomorphism `e : Ω₁ ≃ₜ Ω₂`
  conjugates `holAutOn Ω₁` onto `holAutOn Ω₂` (an isomorphism of Aut-holomorphic spaces), then
  `e` is holomorphic or antiholomorphic (`RCDiffAt`).
-/

namespace Iut

namespace AutHol

namespace Disc

open Complex Metric Set Filter Topology Uniformization

open scoped ComplexConjugate

/-- `g : Ω → Ω` is **holomorphic**: it is given by a function holomorphic on `Ω`. -/
def HolOn (Ω : Set ℂ) (g : Ω → Ω) : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F Ω ∧ ∀ z : Ω, (g z : ℂ) = F z

theorem HolOn.id (Ω : Set ℂ) : HolOn Ω _root_.id := ⟨_root_.id, differentiableOn_id, fun _ => rfl⟩

theorem HolOn.mapsTo {Ω : Set ℂ} {g : Ω → Ω} {F : ℂ → ℂ} (hFg : ∀ z : Ω, (g z : ℂ) = F z) :
    MapsTo F Ω Ω := fun z hz => by
  have := hFg ⟨z, hz⟩
  simp only at this
  rw [← this]
  exact (g _).2

theorem HolOn.comp {Ω : Set ℂ} {g h : Ω → Ω} (hg : HolOn Ω g) (hh : HolOn Ω h) :
    HolOn Ω (g ∘ h) := by
  obtain ⟨F, hF, hFg⟩ := hg
  obtain ⟨G, hG, hGh⟩ := hh
  exact ⟨F ∘ G, hF.comp hG (HolOn.mapsTo hGh), fun z => by
    simp only [Function.comp_apply, hFg, hGh]⟩

/-- **The holomorphic automorphisms of `Ω`.** -/
def holAutOn (Ω : Set ℂ) : Subgroup (Ω ≃ₜ Ω) where
  carrier := {g | HolOn Ω g ∧ HolOn Ω g.symm}
  mul_mem' := fun hg hh => ⟨hg.1.comp hh.1, hh.2.comp hg.2⟩
  one_mem' := ⟨HolOn.id Ω, HolOn.id Ω⟩
  inv_mem' := fun hg => ⟨hg.2, hg.1⟩

theorem holAutOn_Dk : holAutOn Dk = holAut := Subgroup.ext fun _ => Iff.rfl

/-! ### Biholomorphisms -/

/-- `F` maps `Ω₁` biholomorphically onto `Ω₂`, with inverse `G`. -/
def IsBihol (Ω₁ Ω₂ : Set ℂ) (F G : ℂ → ℂ) : Prop :=
  MapsTo F Ω₁ Ω₂ ∧ MapsTo G Ω₂ Ω₁ ∧ (∀ z ∈ Ω₁, G (F z) = z) ∧ (∀ w ∈ Ω₂, F (G w) = w) ∧
    DifferentiableOn ℂ F Ω₁ ∧ DifferentiableOn ℂ G Ω₂

variable {Ω₁ Ω₂ : Set ℂ} {F G : ℂ → ℂ}

theorem IsBihol.symm (h : IsBihol Ω₁ Ω₂ F G) : IsBihol Ω₂ Ω₁ G F :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

/-- The homeomorphism `Ω₁ ≃ₜ Ω₂` of a biholomorphism. -/
noncomputable def IsBihol.homeo (h : IsBihol Ω₁ Ω₂ F G) : Ω₁ ≃ₜ Ω₂ :=
  homeomorphOfInvOn F G h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1.continuousOn
    h.2.2.2.2.2.continuousOn

@[simp] theorem IsBihol.coe_homeo (h : IsBihol Ω₁ Ω₂ F G) (z : Ω₁) : (h.homeo z : ℂ) = F z := rfl

@[simp] theorem IsBihol.coe_homeo_symm (h : IsBihol Ω₁ Ω₂ F G) (w : Ω₂) :
    (h.homeo.symm w : ℂ) = G w := rfl

/-- Conjugation `g ↦ e ∘ g ∘ e⁻¹` for homeomorphisms between subsets. -/
noncomputable def cjS {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (g : X ≃ₜ X) : Y ≃ₜ Y := (e.symm.trans g).trans e

@[simp] theorem cjS_apply {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (g : X ≃ₜ X) (y : Y) : cjS e g y = e (g (e.symm y)) := rfl

theorem cjS_symm_cjS {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (g : X ≃ₜ X) : cjS e.symm (cjS e g) = g := by ext; simp

theorem HolOn.conj_bihol (h : IsBihol Ω₁ Ω₂ F G) {g : Ω₁ → Ω₁} (hg : HolOn Ω₁ g) :
    HolOn Ω₂ (fun w => h.homeo (g (h.homeo.symm w))) := by
  obtain ⟨K, hK, hKg⟩ := hg
  refine ⟨F ∘ K ∘ G, ?_, fun w => ?_⟩
  · exact h.2.2.2.2.1.comp (hK.comp h.2.2.2.2.2 h.2.1) ((HolOn.mapsTo hKg).comp h.2.1)
  · simp [hKg]

/-- **Conjugation by a biholomorphism carries holomorphic automorphisms to holomorphic
automorphisms.** -/
theorem IsBihol.conj_mem (h : IsBihol Ω₁ Ω₂ F G) {g : Ω₁ ≃ₜ Ω₁} (hg : g ∈ holAutOn Ω₁) :
    cjS h.homeo g ∈ holAutOn Ω₂ :=
  ⟨HolOn.conj_bihol h hg.1, HolOn.conj_bihol h hg.2⟩

theorem IsBihol.homeo_symm (h : IsBihol Ω₁ Ω₂ F G) : h.homeo.symm = h.symm.homeo := rfl

theorem IsBihol.conj_mem_iff (h : IsBihol Ω₁ Ω₂ F G) (g : Ω₁ ≃ₜ Ω₁) :
    g ∈ holAutOn Ω₁ ↔ cjS h.homeo g ∈ holAutOn Ω₂ := by
  refine ⟨h.conj_mem, fun hg => ?_⟩
  have := h.symm.conj_mem hg
  rwa [← h.homeo_symm, cjS_symm_cjS] at this

/-! ### Proposition 2.2 (i) -/

theorem rcDiffAt_comp_of_open {Φ₁ Φ₂ : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (h₁ : DifferentiableOn ℂ Φ₁ S) {z : ℂ} (hz : Φ₂ z ∈ S) {δ : Bool} (h₂ : RCDiffAt δ Φ₂ z) :
    RCDiffAt δ (Φ₁ ∘ Φ₂) z := by
  have := RCDiffAt.comp (ε := false) (rcDiffAt_false.2 (h₁.differentiableAt (hS.mem_nhds hz))) h₂
  simpa using this

/-- **[AbsTopIII] Proposition 2.2 (i)**: an isomorphism `e : Ω₁ ≃ₜ Ω₂` of the Aut-holomorphic
spaces of two open subsets of `ℂ` biholomorphic to the unit disc (conjugation by `e` carries the
holomorphic automorphisms of `Ω₁` onto those of `Ω₂`) is holomorphic or antiholomorphic. -/
theorem rc_of_normalizes_bihol (hΩ₁ : IsOpen Ω₁) {F₁ G₁ F₂ G₂ : ℂ → ℂ}
    (h₁ : IsBihol Dk Ω₁ F₁ G₁) (h₂ : IsBihol Dk Ω₂ F₂ G₂) (e : Ω₁ ≃ₜ Ω₂)
    (he : ∀ g : Ω₁ ≃ₜ Ω₁, g ∈ holAutOn Ω₁ ↔ cjS e g ∈ holAutOn Ω₂) :
    ∃ (δ : Bool) (Φ : ℂ → ℂ), (∀ z ∈ Ω₁, RCDiffAt δ Φ z) ∧ ∀ z : Ω₁, (e z : ℂ) = Φ z := by
  -- `α = h₂⁻¹ ∘ e ∘ h₁` normalises `holAut`
  set α : Dk ≃ₜ Dk := (h₁.homeo.trans e).trans h₂.homeo.symm with hα
  have hαn : Normalizes α := by
    intro g
    rw [← holAutOn_Dk, h₁.conj_mem_iff, he, h₂.symm.conj_mem_iff]
    have : cjS h₂.symm.homeo (cjS e (cjS h₁.homeo g)) = cj α g := by ext; rfl
    rw [this, holAutOn_Dk]
  obtain ⟨g, hg, hαg⟩ := rc_of_normalizes hαn
  obtain ⟨K, hK, hKg⟩ := hg.1
  have hKm : MapsTo K Dk Dk := HolOn.mapsTo (Ω := Dk) hKg
  -- `e = h₂ ∘ α ∘ h₁⁻¹`
  have heα : ∀ z : Ω₁, e z = h₂.homeo (α (h₁.homeo.symm z)) := by
    intro z; simp [hα]
  have hG₁ : ∀ z ∈ Ω₁, DifferentiableAt ℂ G₁ z := fun z hz =>
    h₁.2.2.2.2.2.differentiableAt (hΩ₁.mem_nhds hz)
  rcases hαg with hαg | hαg
  · refine ⟨false, F₂ ∘ K ∘ G₁, fun z hz => ?_, fun z => ?_⟩
    · rw [rcDiffAt_false]
      have hGz := h₁.2.1 hz
      refine (h₂.2.2.2.2.1.differentiableAt (isOpen_ball.mem_nhds (hKm hGz))).comp z
        ((hK.differentiableAt (isOpen_ball.mem_nhds hGz)).comp z (hG₁ z hz))
    · rw [heα, hαg, IsBihol.coe_homeo]
      simp [hKg]
  · refine ⟨true, F₂ ∘ K ∘ (starRingEnd ℂ) ∘ G₁, fun z hz => ?_, fun z => ?_⟩
    · rw [rcDiffAt_true]
      have hGz := h₁.2.1 hz
      have hcG : DifferentiableAt ℂ ((starRingEnd ℂ) ∘ G₁ ∘ (starRingEnd ℂ)) (conj z) := by
        have := (hG₁ z hz).conj_conj
        simpa [Function.comp_def] using this
      have hc : conj (G₁ z) ∈ Dk := conj_mem_Dk hGz
      have hKd : DifferentiableAt ℂ K (((starRingEnd ℂ) ∘ G₁ ∘ (starRingEnd ℂ)) (conj z)) := by
        simp only [Function.comp_apply, Complex.conj_conj]
        exact hK.differentiableAt (isOpen_ball.mem_nhds hc)
      have hF : DifferentiableAt ℂ F₂ (K (((starRingEnd ℂ) ∘ G₁ ∘ (starRingEnd ℂ)) (conj z))) := by
        simp only [Function.comp_apply, Complex.conj_conj]
        exact h₂.2.2.2.2.1.differentiableAt (isOpen_ball.mem_nhds (hKm hc))
      have := hF.comp (conj z) (hKd.comp (conj z) hcG)
      exact this
    · rw [heα, hαg, IsBihol.coe_homeo]
      simp [hKg]

end Disc

end AutHol

end Iut
