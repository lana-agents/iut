/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Punct
import Mathlib.Topology.DiscreteSubset

/-!
# Self-maps of `T_Λ` induced by RC-holomorphic homeomorphisms of `ℂ`

* `isLocalHomeomorph_of_comp_surj`: if `p` is a surjective local homeomorphism, `g` is
  continuous and `g ∘ p` is a local homeomorphism, then so is `g`;
* `finite_fiber`: the fibres of a local homeomorphism out of a compact space are finite;
* `isMorphism_of_lift`: a self-map `G` of `T_Λ` with `G ∘ mk = mk ∘ Φ`, `Φ` a homeomorphism of
  `ℂ` that is holomorphic (or antiholomorphic) together with its inverse, is a morphism of
  Aut-holomorphic spaces (e.g. the multiplication maps `[N]` of [AbsTopII] Example 3.2 (i)).
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus

theorem isLocalHomeomorph_of_comp_surj {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {p : X → Y} {g : Y → Z} (hp : IsLocalHomeomorph p)
    (hps : Function.Surjective p) (hg : Continuous g) (hgp : IsLocalHomeomorph (g ∘ p)) :
    IsLocalHomeomorph g := by
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro y
  obtain ⟨x, rfl⟩ := hps y
  obtain ⟨S, hSo, hxS, hSinj⟩ := hp.isLocallyInjective x
  obtain ⟨S', hS'o, hxS', hS'inj⟩ := hgp.isLocallyInjective x
  set W := S ∩ S'
  have hWo : IsOpen W := hSo.inter hS'o
  have hpW : IsOpen (p '' W) := hp.isOpenMap W hWo
  refine ⟨p '' W, hpW.mem_nhds ⟨x, ⟨hxS, hxS'⟩, rfl⟩, ?_⟩
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (hg.comp continuous_subtype_val) ?_ ?_
  · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩ h
    have : a = b := hS'inj ha.2 hb.2 h
    subst this
    rfl
  · intro O hO
    have hO' : IsOpen (Subtype.val '' O : Set Y) := hpW.isOpenMap_subtype_val O hO
    have : (p '' W).restrict g '' O = (g ∘ p) '' (p ⁻¹' (Subtype.val '' O) ∩ W) := by
      ext z
      constructor
      · rintro ⟨⟨_, a, ha, rfl⟩, hO, rfl⟩
        exact ⟨a, ⟨⟨_, hO, rfl⟩, ha⟩, rfl⟩
      · rintro ⟨a, ⟨⟨y', hy', hy'a⟩, ha⟩, rfl⟩
        refine ⟨y', hy', ?_⟩
        simp only [restrict_apply, Function.comp_apply, hy'a]
    rw [this]
    exact hgp.isOpenMap _ ((hO'.preimage hp.continuous).inter hWo)

/-- The fibres of a local homeomorphism out of a compact space are finite. -/
theorem finite_fiber {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X]
    [T1Space Y] {f : X → Y} (hf : IsLocalHomeomorph f) (y : Y) : (f ⁻¹' {y}).Finite := by
  have hc : IsCompact (f ⁻¹' {y}) := (isClosed_singleton.preimage hf.continuous).isCompact
  refine hc.finite ((hf.isLocalHomeomorphOn.mono (subset_univ _)).isDiscrete_of_image ?_)
  exact (subsingleton_singleton.anti (image_preimage_subset f {y})).isDiscrete

variable {L : PeriodPair}

theorem continuous_of_lift {G : Torus L → Torus L} {Φ : ℂ → ℂ} (hΦ : Continuous Φ)
    (hG : ∀ z, G (mk L z) = mk L (Φ z)) : Continuous G := by
  rw [(isCoveringMap_mk.isQuotientMap mk_surjective).continuous_iff]
  have : G ∘ mk L = mk L ∘ Φ := funext hG
  rw [this]
  exact continuous_mk.comp hΦ

theorem isLocalHomeomorph_of_lift {G : Torus L → Torus L} (Φ : ℂ ≃ₜ ℂ)
    (hG : ∀ z, G (mk L z) = mk L (Φ z)) : IsLocalHomeomorph G := by
  refine isLocalHomeomorph_of_comp_surj isCoveringMap_mk.isLocalHomeomorph mk_surjective
    (continuous_of_lift Φ.continuous hG) ?_
  have : G ∘ mk L = mk L ∘ Φ := funext hG
  rw [this]
  exact isCoveringMap_mk.isLocalHomeomorph.comp Φ.isLocalHomeomorph

/-- **Self-maps of `T_Λ` induced by RC-holomorphic homeomorphisms of `ℂ` are morphisms of
Aut-holomorphic spaces.** -/
theorem isMorphism_of_lift {G : Torus L → Torus L} (Φ : ℂ ≃ₜ ℂ) (δ : Bool)
    (hΦ : ∀ w, RCDiffAt δ Φ w) (hΦ' : ∀ w, RCDiffAt δ Φ.symm w)
    (hG : ∀ z, G (mk L z) = mk L (Φ z)) : IsMorphism (torusStr L) (torusStr L) G := by
  refine ⟨isLocalHomeomorph_of_lift Φ hG, ?_⟩
  intro U _ V _ e he
  apply ofCover_conj continuous_mk e (δ := δ)
  · refine rcAlong_of_lift (U.2.preimage continuous_mk) (fun x hx => ?_) hΦ (fun z hz => ?_)
    · obtain ⟨z, rfl⟩ := mk_surjective (L := L) x
      exact ⟨z, hx, rfl⟩
    · rw [extendU_of_mem _ (show mk L z ∈ (U : Set (Torus L)) from hz), he]
      exact hG z
  · intro z hz
    set u := e.symm ⟨mk L z, hz⟩
    obtain ⟨z₁, hz₁⟩ := mk_surjective (L := L) (u : Torus L)
    have hl : Φ z₁ - z ∈ L.lattice := by
      rw [← mk_eq_mk, ← hG, hz₁, ← he u]
      simp [u]
    set l := Φ z₁ - z
    refine ⟨fun w => Φ.symm (w + l), Eventually.of_forall fun w => ?_, ?_⟩
    · have h := RCDiffAt.comp (ε := δ) (δ := false) (Φ₁ := Φ.symm) (Φ₂ := fun u => u + l)
        (w := w) (hΦ' _) (by rw [rcDiffAt_false]; fun_prop)
      rwa [Bool.xor_false] at h
    · have hcont : ContinuousAt (fun w => mk L (Φ.symm (w + l))) z :=
        (continuous_mk.comp
          (Φ.symm.continuous.comp (continuous_id.add continuous_const))).continuousAt
      have hzz : mk L (Φ.symm (z + l)) = u := by
        simp only [l, add_sub_cancel, Homeomorph.symm_apply_apply, hz₁]
      have h1 : ∀ᶠ w in 𝓝 z, mk L (Φ.symm (w + l)) ∈ U :=
        hcont.preimage_mem_nhds (by rw [hzz]; exact U.2.mem_nhds u.2)
      have h2 : ∀ᶠ w in 𝓝 z, mk L w ∈ V :=
        continuous_mk.continuousAt.preimage_mem_nhds (V.2.mem_nhds hz)
      filter_upwards [h1, h2] with w hw1 hw2
      rw [extendU_of_mem _ hw2]
      have : e ⟨mk L (Φ.symm (w + l)), hw1⟩ = ⟨mk L w, hw2⟩ := by
        apply Subtype.ext
        rw [he, hG, Homeomorph.apply_symm_apply, mk_add, (mk_eq_zero (L := L)).2 hl, add_zero]
      rw [← this, e.symm_apply_apply]

end Ell

end AutHol

end Iut
