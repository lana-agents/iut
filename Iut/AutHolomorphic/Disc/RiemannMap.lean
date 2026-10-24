/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Disc.Domain
import Oka.Uniformization.CoveringLimit
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# The Riemann mapping theorem for bounded simply connected domains

`exists_isBihol`: **a bounded, open, nonempty, simply connected `Ω ⊆ ℂ` is biholomorphic to the
unit disc.** Input: oka's `Uniformization.PlaneData.exists_covering` (the Koebe–Fisher–Hubbard–
Wittner construction of a holomorphic covering `ψ : 𝔻 → Ω`, onto, with `ψ' ≠ 0`). Since `Ω` is
simply connected, the inclusion `Ω → ℂ` lifts through `ψ` (Mathlib's
`IsCoveringMapOn.existsUnique_continuousMap_lifts`) to a section `σ` of `ψ`; `σ ∘ ψ` and `id` are
two lifts of `ψ|_𝔻` that agree at one point, so `σ ∘ ψ = id` by uniqueness of lifts on the (convex,
hence simply connected) disc. `σ` is holomorphic since `ψ' ≠ 0` (`differentiableAt_of_comp_eq`).

Used for [AbsTopIII] Corollary 2.3 (i): the image of a small disc under a morphism of
Aut-holomorphic spaces is a bounded simply connected domain, hence an Aut-holomorphic disc.
-/

namespace Iut

namespace AutHol

namespace Disc

open Complex Metric Set Filter Topology Uniformization

/-- A homeomorphism of `ℂ` is a covering map on every subset. -/
theorem isCoveringMapOn_of_homeomorph (g : ℂ ≃ₜ ℂ) (s : Set ℂ) : IsCoveringMapOn g s :=
  g.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun _ _ => Set.Subsingleton.finite fun _ ha _ hb => g.injective (ha.trans hb.symm))
    g.isLocalHomeomorph.isLocalHomeomorphOn

instance : SimplyConnectedSpace Dk :=
  haveI := (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, zero_mem_Dk⟩
  SimplyConnectedSpace.ofContractible _

/-- **The Riemann mapping theorem** for bounded domains: a bounded, open, nonempty, simply
connected subset of `ℂ` is biholomorphic to the unit disc. -/
theorem exists_isBihol {Ω : Set ℂ} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    [SimplyConnectedSpace Ω] : ∃ F G : ℂ → ℂ, IsBihol Dk Ω F G := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨R, hR⟩ := hb.subset_ball c
  have hR0 : 0 < R := by
    have := hR hc
    rw [mem_ball, dist_self] at this
    exact this
  have hR0' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  -- the affine chart `w ↦ c + R w`
  set p₀ : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (R : ℂ) hR0').trans (Homeomorph.addLeft c) with hp₀
  have hp₀_apply : ∀ w, p₀ w = c + R * w := fun _ => rfl
  have hgood : Good (p₀ ⁻¹' Ω) := by
    refine ⟨hΩ.preimage p₀.continuous, fun w hw => ?_, ?_⟩
    · have := hR hw
      rw [hp₀_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0] at this
      rw [mem_ball_zero_iff]
      nlinarith [norm_nonneg w]
    · rw [mem_preimage, hp₀_apply, mul_zero, add_zero]; exact hc
  have hpre : IsPreconnected Ω := by
    rw [isPreconnected_iff_preconnectedSpace]; infer_instance
  have hpd : PlaneData Ω (p₀ ⁻¹' Ω) p₀ :=
    ⟨hgood, hΩ, hpre, isCoveringMapOn_of_homeomorph p₀ Ω, rfl,
      ((differentiable_const c).add
        ((differentiable_const _).mul differentiable_id)).differentiableOn⟩
  have hc₀ : c + R ∉ Ω := by
    intro h
    have := hR h
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR0] at this
    exact lt_irrefl _ this
  obtain ⟨ψ, hcov, hψpre, hψd, hψ', hψs⟩ := hpd.exists_covering hc₀
  -- lift the inclusion `Ω → ℂ`
  haveI : LocallyPathConnectedSpace Ω := hΩ.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace Dk := isOpen_ball.locallyPathConnectedSpace
  obtain ⟨e₀, he₀, he₀c⟩ := hψs hc
  let f : C(Ω, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨σ, ⟨hσ₀, hσ⟩, -⟩ := hcov.existsUnique_continuousMap_lifts f (a₀ := ⟨c, hc⟩) (e₀ := e₀)
    he₀c (fun a => a.2)
  have hψσ : ∀ w : Ω, ψ (σ w) = w := fun w => congrFun hσ w
  have hσD : ∀ w : Ω, σ w ∈ Dk := fun w => by
    have : σ w ∈ ψ ⁻¹' Ω := by rw [mem_preimage, hψσ]; exact w.2
    rwa [hψpre] at this
  -- `σ ∘ ψ = id` on the disc
  have hψc : Continuous fun z : Dk => ψ z :=
    hψd.continuousOn.comp_continuous continuous_subtype_val fun z => z.2
  have hψΩ : ∀ z : Dk, ψ z ∈ Ω := fun z => by
    have : (z : ℂ) ∈ ψ ⁻¹' Ω := by rw [hψpre]; exact z.2
    exact this
  let f' : C(Dk, Ω) := ⟨fun z => ⟨ψ z, hψΩ z⟩, hψc.subtype_mk _⟩
  let fc : C(Dk, ℂ) := ⟨fun z => ψ z, hψc⟩
  have he₀D : e₀ ∈ Dk := he₀
  obtain ⟨L, -, hL⟩ := hcov.existsUnique_continuousMap_lifts fc (a₀ := ⟨e₀, he₀D⟩) (e₀ := e₀)
    rfl (fun z => hψΩ z)
  have h1 := hL ⟨Subtype.val, continuous_subtype_val⟩ ⟨rfl, rfl⟩
  have h2 := hL (σ.comp f') ⟨by
      change σ ⟨ψ e₀, _⟩ = e₀
      have : (⟨ψ e₀, hψΩ ⟨e₀, he₀D⟩⟩ : Ω) = ⟨c, hc⟩ := Subtype.ext he₀c
      rw [this, hσ₀], by
      funext z
      exact hψσ _⟩
  have hσψ : ∀ z : Dk, σ ⟨ψ z, hψΩ z⟩ = z := fun z => by
    have := congrArg (fun F : C(Dk, ℂ) => F z) (h2.trans h1.symm)
    exact this
  -- the inverse map
  classical
  let G : ℂ → ℂ := fun w => if h : w ∈ Ω then σ ⟨w, h⟩ else 0
  have hG : ∀ w (h : w ∈ Ω), G w = σ ⟨w, h⟩ := fun w h => by simp [G, h]
  have hGc : ContinuousOn G Ω := by
    rw [continuousOn_iff_continuous_restrict]
    have : Ω.restrict G = σ := by funext w; simp [Set.restrict, hG w w.2]
    rw [this]; exact σ.continuous
  refine ⟨ψ, G, fun z hz => hψΩ ⟨z, hz⟩, fun w hw => by rw [hG w hw]; exact hσD _,
    fun z hz => by rw [hG _ (hψΩ ⟨z, hz⟩)]; exact hσψ ⟨z, hz⟩,
    fun w hw => by rw [hG w hw]; exact hψσ ⟨w, hw⟩, hψd, fun w hw => ?_⟩
  have hGw : G w ∈ ball (0 : ℂ) 1 := by rw [hG w hw]; exact hσD _
  have hstrict := hasStrictDerivAt_of_differentiableOn hψd isOpen_ball hGw
  refine (differentiableAt_of_comp_eq hstrict (hψ' _ hGw) (hGc.continuousAt (hΩ.mem_nhds hw))
    ?_ differentiableAt_id).differentiableWithinAt
  filter_upwards [hΩ.mem_nhds hw] with v hv
  rw [hG v hv, hψσ ⟨v, hv⟩]
  rfl

end Disc

end AutHol

end Iut
