/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Oka.Uniformization.Holomorphic

/-!
# Holomorphic automorphisms of `ℂ` are affine

The classical fact behind the Aut-holomorphic structure of the plane ([AbsTopIII], Definition
2.1(i), applied to `X = ℂ`): **an entire function which is a homeomorphism `ℂ ≃ₜ ℂ` is of the form
`z ↦ a z + b` with `a ≠ 0`** (`exists_affine_of_homeomorph`).

Proof. Normalise `f(0) = 0`. Since `f` is a homeomorphism it is proper, so `‖f z‖ → ∞` as
`‖z‖ → ∞`, and `G(w) = 1 / f(1/w)` (with `G 0 = 0`) is continuous at `0` and holomorphic on
`ℂ ∖ {0}`; by Riemann's removable singularity theorem it is entire. It is injective, hence
`G′(0) ≠ 0` (`Uniformization.deriv_ne_zero_of_injOn`), so `‖G w‖ ≥ (‖G′(0)‖ / 2) ‖w‖` near `0`,
i.e. `‖f z‖ ≤ C ‖z‖` near `∞`. Then `f(z) / z` (`dslope f 0`) is a bounded entire function,
independent of `z` by Liouville's theorem.
-/

namespace Iut

namespace AutHol

open Filter Topology Metric Set

/-- The function `w ↦ 1 / f(1/w)` (with the convention `0⁻¹ = 0`). -/
noncomputable def invConj (f : ℂ → ℂ) (w : ℂ) : ℂ := (f w⁻¹)⁻¹

theorem invConj_injective {f : ℂ → ℂ} (hf : Function.Injective f) :
    Function.Injective (invConj f) := by
  intro w w' h
  simp only [invConj, inv_inj] at h
  exact inv_injective (hf h)

theorem invConj_zero {f : ℂ → ℂ} (h0 : f 0 = 0) : invConj f 0 = 0 := by
  simp [invConj, h0]

/-- `w ↦ 1 / f(1/w)` is holomorphic off `0` when `f` is entire and injective with `f 0 = 0`. -/
theorem differentiableAt_invConj {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hf : Function.Injective f) (h0 : f 0 = 0) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (invConj f) w := by
  have hfw : f w⁻¹ ≠ 0 := by
    intro h
    rw [← h0] at h
    exact inv_ne_zero hw (hf h)
  exact ((hd _).comp w (differentiableAt_inv hw)).inv hfw

/-- `w ↦ 1 / f(1/w)` is continuous at `0` when `f` is proper with `f 0 = 0`. -/
theorem continuousAt_invConj {f : ℂ → ℂ} (h0 : f 0 = 0)
    (hp : Tendsto f (cocompact ℂ) (cocompact ℂ)) : ContinuousAt (invConj f) 0 := by
  rw [continuousAt_iff_punctured_nhds, invConj_zero h0]
  have h1 : Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] 0) (cocompact ℂ) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_nhdsNE_zero
  have h2 := hp.comp h1
  rw [← Metric.cobounded_eq_cocompact] at h2
  exact tendsto_inv₀_cobounded.comp h2

theorem differentiable_invConj {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hf : Function.Injective f) (h0 : f 0 = 0)
    (hp : Tendsto f (cocompact ℂ) (cocompact ℂ)) : Differentiable ℂ (invConj f) := by
  have h := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (f := invConj f) (s := univ) (c := 0) univ_mem).1
    ⟨fun w hw => (differentiableAt_invConj hd hf h0 hw.2).differentiableWithinAt,
      continuousAt_invConj h0 hp⟩
  exact fun w => (h w (mem_univ w)).differentiableAt (by simp)

/-- **Linear growth at infinity**: `‖f z‖ ≤ C ‖z‖` for large `‖z‖`. -/
theorem exists_linear_bound {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hf : Function.Injective f) (h0 : f 0 = 0)
    (hp : Tendsto f (cocompact ℂ) (cocompact ℂ)) :
    ∃ R C : ℝ, 0 < R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ C * ‖z‖ := by
  set G := invConj f
  have hG : Differentiable ℂ G := differentiable_invConj hd hf h0 hp
  have hG0 : G 0 = 0 := invConj_zero h0
  have hc : deriv G 0 ≠ 0 :=
    Uniformization.deriv_ne_zero_of_injOn hG.differentiableOn univ_mem
      (invConj_injective hf).injOn
  set c := deriv G 0
  have hslope : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 c) :=
    hasDerivAt_iff_tendsto_slope.1 (hG 0).hasDerivAt
  have hpos : 0 < ‖c‖ / 2 := by positivity
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), ‖c‖ / 2 < ‖slope G 0 w‖ :=
    (continuous_norm.tendsto c).comp hslope |>.eventually (lt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1
    (eventually_nhdsWithin_iff.1 hev)
  refine ⟨2 / δ, 2 / ‖c‖, by positivity, fun z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    have : 0 < 2 / δ := by positivity
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hw : z⁻¹ ∈ ball (0 : ℂ) δ := by
    rw [mem_ball, dist_zero_right, norm_inv]
    rw [div_le_iff₀ hδ] at hz
    rw [inv_lt_comm₀ hzpos hδ, ← one_div, div_lt_iff₀ hδ]
    linarith
  have hb := hball _ hw (inv_ne_zero hz0)
  rw [slope_def_field, sub_zero, hG0, sub_zero] at hb
  simp only [G, invConj, inv_inv] at hb
  have hfz : f z ≠ 0 := by
    intro h
    rw [← h0] at h
    exact hz0 (hf h)
  rw [norm_div, norm_inv, norm_inv, div_inv_eq_mul] at hb
  have hfpos : 0 < ‖f z‖ := norm_pos_iff.2 hfz
  have key : ‖c‖ * ‖f z‖ < 2 * ‖z‖ := by
    have h2 : ‖f z‖⁻¹ * ‖z‖ * (2 * ‖f z‖) = 2 * ‖z‖ := by field_simp
    have h3 : ‖c‖ * 2⁻¹ * (2 * ‖f z‖) = ‖c‖ * ‖f z‖ := by field_simp
    nlinarith [mul_lt_mul_of_pos_right hb (by positivity : (0 : ℝ) < 2 * ‖f z‖)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.2 hc)]
  linarith

/-- **An injective proper entire function is affine.** -/
theorem exists_affine_of_proper {f : ℂ → ℂ} (hd : Differentiable ℂ f)
    (hf : Function.Injective f) (hp : Tendsto f (cocompact ℂ) (cocompact ℂ)) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  set g : ℂ → ℂ := fun z => f z - f 0
  have hgd : Differentiable ℂ g := hd.sub_const _
  have hg : Function.Injective g := fun z w h => hf (sub_left_injective h)
  have hg0 : g 0 = 0 := sub_self _
  have hgp : Tendsto g (cocompact ℂ) (cocompact ℂ) := by
    have : Tendsto (fun y : ℂ => y - f 0) (cocompact ℂ) (cocompact ℂ) :=
      (Homeomorph.subRight (f 0)).isClosedEmbedding.tendsto_cocompact
    exact this.comp hp
  obtain ⟨R, C, hR, hRC⟩ := exists_linear_bound hgd hg hg0 hgp
  set h := dslope g 0
  have hhd : Differentiable ℂ h := fun z =>
    ((Complex.differentiableOn_dslope (f := g) (s := univ) (c := 0) univ_mem).2
      hgd.differentiableOn z (mem_univ z)).differentiableAt (by simp)
  have hbdd : Bornology.IsBounded (range h) := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      hhd.continuous.continuousOn
    refine isBounded_iff_forall_norm_le.2 ⟨max M C, ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ R
    · exact (hM z (by simpa using hz)).trans (le_max_left _ _)
    · push Not at hz
      have hz0 : z ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hz
        linarith
      have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
      rw [show h z = dslope g 0 z from rfl, dslope_of_ne _ hz0, slope_def_field, sub_zero, hg0,
        sub_zero, norm_div]
      rw [div_le_iff₀ hzpos]
      exact (hRC z hz.le).trans (by nlinarith [le_max_right M C])
  have hconst : ∀ z, h z = h 0 := fun z => hhd.apply_eq_apply_of_bounded hbdd z 0
  refine ⟨h 0, f 0, ?_, fun z => ?_⟩
  · intro ha
    have h1 : g 1 = 0 := by
      have := hconst 1
      rw [show h 1 = dslope g 0 1 from rfl, dslope_of_ne _ one_ne_zero, slope_def_field,
        sub_zero, hg0, sub_zero, div_one, ha] at this
      exact this
    exact one_ne_zero (hg (h1.trans hg0.symm))
  · by_cases hz : z = 0
    · simp [hz]
    · have := hconst z
      rw [show h z = dslope g 0 z from rfl, dslope_of_ne _ hz, slope_def_field, sub_zero, hg0,
        sub_zero] at this
      have hgz : g z = h 0 * z := by
        rw [← this]
        field_simp
      simp only [g] at hgz
      linear_combination hgz

/-- **Entire homeomorphisms of `ℂ` are affine**: `f z = a z + b` with `a ≠ 0`. -/
theorem exists_affine_of_homeomorph (f : ℂ ≃ₜ ℂ) (hd : Differentiable ℂ f) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b :=
  exists_affine_of_proper hd f.injective f.isClosedEmbedding.tendsto_cocompact

end AutHol

end Iut
