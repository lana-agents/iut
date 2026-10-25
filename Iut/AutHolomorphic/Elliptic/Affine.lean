/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.Punct
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# RC-holomorphic self-coverings of a complex torus are linear

**Theorem** (`exists_rc_of_rcLift`). Let `f : T_Λ → T_Λ` be continuous with `f 0 = 0`, locally
injective and holomorphic or antiholomorphic (in the coordinate `mk : ℂ → T_Λ`) near every point
outside a finite set `K`. Then `f (mk z) = mk (a z)` for all `z`, or `f (mk z) = mk (a z̄)` for
all `z`, with `a ≠ 0`. In particular `f` is a group endomorphism.

This is the classical fact ("holomorphic maps of tori are affine") used in the classification of
the elliptic cuspidalisation diagrams of [AbsTopIII] Corollary 2.7 (b). The proof:

* lift `f ∘ mk` through the covering `mk` to `F : ℂ → ℂ`, `F 0 = 0` (`ℂ` is simply connected);
* `F` is holomorphic or antiholomorphic near every point of `Ω = ℂ ∖ mk⁻¹ K`; the type is the
  same on all of `Ω`, since `Ω` is connected and a locally injective map is not both near a point
  (`deriv_eq_zero_of_both`);
* removable singularities (`differentiable_of_punctured`): `F` or `F ∘ conj` is entire;
* its derivative is `Λ`-periodic (in the appropriate variable), hence bounded, hence fixed by
  Liouville.
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus ComplexConjugate

variable {L : PeriodPair}

/-- Complex conjugation. -/
local notation "cc" => starRingEnd ℂ

/-! ### Analytic lemmas on `ℂ` -/

/-- **Removable singularities**: a continuous function that is differentiable on a punctured
neighbourhood of every point is entire. -/
theorem differentiable_of_punctured {G : ℂ → ℂ} (hc : Continuous G)
    (h : ∀ z, ∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ G w) : Differentiable ℂ G := by
  intro z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 (h z)
  have hd : DifferentiableOn ℂ G (ball z ε \ {z}) := fun w hw =>
    (hball ⟨hw.1, hw.2⟩).differentiableWithinAt
  have := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds z hε)).1 ⟨hd, hc.continuousAt⟩
  exact this.differentiableAt (ball_mem_nhds z hε)

/-- A map that is both holomorphic and antiholomorphic at `w` has derivative `0` there. -/
theorem deriv_eq_zero_of_both {F : ℂ → ℂ} {w : ℂ} (h₁ : DifferentiableAt ℂ F w)
    (h₂ : RCDiffAt true F w) : deriv F w = 0 := by
  rw [rcDiffAt_true] at h₂
  have h₃ : DifferentiableAt ℂ (cc ∘ F) w := by
    have := h₂.conj_conj
    simpa [Function.comp_def] using this
  set c := deriv F w
  set d := deriv (cc ∘ F) w
  have hF : HasFDerivAt F ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)
      w := (h₁.hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hG : HasFDerivAt (cc ∘ F)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) d).restrictScalars ℝ) w :=
    (h₃.hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have hG' : HasFDerivAt (cc ∘ F) ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)) w :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp w hF
  have heq := hG.unique hG'
  have e1 := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) heq
  have e2 := congrArg (fun T : ℂ →L[ℝ] ℂ => T Complex.I) heq
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul] at e1 e2
  have k1 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (1 * c) = cc c := by
    rw [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, one_mul]
  have k2 : (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.I * c) = -Complex.I * cc c := by
    rw [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul, Complex.conj_I]
  rw [k1] at e1
  rw [k2] at e2
  have hI : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have h2 : (2 * Complex.I) * cc c = 0 := by linear_combination (-Complex.I) * e1 + e2
  have : cc c = 0 := (mul_eq_zero.1 h2).resolve_left hI
  simpa using this

/-! ### The theorem -/

theorem rcDiffAt_congr {δ : Bool} {Φ F : ℂ → ℂ} {w : ℂ} (h : RCDiffAt δ Φ w)
    (he : F =ᶠ[𝓝 w] Φ) : RCDiffAt δ F w := by
  cases δ
  · exact (rcDiffAt_false.1 h).congr_of_eventuallyEq he
  · rw [rcDiffAt_true] at h ⊢
    have hcc : Tendsto (cc : ℂ → ℂ) (𝓝 (cc w)) (𝓝 w) := by
      have := (Complex.continuous_conj.tendsto (cc w))
      simpa using this
    have he' : (F ∘ cc) =ᶠ[𝓝 (cc w)] (Φ ∘ cc) := hcc.eventually he
    exact h.congr_of_eventuallyEq he'

theorem rcDiffAt_sub_const {δ : Bool} {Φ : ℂ → ℂ} {w : ℂ} (h : RCDiffAt δ Φ w) (c : ℂ) :
    RCDiffAt δ (fun u => Φ u - c) w := by
  have := RCDiffAt.comp (ε := false) (Φ₁ := fun u => u - c) (Φ₂ := Φ)
    (by rw [rcDiffAt_false]; fun_prop) h
  simpa [Function.comp_def] using this

/-- A lift of a map that is RC-holomorphic along `mk` is RC-holomorphic. -/
theorem rcDiffAt_of_lift {F : ℂ → ℂ} (hF : Continuous F) {z : ℂ} {δ : Bool} {Φ : ℂ → ℂ}
    (hΦ : ∀ᶠ w in 𝓝 z, RCDiffAt δ Φ w) (hΦF : ∀ᶠ w in 𝓝 z, mk L (Φ w) = mk L (F w)) :
    ∀ᶠ w in 𝓝 z, RCDiffAt δ F w := by
  have hall : ∀ᶠ w in 𝓝 z, RCDiffAt δ Φ w ∧ Φ w - F w ∈ L.lattice := by
    filter_upwards [hΦ, hΦF] with w h1 h2
    exact ⟨h1, mk_eq_mk.1 h2⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hall
  haveI : PreconnectedSpace (ball z ρ) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball z ρ).isPreconnected
  have hcont : Continuous fun w : ball z ρ => Φ w - F w := by
    refine continuous_iff_continuousAt.2 fun w => ?_
    exact (((hball w.2).1.continuousAt).sub hF.continuousAt).comp
      continuous_subtype_val.continuousAt
  have hconst : ∀ w ∈ ball z ρ, F w = Φ w - (Φ z - F z) := by
    intro w hw
    have := eq_of_mem_lattice hcont (fun w => (hball w.2).2) ⟨w, hw⟩ ⟨z, mem_ball_self hρ⟩
    simp only at this
    linear_combination -this
  filter_upwards [ball_mem_nhds z hρ] with w hw
  refine rcDiffAt_congr (rcDiffAt_sub_const (hball hw).1 (Φ z - F z)) ?_
  filter_upwards [isOpen_ball.mem_nhds hw] with u hu
  exact hconst u hu

/-- **RC-holomorphic self-coverings of `T_Λ` fixing `0` are `ℝ`-linear**: `x ↦ a x` or
`x ↦ a x̄`. -/
theorem exists_rc_of_rcLift {f : Torus L → Torus L} (hfc : Continuous f) (hf0 : f 0 = 0)
    {K : Set (Torus L)} (hK : K.Finite) (hinj : ∀ x ∉ K, ∃ N ∈ 𝓝 x, InjOn f N)
    (hloc : ∀ z, mk L z ∉ K → ∃ (δ : Bool) (Φ : ℂ → ℂ), (∀ᶠ w in 𝓝 z, RCDiffAt δ Φ w) ∧
      ∀ᶠ w in 𝓝 z, f (mk L w) = mk L (Φ w)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∃ δ : Bool, ∀ z, f (mk L z) = mk L (rc a δ z) := by
  -- the lift
  obtain ⟨F, ⟨hF0, hFf⟩, -⟩ := isCoveringMap_mk.existsUnique_continuousMap_lifts
    (⟨f ∘ mk L, hfc.comp continuous_mk⟩ : C(ℂ, Torus L)) 0 0
    (by simp [mk_zero, hf0])
  have hF : ∀ z, mk L (F z) = f (mk L z) := fun z => congrFun hFf z
  have hFc : Continuous F := F.continuous
  -- `F` is locally injective
  have hloc_inj : ∀ z, mk L z ∉ K → ∃ N ∈ 𝓝 z, InjOn F N := by
    intro z hz
    obtain ⟨N₁, hN₁, hinj₁⟩ := hinj (mk L z) hz
    obtain ⟨N₂, hN₂o, hzN₂, hN₂⟩ := isCoveringMap_mk.isLocalHomeomorph.isLocallyInjective z
    refine ⟨N₂ ∩ mk L ⁻¹' N₁, inter_mem (hN₂o.mem_nhds hzN₂)
      (continuous_mk.continuousAt.preimage_mem_nhds hN₁), fun a ha b hb hab => hN₂ ha.1 hb.1 ?_⟩
    refine hinj₁ ha.2 hb.2 ?_
    rw [← hF, ← hF, hab]
  -- the local type
  set Ω : Set ℂ := (mk L ⁻¹' K)ᶜ with hΩ
  have hΩo : IsOpen Ω := (hK.isClosed.preimage continuous_mk).isOpen_compl
  have hrc : ∀ z ∈ Ω, ∃ δ : Bool, ∀ᶠ w in 𝓝 z, RCDiffAt δ F w := by
    intro z hz
    obtain ⟨δ, Φ, hΦ, hΦe⟩ := hloc z hz
    refine ⟨δ, rcDiffAt_of_lift (L := L) hFc hΦ ?_⟩
    filter_upwards [hΦe] with w hw
    rw [hF, hw]
  set Hol : Set ℂ := Ω ∩ {z | ∀ᶠ w in 𝓝 z, RCDiffAt false F w}
  set Anti : Set ℂ := Ω ∩ {z | ∀ᶠ w in 𝓝 z, RCDiffAt true F w}
  have hHo : IsOpen Hol := hΩo.inter isOpen_setOf_eventually_nhds
  have hAo : IsOpen Anti := hΩo.inter isOpen_setOf_eventually_nhds
  have hcover : Ω ⊆ Hol ∪ Anti := by
    intro z hz
    obtain ⟨δ, hδ⟩ := hrc z hz
    cases δ
    · exact Or.inl ⟨hz, hδ⟩
    · exact Or.inr ⟨hz, hδ⟩
  have hdisj : Disjoint Hol Anti := by
    rw [Set.disjoint_left]
    rintro z ⟨hzΩ, h1⟩ ⟨-, h2⟩
    obtain ⟨N, hN, hNinj⟩ := hloc_inj z hzΩ
    have hall : ∀ᶠ w in 𝓝 z, (DifferentiableAt ℂ F w ∧ deriv F w = 0) ∧ w ∈ N := by
      filter_upwards [h1, h2, hN] with w hw1 hw2 hw3
      exact ⟨⟨hw1, deriv_eq_zero_of_both hw1 hw2⟩, hw3⟩
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hall
    have hconst : ∀ w ∈ ball z ρ, F w = F z := by
      intro w hw
      have hdo : DifferentiableOn ℂ F (ball z ρ) := fun u hu =>
        (hball hu).1.1.differentiableWithinAt
      exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z ρ).isPreconnected hdo
        (fun u hu => (hball hu).1.2) hw (mem_ball_self hρ)
    have hw : z + (ρ / 2 : ℝ) ∈ ball z ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have := hNinj (hball hw).2 (hball (mem_ball_self hρ)).2 (hconst _ hw)
    have h0 : ((ρ / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have : ρ / 2 = 0 := by exact_mod_cast h0
    linarith
  have hΩc : IsConnected Ω := isConnected_compl_preimage hK.countable
  -- a global type
  obtain ⟨δ, hδ⟩ : ∃ δ : Bool, ∀ z ∈ Ω, ∀ᶠ w in 𝓝 z, RCDiffAt δ F w := by
    obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
    rcases hcover hz₀ with h | h
    · refine ⟨false, fun z hz => ?_⟩
      exact (hΩc.isPreconnected.subset_left_of_subset_union hHo hAo hdisj hcover
        ⟨z₀, hz₀, h⟩ hz).2
    · refine ⟨true, fun z hz => ?_⟩
      exact (hΩc.isPreconnected.subset_right_of_subset_union hHo hAo hdisj hcover
        ⟨z₀, hz₀, h⟩ hz).2
  -- `G = F ∘ conj^δ` is entire
  set G : ℂ → ℂ := if δ then F ∘ cc else F with hGdef
  have hGc : Continuous G := by
    cases δ
    · exact hFc
    · exact hFc.comp Complex.continuous_conj
  have hGd : Differentiable ℂ G := by
    refine differentiable_of_punctured hGc fun z => ?_
    cases δ
    · filter_upwards [eventually_notMem_preimage hK z] with w hw
      exact rcDiffAt_false.1 (hδ w hw).self_of_nhds
    · have hcc : Tendsto (cc : ℂ → ℂ) (𝓝[≠] z) (𝓝[≠] (cc z)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (Complex.continuous_conj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact fun h => hw (by simpa using congrArg cc h)
      filter_upwards [hcc.eventually (eventually_notMem_preimage hK (cc z))] with w hw
      have := rcDiffAt_true.1 (hδ (cc w) hw).self_of_nhds
      simpa [G] using this
  -- periodicity
  have hper : ∀ l ∈ L.lattice, ∃ c, ∀ z, F (z + l) = F z + c := by
    intro l hl
    have hΛ : ∀ z, F (z + l) - F z ∈ L.lattice := fun z => by
      rw [← mk_eq_mk, hF, hF, mk_add, (mk_eq_zero (L := L)).2 hl, add_zero]
    refine ⟨F (0 + l) - F 0, fun z => ?_⟩
    have := eq_of_mem_lattice (Z := ℂ) (by fun_prop) hΛ z 0
    linear_combination this
  set h : ℂ → ℂ := fun z => deriv G (if δ then cc z else z) with hh
  have hhc : Continuous h := by
    have := hGd.deriv.continuous
    cases δ
    · exact this
    · exact this.comp Complex.continuous_conj
  have hhp : ∀ z, ∀ l ∈ L.lattice, h (z + l) = h z := by
    intro z l hl
    obtain ⟨c, hc⟩ := hper l hl
    cases δ
    · have : G = F := rfl
      simp only [hh, if_neg Bool.false_ne_true, this]
      have h1 : (fun u => F (u + l)) = fun u => F u + c := funext fun u => hc u
      have h2 : deriv (fun u => F (u + l)) z = deriv F (z + l) := deriv_comp_add_const _ _ _
      rw [← h2, h1, deriv_add_const]
    · have : G = F ∘ cc := rfl
      simp only [hh, if_pos, this, map_add]
      have h1 : (fun u => (F ∘ cc) (u + cc l)) = fun u => (F ∘ cc) u + c := by
        funext u
        simp [hc]
      have h2 : deriv (fun u => (F ∘ cc) (u + cc l)) (cc z) = deriv (F ∘ cc) (cc z + cc l) :=
        deriv_comp_add_const _ _ _
      rw [← h2, h1, deriv_add_const]
  obtain ⟨M, hM⟩ := exists_bound_of_periodic hhc hhp
  have hbd : Bornology.IsBounded (range (deriv G)) := by
    refine isBounded_iff_forall_norm_le.2 ⟨M, ?_⟩
    rintro _ ⟨w, rfl⟩
    have := hM (if δ then cc w else w)
    cases δ <;> simpa [hh] using this
  set a := deriv G 0
  have hda : ∀ w, deriv G w = a := fun w => hGd.deriv.apply_eq_apply_of_bounded hbd w 0
  have hG0 : G 0 = 0 := by cases δ <;> simp [G, hF0]
  have hGa : ∀ w, G w = a * w := by
    intro w
    have hd : Differentiable ℂ (fun u => G u - a * u) := hGd.sub (by fun_prop)
    have := is_const_of_deriv_eq_zero hd (fun u => by
      have hd' : HasDerivAt (fun u => G u - a * u) (deriv G u - a * 1) u :=
        (hGd u).hasDerivAt.sub ((hasDerivAt_id' u).const_mul a)
      rw [hd'.deriv, hda u]
      ring) w 0
    rw [hG0] at this
    linear_combination this
  have hFa : ∀ z, F z = rc a δ z := by
    intro z
    cases δ
    · exact hGa z
    · have := hGa (cc z)
      simpa [G, rc] using this
  -- `a ≠ 0`
  have ha : a ≠ 0 := by
    intro ha0
    obtain ⟨z₀, hz₀⟩ := hΩc.nonempty
    obtain ⟨N, hN, hNinj⟩ := hloc_inj z₀ hz₀
    obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hN
    have hw : z₀ + ((ρ / 2 : ℝ) : ℂ) ∈ ball z₀ ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have := hNinj (hball hw) (hball (mem_ball_self hρ))
      (by rw [hFa, hFa, ha0]; cases δ <;> simp [rc])
    have h0 : ((ρ / 2 : ℝ) : ℂ) = 0 := by linear_combination this
    have : ρ / 2 = 0 := by exact_mod_cast h0
    linarith
  exact ⟨a, ha, δ, fun z => by rw [← hF, hFa]⟩

end Ell

end AutHol

end Iut
