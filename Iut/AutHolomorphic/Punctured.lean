/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Basic
import Iut.AutHolomorphic.EntireAut

/-!
# The Aut-holomorphic punctured plane `ℂ^×` (IUT I, Remark 3.4.2)

IUT I, Remark 3.4.2, recasts the archimedean Kummer structure `κ_v : O^▷(C_v) ↪ A_{D_v}` as the
Aut-holomorphic structure on the groupification `O^▷(C_v)^gp ≅ ℂ^×` together with a
co-holomorphicization, using "the elementary fact that every holomorphic automorphism of the
complex Lie group `ℂ^×` that preserves the submonoid of elements of norm `≤ 1` is equal to the
identity". This file proves the underlying classification.

* `punct = ofEmbedding (↑)`: the Aut-holomorphic structure of `ℂ^× = ℂ ∖ {0}`.
* `mem_global_punct`: **`A_{ℂ^×}(ℂ^×)` consists of the maps `z ↦ a z` and `z ↦ a / z`**
  (`a ≠ 0`). Proof: a holomorphic homeomorphism of `ℂ^×` is proper, so near `0` (and near `∞`)
  it tends to `0` or to `∞` (the punctured discs are connected); in the first case Riemann's
  removable singularity theorem extends it to an injective proper entire function, which is
  affine (`exists_affine_of_proper`); the second case reduces to the first by `w ↦ 1/w`.
* `eq_id_of_mul_of_monoid`: **a holomorphic automorphism of `ℂ^×` which is a group homomorphism
  and preserves `{|z| ≤ 1}` is the identity** (IUT I, Remark 3.4.2).
-/

namespace Iut

namespace AutHol

open Set Filter Topology Metric TopologicalSpace

/-- `ℂ^× = ℂ ∖ {0}`. -/
abbrev Punct : Type := {z : ℂ // z ≠ 0}

/-- **The Aut-holomorphic punctured plane.** -/
noncomputable def punct : AutHolStr Punct := ofEmbedding Subtype.val

/-! ### Compact annuli and properness -/

/-- The closed annulus `ε ≤ |z| ≤ ε⁻¹` in `ℂ^×`. -/
def ann (ε : ℝ) : Set Punct := {w | ε ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ ε⁻¹}

theorem isCompact_ann {ε : ℝ} (hε : 0 < ε) : IsCompact (ann ε) := by
  rw [Subtype.isCompact_iff]
  have : ((↑) : Punct → ℂ) '' ann ε = {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ ε⁻¹} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp only [norm_zero, mem_setOf_eq] at hz
        linarith [hz.1]
      exact ⟨⟨z, hz0⟩, hz, rfl⟩
  rw [this]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · refine (isBounded_closedBall (x := (0 : ℂ)) (r := ε⁻¹)).subset fun z hz => ?_
    simpa using hz.2

/-- **Properness of a homeomorphism of `ℂ^×`**: points near `0` or `∞` go near `0` or `∞`. -/
theorem exists_delta (f : Punct ≃ₜ Punct) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z : Punct, (‖(z : ℂ)‖ < δ ∨ δ⁻¹ < ‖(z : ℂ)‖) →
      (‖(f z : ℂ)‖ < ε ∨ ε⁻¹ < ‖(f z : ℂ)‖) := by
  have hL : IsCompact (f.symm '' ann ε) := (isCompact_ann hε).image f.symm.continuous
  obtain ⟨M₁, hM₁⟩ := hL.exists_bound_of_continuousOn
    (f := fun w : Punct => ‖(w : ℂ)‖) (continuous_norm.comp continuous_subtype_val).continuousOn
  obtain ⟨M₂, hM₂⟩ := hL.exists_bound_of_continuousOn (f := fun w : Punct => ‖(w : ℂ)‖⁻¹)
    (by
      refine ContinuousOn.inv₀ (continuous_norm.comp continuous_subtype_val).continuousOn ?_
      intro w _
      exact norm_ne_zero_iff.2 w.2)
  set M := max (max M₁ M₂) 0 + 1 with hM
  have hMpos : 0 < M := by
    have := le_max_right (max M₁ M₂) 0
    linarith
  refine ⟨M⁻¹, inv_pos.2 hMpos, fun z hz => ?_⟩
  by_contra hcon
  push Not at hcon
  have hzL : z ∈ f.symm '' ann ε := ⟨f z, hcon, f.symm_apply_apply z⟩
  have h1 := hM₁ z hzL
  have h2 := hM₂ z hzL
  rw [Real.norm_of_nonneg (norm_nonneg _)] at h1
  rw [Real.norm_of_nonneg (inv_nonneg.2 (norm_nonneg _))] at h2
  have hzpos : 0 < ‖(z : ℂ)‖ := norm_pos_iff.2 z.2
  have hmax1 : M₁ ≤ max (max M₁ M₂) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmax2 : M₂ ≤ max (max M₁ M₂) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  rcases hz with hz | hz
  · have : M < ‖(z : ℂ)‖⁻¹ := (lt_inv_comm₀ hzpos hMpos).1 hz
    linarith
  · rw [inv_inv] at hz
    linarith

/-! ### Connectedness of punctured discs and of neighbourhoods of `∞` -/

theorem isPreconnected_norm_preimage {S : Set ℝ} (hS : IsPreconnected S)
    (hpos : ∀ t ∈ S, 0 < t) : IsPreconnected {z : ℂ | ‖z‖ ∈ S} := by
  have : {z : ℂ | ‖z‖ ∈ S} =
      (fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I)) '' (S ×ˢ univ) := by
    ext z
    constructor
    · intro hz
      exact ⟨(‖z‖, Complex.arg z), ⟨hz, trivial⟩, Complex.norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨⟨t, θ⟩, ⟨ht, -⟩, rfl⟩
      simp only [mem_setOf_eq, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
        mul_one, Real.norm_eq_abs, abs_of_pos (hpos t ht)]
      exact ht
  rw [this]
  exact (hS.prod isPreconnected_univ).image _ (by fun_prop : Continuous _).continuousOn

/-- On a preconnected set where `|F| < 1/2` or `|F| > 2`, one of the two holds everywhere. -/
theorem dichotomy {F : ℂ → ℂ} {T : Set ℂ} (hT : IsPreconnected T) (hc : ContinuousOn F T)
    (h : ∀ z ∈ T, ‖F z‖ < 1 / 2 ∨ 2 < ‖F z‖) :
    (∀ z ∈ T, ‖F z‖ < 1 / 2) ∨ (∀ z ∈ T, 2 < ‖F z‖) := by
  rcases (hT.image F hc).subset_or_subset
      (isOpen_lt continuous_norm continuous_const : IsOpen {w : ℂ | ‖w‖ < 1 / 2})
      (isOpen_lt continuous_const continuous_norm : IsOpen {w : ℂ | 2 < ‖w‖})
      (Set.disjoint_left.2 fun w hw1 hw2 => by
        simp only [mem_setOf_eq] at hw1 hw2
        linarith)
      (by
        rintro _ ⟨z, hz, rfl⟩
        exact h z hz) with h1 | h2
  · exact Or.inl fun z hz => h1 ⟨z, hz, rfl⟩
  · exact Or.inr fun z hz => h2 ⟨z, hz, rfl⟩

/-! ### The core case: small near `0` -/

/-- **A holomorphic, injective, proper self-map of `ℂ^×` which is small near `0` is linear.** -/
theorem exists_linear_of_small {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F {0}ᶜ)
    (hinj : InjOn F {0}ᶜ) (hne : ∀ z ≠ 0, F z ≠ 0)
    (hprop : ∀ ε > 0, ∃ δ > 0, ∀ z ≠ 0, (‖z‖ < δ ∨ δ⁻¹ < ‖z‖) → (‖F z‖ < ε ∨ ε⁻¹ < ‖F z‖))
    (hsmall : ∃ r > 0, ∀ z ≠ 0, ‖z‖ < r → ‖F z‖ < 1 / 2) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ z ≠ 0, F z = a * z := by
  obtain ⟨r, hr, hrs⟩ := hsmall
  -- `F → 0` at `0`
  have htend0 : Tendsto F (𝓝[≠] 0) (𝓝 0) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₁, hδ₁, hδ₁s⟩ := hprop (min ε (1 / 2)) (by positivity)
    refine ⟨min δ₁ r, by positivity, fun {x} hx hxd => ?_⟩
    have hx0 : x ≠ 0 := hx
    rw [dist_zero_right] at hxd ⊢
    have h1 := hxd.trans_le (min_le_left _ _)
    have h2 := hxd.trans_le (min_le_right _ _)
    rcases hδ₁s x hx0 (Or.inl h1) with h | h
    · exact h.trans_le (min_le_left _ _)
    · exfalso
      have hle : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _
      have : (2 : ℝ) ≤ (min ε (1 / 2))⁻¹ := by
        rw [le_inv_comm₀ (by norm_num) (by positivity)]
        linarith
      linarith [hrs x hx0 h2]
  set G : ℂ → ℂ := Function.update F 0 0 with hGdef
  have hGF : ∀ z ≠ 0, G z = F z := fun z hz => Function.update_of_ne hz _ _
  have hG0 : G 0 = 0 := Function.update_self _ _ _
  have hGd : Differentiable ℂ G := by
    have hcont : ContinuousAt G 0 := by
      rw [continuousAt_iff_punctured_nhds, hG0]
      exact htend0.congr' (eventually_nhdsWithin_of_forall fun z hz => (hGF z hz).symm)
    have h := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (f := G) (s := univ) (c := 0) univ_mem).1
      ⟨(hd.mono fun z hz => hz.2).congr fun z hz => hGF z hz.2, hcont⟩
    exact fun z => (h z (mem_univ z)).differentiableAt (by simp)
  have hGinj : Function.Injective G := by
    intro z w hzw
    by_cases hz : z = 0
    · by_cases hw : w = 0
      · rw [hz, hw]
      · rw [hz, hG0, hGF w hw] at hzw
        exact absurd hzw.symm (hne w hw)
    · by_cases hw : w = 0
      · rw [hw, hG0, hGF z hz] at hzw
        exact absurd hzw (hne z hz)
      · rw [hGF z hz, hGF w hw] at hzw
        exact hinj hz hw hzw
  -- behaviour at `∞`
  obtain ⟨δ₀, hδ₀, hδ₀s⟩ := hprop (1 / 2) (by norm_num)
  have hT : IsPreconnected {z : ℂ | ‖z‖ ∈ Ioi δ₀⁻¹} :=
    isPreconnected_norm_preimage isPreconnected_Ioi fun t ht => lt_trans (by positivity) ht
  have hTne : ∀ z ∈ {z : ℂ | ‖z‖ ∈ Ioi δ₀⁻¹}, z ≠ 0 := by
    intro z hz h0
    simp only [mem_setOf_eq, mem_Ioi, h0, norm_zero] at hz
    linarith [inv_pos.2 hδ₀]
  have hdich := dichotomy hT (hd.continuousOn.mono fun z hz => hTne z hz) (fun z hz => by
    have := hδ₀s z (hTne z hz) (Or.inr hz)
    rwa [one_div, inv_inv, ← one_div] at this)
  have hGprop : Tendsto G (cocompact ℂ) (cocompact ℂ) := by
    rcases hdich with hsm | hlg
    · exfalso
      -- `G` is bounded, hence takes a single value
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) δ₀⁻¹).exists_bound_of_continuousOn
        hGd.continuous.continuousOn
      have hbdd : Bornology.IsBounded (range G) := by
        refine isBounded_iff_forall_norm_le.2 ⟨max C (1 / 2), ?_⟩
        rintro _ ⟨z, rfl⟩
        by_cases hz : ‖z‖ ≤ δ₀⁻¹
        · exact (hC z (by simpa using hz)).trans (le_max_left _ _)
        · push Not at hz
          rw [hGF z (hTne z hz)]
          exact (hsm z hz).le.trans (le_max_right _ _)
      have := hGd.apply_eq_apply_of_bounded hbdd 1 0
      exact one_ne_zero (hGinj this)
    · rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded]
      refine tendsto_atTop.2 fun M => ?_
      obtain ⟨δ, hδ, hδs⟩ := hprop (min (1 / 2) (1 / (|M| + 1))) (by positivity)
      have hev := (tendsto_norm_cobounded_atTop :
          Tendsto (norm : ℂ → ℝ) (Bornology.cobounded ℂ) atTop).eventually
        (eventually_gt_atTop (max δ⁻¹ δ₀⁻¹))
      refine hev.mono fun z hz => ?_
      have hz1 : δ⁻¹ < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
      have hz2 : z ∈ {z : ℂ | ‖z‖ ∈ Ioi δ₀⁻¹} := lt_of_le_of_lt (le_max_right _ _) hz
      have hz0 := hTne z hz2
      have hlarge := hlg z hz2
      rw [hGF z hz0]
      have hεpos : 0 < min (1 / 2) (1 / (|M| + 1)) := by positivity
      rcases hδs z hz0 (Or.inr hz1) with h | h
      · exfalso
        have : min (1 / 2) (1 / (|M| + 1)) ≤ 1 / 2 := min_le_left _ _
        linarith
      · have hle : |M| + 1 ≤ (min (1 / 2) (1 / (|M| + 1)))⁻¹ := by
          rw [le_inv_comm₀ (by positivity) hεpos, ← one_div]
          exact min_le_right _ _
        linarith [le_abs_self M]
  obtain ⟨a, b, ha, hab⟩ := exists_affine_of_proper hGd hGinj hGprop
  have hb : b = 0 := by
    have := hab 0
    rw [hG0, mul_zero, zero_add] at this
    exact this.symm
  refine ⟨a, ha, fun z hz => ?_⟩
  rw [← hGF z hz, hab, hb, add_zero]

/-! ### Holomorphic automorphisms of `ℂ^×` -/

theorem image_val_top_punct : ((↑) : Punct → ℂ) '' ((⊤ : Opens Punct) : Set Punct) = {0}ᶜ := by
  ext z
  constructor
  · rintro ⟨w, -, rfl⟩
    exact w.2
  · intro hz
    exact ⟨⟨z, hz⟩, by simp, rfl⟩

theorem holIn_top_punct_iff {g : (⊤ : Opens Punct) → (⊤ : Opens Punct)} :
    HolIn ((↑) : Punct → ℂ) ((⊤ : Opens Punct) : Set Punct) g ↔
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {0}ᶜ ∧
        ∀ z : Punct, ((g ⟨z, by simp⟩ : Punct) : ℂ) = F z := by
  rw [HolIn, image_val_top_punct]
  exact exists_congr fun F => and_congr Iff.rfl ⟨fun h z => h ⟨z, by simp⟩, fun h x => h x.1⟩

/-- **`A_{ℂ^×}(ℂ^×)` consists of the maps `z ↦ a z` and `z ↦ a / z`.** -/
theorem mem_global_punct {f : Punct ≃ₜ Punct} :
    f ∈ punct.global ↔
      ∃ a : ℂ, a ≠ 0 ∧ ((∀ z : Punct, (f z : ℂ) = a * z) ∨ (∀ z : Punct, (f z : ℂ) = a / z)) := by
  rw [AutHolStr.mem_global]
  change HolIn _ _ _ ∧ HolIn _ _ _ ↔ _
  rw [holIn_top_punct_iff, holIn_top_punct_iff]
  constructor
  · rintro ⟨⟨F, hFd, hFf⟩, -⟩
    have hFf' : ∀ z : Punct, (f z : ℂ) = F z := hFf
    have hne : ∀ z ≠ 0, F z ≠ 0 := fun z hz => by
      rw [← hFf' ⟨z, hz⟩]
      exact (f ⟨z, hz⟩).2
    have hinj : InjOn F {0}ᶜ := by
      intro z hz w hw hzw
      rw [← hFf' ⟨z, hz⟩, ← hFf' ⟨w, hw⟩] at hzw
      have := f.injective (Subtype.ext hzw)
      exact congrArg Subtype.val this
    have hprop : ∀ ε > 0, ∃ δ > 0, ∀ z ≠ 0, (‖z‖ < δ ∨ δ⁻¹ < ‖z‖) →
        (‖F z‖ < ε ∨ ε⁻¹ < ‖F z‖) := by
      intro ε hε
      obtain ⟨δ, hδ, hδs⟩ := exists_delta f hε
      refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
      have := hδs ⟨z, hz⟩ hzδ
      rwa [hFf'] at this
    -- dichotomy at `0`
    obtain ⟨δ₀, hδ₀, hδ₀s⟩ := hprop (1 / 2) (by norm_num)
    have hT : IsPreconnected {z : ℂ | ‖z‖ ∈ Ioo 0 δ₀} :=
      isPreconnected_norm_preimage isPreconnected_Ioo fun t ht => ht.1
    have hTne : ∀ z ∈ {z : ℂ | ‖z‖ ∈ Ioo 0 δ₀}, z ≠ 0 := fun z hz =>
      norm_pos_iff.1 hz.1
    rcases dichotomy hT (hFd.continuousOn.mono fun z hz => hTne z hz) (fun z hz => by
        have := hδ₀s z (hTne z hz) (Or.inl hz.2)
        rwa [one_div, inv_inv, ← one_div] at this) with hsm | hlg
    · obtain ⟨a, ha, haF⟩ := exists_linear_of_small hFd hinj hne hprop
        ⟨δ₀, hδ₀, fun z hz hzδ => hsm z ⟨norm_pos_iff.2 hz, hzδ⟩⟩
      exact ⟨a, ha, Or.inl fun z => by rw [hFf', haF z z.2]⟩
    · have hd' : DifferentiableOn ℂ (fun z => (F z)⁻¹) {0}ᶜ :=
        hFd.inv fun z hz => hne z hz
      have hinj' : InjOn (fun z => (F z)⁻¹) {0}ᶜ := fun z hz w hw hzw =>
        hinj hz hw (inv_injective hzw)
      have hne' : ∀ z ≠ 0, (F z)⁻¹ ≠ 0 := fun z hz => inv_ne_zero (hne z hz)
      have hprop' : ∀ ε > 0, ∃ δ > 0, ∀ z ≠ 0, (‖z‖ < δ ∨ δ⁻¹ < ‖z‖) →
          (‖(F z)⁻¹‖ < ε ∨ ε⁻¹ < ‖(F z)⁻¹‖) := by
        intro ε hε
        obtain ⟨δ, hδ, hδs⟩ := hprop ε hε
        refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
        have hFpos : 0 < ‖F z‖ := norm_pos_iff.2 (hne z hz)
        rw [norm_inv]
        rcases hδs z hz hzδ with h | h
        · exact Or.inr ((inv_lt_inv₀ hε hFpos).2 h)
        · exact Or.inl ((inv_lt_comm₀ hε hFpos).1 h)
      obtain ⟨a, ha, haF⟩ := exists_linear_of_small hd' hinj' hne' hprop'
        ⟨δ₀, hδ₀, fun z hz hzδ => by
          have h2 := hlg z ⟨norm_pos_iff.2 hz, hzδ⟩
          rw [norm_inv]
          rw [inv_lt_comm₀ (by linarith) (by norm_num)]
          norm_num
          exact h2⟩
      refine ⟨a⁻¹, inv_ne_zero ha, Or.inr fun z => ?_⟩
      have h1 := haF z z.2
      rw [hFf']
      have hF0 := hne z z.2
      have hz0 := z.2
      rw [inv_eq_iff_eq_inv] at h1
      rw [h1, mul_inv, div_eq_mul_inv]
  · rintro ⟨a, ha, h | h⟩
    · refine ⟨⟨fun z => a * z, by fun_prop, fun z => h z⟩, ⟨fun z => z / a, by fun_prop,
        fun z => ?_⟩⟩
      change ((f.symm z : Punct) : ℂ) = (z : ℂ) / a
      have := h (f.symm z)
      rw [Homeomorph.apply_symm_apply] at this
      rw [eq_div_iff ha, this, mul_comm]
    · refine ⟨⟨fun z => a / z, ?_, fun z => h z⟩, ⟨fun z => a / z, ?_, fun z => ?_⟩⟩
      · exact (differentiableOn_const a).div differentiableOn_id fun z hz => hz
      · exact (differentiableOn_const a).div differentiableOn_id fun z hz => hz
      · change ((f.symm z : Punct) : ℂ) = a / (z : ℂ)
        have := h (f.symm z)
        rw [Homeomorph.apply_symm_apply] at this
        have hs0 := (f.symm z).2
        rw [this, div_div_cancel₀ ha]

/-- **IUT I, Remark 3.4.2**: a holomorphic automorphism of the complex Lie group `ℂ^×` (an
element of `A_{ℂ^×}(ℂ^×)` which is a group homomorphism) that preserves the submonoid
`{|z| ≤ 1}` is the identity. -/
theorem eq_id_of_mul_of_monoid {f : Punct ≃ₜ Punct} (hf : f ∈ punct.global)
    (hmul : ∀ z w : Punct, (f ⟨z * w, mul_ne_zero z.2 w.2⟩ : ℂ) = f z * f w)
    (hmon : ∀ z : Punct, ‖(z : ℂ)‖ ≤ 1 → ‖(f z : ℂ)‖ ≤ 1) : ∀ z, f z = z := by
  obtain ⟨a, ha, h | h⟩ := mem_global_punct.1 hf
  · have h1 := hmul ⟨1, one_ne_zero⟩ ⟨1, one_ne_zero⟩
    simp only [h, mul_one] at h1
    have ha1 : a = 1 := by
      have : a * (a - 1) = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 ha
      · linear_combination h0
    intro z
    apply Subtype.ext
    rw [h, ha1, one_mul]
  · exfalso
    have h1 := hmul ⟨1, one_ne_zero⟩ ⟨1, one_ne_zero⟩
    simp only [h, mul_one, div_one] at h1
    have ha1 : a = 1 := by
      have : a * (a - 1) = 0 := by linear_combination -h1
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 ha
      · linear_combination h0
    have h2 := hmon ⟨1 / 2, by norm_num⟩ (by norm_num)
    rw [h, ha1] at h2
    norm_num at h2

end AutHol

end Iut
