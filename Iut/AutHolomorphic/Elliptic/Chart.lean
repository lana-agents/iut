/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.LinearHol
import Iut.AutHolomorphic.LocalRC
import Iut.AutHolomorphic.Morphism

/-!
# Morphisms into the complex torus are RC-holomorphic ([AbsTopIII] Corollary 2.3 (i))

For the complex torus `T_Λ` with its Aut-holomorphic structure `torusStr L` (holomorphy along
`mk : ℂ → T_Λ`):

* `isMorphism_mk`: for an open `S ⊆ ℂ`, the map `mk : S → T_Λ` is a morphism of Aut-holomorphic
  spaces, `S` carrying `ofEmbedding (↑)` (the charts of `T_Λ` are isomorphisms onto their images);
  the comparison of the two notions of holomorphy is `holIn_conj_iff`;
* **`exists_rcLift_of_isMorphism`** ([AbsTopIII] Corollary 2.3 (i) for open subsets of `T_Λ`): a
  morphism of Aut-holomorphic spaces `φ : U → T_Λ`, `U ⊆ T_Λ` open, lifts near every point of
  `mk⁻¹ U` to a map `ℂ → ℂ` that is holomorphic or antiholomorphic there. The proof passes
  through charts to `rcDiff_of_isMorphism` (Corollary 2.3 (i) for open subsets of `ℂ`, which rests
  on Proposition 2.2 (i) and the Riemann mapping theorem).
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace Metric Torus

variable {L : PeriodPair}

/-- Local version of `rcAlong_of_lift`: the lift only needs to be (anti)holomorphic on `W`. -/
theorem rcAlong_of_lift' {W : Set ℂ} (hW : IsOpen W) {S : Set (Torus L)} (hS : S ⊆ mk L '' W)
    {φ : ℂ → ℂ} {δ : Bool} (hφ : ∀ w ∈ W, RCDiffAt δ φ w) {G : Torus L → Torus L}
    (hG : ∀ z ∈ W, G (mk L z) = mk L (φ z)) : RCAlong (mk L) S G δ := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hS hz
  have hl : z - w ∈ L.lattice := mk_eq_mk.1 hwz.symm
  have hev : ∀ᶠ u in 𝓝 z, u - (z - w) ∈ W := by
    have h1 : Tendsto (fun u : ℂ => u - (z - w)) (𝓝 z) (𝓝 (z - (z - w))) :=
      (continuous_id.sub continuous_const).tendsto z
    rw [sub_sub_cancel] at h1
    exact h1.eventually (hW.mem_nhds hw)
  refine ⟨fun u => φ (u - (z - w)), ?_, ?_⟩
  · filter_upwards [hev] with u hu
    have h := RCDiffAt.comp (ε := δ) (δ := false) (Φ₁ := φ) (Φ₂ := fun u => u - (z - w))
      (w := u) (hφ _ hu) (by rw [rcDiffAt_false]; fun_prop)
    rwa [Bool.xor_false] at h
  · filter_upwards [hev] with u hu
    have : mk L u = mk L (u - (z - w)) := mk_eq_mk.2 (by simpa using hl)
    rw [this, hG _ hu]

/-- Local version of `differentiableAt_of_holAlong`: `φ` need only be continuous near `z₀`. -/
theorem differentiableAt_of_holAlong' {U : Set (Torus L)} {G : Torus L → Torus L}
    (hG : HolAlong (mk L) U G) {z₀ : ℂ} (hz₀ : mk L z₀ ∈ U) {φ : ℂ → ℂ}
    (hφ : ∀ᶠ z in 𝓝 z₀, ContinuousAt φ z)
    (hGφ : ∀ᶠ z in 𝓝 z₀, G (mk L z) = mk L (φ z)) : DifferentiableAt ℂ φ z₀ := by
  obtain ⟨Φ, hΦ, hΦe⟩ := hG z₀ hz₀
  have hall : ∀ᶠ z in 𝓝 z₀,
      (DifferentiableAt ℂ Φ z ∧ ContinuousAt φ z) ∧ Φ z - φ z ∈ L.lattice := by
    filter_upwards [hΦ, hΦe, hGφ, hφ] with z h1 h2 h3 h4
    exact ⟨⟨h1, h4⟩, mk_eq_mk.1 (h2.trans h3)⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hall
  let Z := Metric.ball z₀ ρ
  haveI : PreconnectedSpace Z :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball z₀ ρ).isPreconnected
  have hcont : Continuous fun z : Z => Φ z - φ z := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    exact (((hball z.2).1.1.continuousAt).sub (hball z.2).1.2).comp
      continuous_subtype_val.continuousAt
  have hconst : ∀ z ∈ Z, φ z = Φ z - (Φ z₀ - φ z₀) := by
    intro z hz
    have := eq_of_mem_lattice hcont (fun z => (hball z.2).2) ⟨z, hz⟩ ⟨z₀, Metric.mem_ball_self hρ⟩
    simp only at this
    linear_combination -this
  have hev : φ =ᶠ[𝓝 z₀] fun z => Φ z - (Φ z₀ - φ z₀) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hρ) hconst
  exact (((hball (Metric.mem_ball_self hρ)).1.1.sub_const _)).congr_of_eventuallyEq hev

/-! ### Charts are morphisms -/

section Chart

variable {S : Set ℂ} (hS : IsOpen S)

include hS in
/-- `W ⊆ S` open gives an open subset of `ℂ`. -/
theorem isOpen_inC (W : Opens S) : IsOpen (Subtype.val '' (W : Set S)) :=
  hS.isOpenMap_subtype_val _ W.2

include hS in
/-- **Comparison of holomorphy in a chart with holomorphy along `mk`**: if `e : W ≃ₜ V`, `W ⊆ S`,
is given by `mk`, then `k : V ≃ₜ V` is holomorphic along `mk` iff `e⁻¹ k e` is holomorphic in the
coordinate of `S`. -/
theorem holIn_conj_iff {W : Opens S} {V : Opens (Torus L)} (e : W ≃ₜ V)
    (he : ∀ x : W, (e x : Torus L) = mk L ((x : S) : ℂ)) (k : V ≃ₜ V) :
    HolIn (Subtype.val : S → ℂ) W (conj e.symm k) ↔ HolAlong (mk L) V (extendU k) := by
  set Wc : Set ℂ := Subtype.val '' (W : Set S) with hWc
  have hWo : IsOpen Wc := isOpen_inC hS W
  -- `τ : W ≃ₜ Wc`
  let τ : W ≃ₜ Wc := ((IsEmbedding.subtypeVal).comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by ext z; simp [hWc]))
  have hτ : ∀ x : W, (τ x : ℂ) = ((x : S) : ℂ) := fun _ => rfl
  have hτs : ∀ z : Wc, (((τ.symm z : W) : S) : ℂ) = z := by
    intro z
    have := congrArg Subtype.val (τ.apply_symm_apply z)
    rwa [hτ] at this
  have hconj : ∀ x : W, conj e.symm k x = e.symm (k (e x)) := fun _ => rfl
  have hmkV : ∀ x : W, mk L ((x : S) : ℂ) ∈ V := fun x => by rw [← he]; exact (e x).2
  constructor
  · rintro ⟨F, hF, hFk⟩
    have hF' : ∀ w ∈ Wc, RCDiffAt false F w := fun w hw =>
      rcDiffAt_false.2 (hF.differentiableAt (hWo.mem_nhds hw))
    refine rcAlong_of_lift' hWo ?_ hF' ?_
    · intro v hv
      obtain ⟨x, hx⟩ := e.surjective ⟨v, hv⟩
      refine ⟨((x : S) : ℂ), ⟨x, x.2, rfl⟩, ?_⟩
      rw [← he, hx]
    · rintro _ ⟨s, hs, rfl⟩
      let x : W := ⟨s, hs⟩
      rw [extendU_of_mem _ (hmkV x)]
      have h1 : (⟨mk L s, hmkV x⟩ : V) = e x := Subtype.ext (he x).symm
      rw [h1]
      have h2 : k (e x) = e (conj e.symm k x) := by rw [hconj, Homeomorph.apply_symm_apply]
      rw [h2, he, hFk]
  · intro hk
    classical
    -- the coordinate expression of `e⁻¹ k e`
    let F : ℂ → ℂ := fun z => if h : z ∈ Wc then
      (((conj e.symm k (τ.symm ⟨z, h⟩) : W) : S) : ℂ) else 0
    have hFW : ∀ x : W, F ((x : S) : ℂ) = (((conj e.symm k x : W) : S) : ℂ) := by
      intro x
      have hx : ((x : S) : ℂ) ∈ Wc := ⟨x, x.2, rfl⟩
      simp only [F, dif_pos hx]
      have : τ.symm ⟨((x : S) : ℂ), hx⟩ = x := by
        rw [Homeomorph.symm_apply_eq]; exact Subtype.ext rfl
      rw [this]
    have hFc : ContinuousOn F Wc := by
      rw [continuousOn_iff_continuous_restrict]
      have : Wc.restrict F = fun z : Wc => (((conj e.symm k (τ.symm z) : W) : S) : ℂ) := by
        funext z
        simp only [restrict_apply, F, dif_pos z.2]
      rw [this]
      fun_prop
    refine ⟨F, fun z hz => ?_, fun x => (hFW x).symm⟩
    obtain ⟨s, hs, rfl⟩ := hz
    let x : W := ⟨s, hs⟩
    refine (differentiableAt_of_holAlong' hk (hmkV x) ?_ ?_).differentiableWithinAt
    · filter_upwards [hWo.mem_nhds ⟨s, hs, rfl⟩] with z hz
      exact hFc.continuousAt (hWo.mem_nhds hz)
    · filter_upwards [hWo.mem_nhds ⟨s, hs, rfl⟩] with z hz
      obtain ⟨s', hs', rfl⟩ := hz
      let x' : W := ⟨s', hs'⟩
      rw [extendU_of_mem _ (hmkV x'), hFW x']
      have h1 : (⟨mk L s', hmkV x'⟩ : V) = e x' := Subtype.ext (he x').symm
      rw [h1, ← he, hconj, Homeomorph.apply_symm_apply]

include hS in
/-- **The charts of `T_Λ` are morphisms**: `mk : S → T_Λ` is a morphism of Aut-holomorphic spaces
from an open `S ⊆ ℂ` (with `A(W) = Aut^hol(W)`) to `T_Λ`. -/
theorem isMorphism_mk :
    IsMorphism (ofEmbedding (Subtype.val : S → ℂ)) (torusStr L) (fun c : S => mk L c) := by
  refine ⟨isCoveringMap_mk.isLocalHomeomorph.comp hS.isOpenEmbedding_subtypeVal.isLocalHomeomorph,
    ?_⟩
  intro W _ V _ e he
  ext g
  rw [mem_map_conj]
  change g ∈ (ofCover continuous_mk).aut V ↔ _
  have : (conj e.symm g).symm = conj e.symm g.symm := by ext; rfl
  rw [mem_ofCover_aut, mem_ofEmbedding_aut, this, holIn_conj_iff hS e he, holIn_conj_iff hS e he]

end Chart

/-! ### Corollary 2.3 (i) on the torus -/

theorem injOn_mk_ball {r R : ℝ} (hr : ∀ l ∈ L.lattice, l ≠ 0 → r ≤ ‖l‖) (hR : 2 * R ≤ r)
    (z : ℂ) : InjOn (mk L) (ball z R) := by
  intro c hc c' hc' h
  have hl : c - c' ∈ L.lattice := mk_eq_mk.1 h
  by_contra hne
  have h1 := hr _ hl (sub_ne_zero.2 hne)
  rw [mem_ball, dist_eq_norm] at hc hc'
  have h2 : ‖c - c'‖ ≤ ‖c - z‖ + ‖c' - z‖ := by
    have := norm_sub_le (c - z) (c' - z)
    simpa using this
  linarith

/-- **[AbsTopIII] Corollary 2.3 (i) for open subsets of the complex torus**: a morphism of
Aut-holomorphic spaces `φ : U → T_Λ` is, near every point, given by a holomorphic or
antiholomorphic map `ℂ → ℂ` through `mk`. -/
theorem exists_rcLift_of_isMorphism {U : Opens (Torus L)} {φ : U → Torus L}
    (hφ : IsMorphism ((torusStr L).restrict U) (torusStr L) φ) {z : ℂ} (hz : mk L z ∈ U) :
    ∃ (δ : Bool) (Φ : ℂ → ℂ) (r : ℝ), 0 < r ∧ (∀ w ∈ ball z r, RCDiffAt δ Φ w) ∧
      ∀ w ∈ ball z r, ∃ h : mk L w ∈ U, φ ⟨mk L w, h⟩ = mk L (Φ w) := by
  obtain ⟨ρ, hρ0, hρ⟩ := exists_sep L
  set R := ρ / 2
  have hR0 : 0 < R := by positivity
  have hR : 2 * R ≤ ρ := by simp only [R]; linarith
  obtain ⟨z', hz'⟩ := mk_surjective (L := L) (φ ⟨mk L z, hz⟩)
  -- the target chart
  set S' : Set ℂ := ball z' R
  have hS'o : IsOpen S' := isOpen_ball
  let O' : Opens (Torus L) := ⟨mk L '' S', isOpenMap_mk _ hS'o⟩
  have hinj' : Function.Injective (fun c : S' => mk L c) := fun c c' h =>
    Subtype.ext (injOn_mk_ball hρ hR z' c.2 c'.2 h)
  have hmor' := isMorphism_mk (L := L) hS'o
  let h' : S' ≃ₜ O' := (hmor'.1.isOpenEmbedding_of_injective hinj').isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by ext y; simp [O']))
  have hh' : ∀ c, (h' c : Torus L) = mk L c := fun _ => rfl
  have hiso := isIso_of_isMorphism hmor' h' hh'
  -- the source set
  have hUo : IsOpen (mk L ⁻¹' (U : Set (Torus L))) := U.2.preimage continuous_mk
  let f₀ : (mk L ⁻¹' (U : Set (Torus L))) → Torus L := fun c => φ ⟨mk L c, c.2⟩
  have hf₀ : Continuous f₀ := hφ.1.continuous.comp
    ((continuous_mk.comp continuous_subtype_val).subtype_mk _)
  set S : Set ℂ := ball z R ∩ Subtype.val '' (f₀ ⁻¹' (O' : Set (Torus L)))
  have hSo : IsOpen S :=
    isOpen_ball.inter (hUo.isOpenMap_subtype_val _ (O'.2.preimage hf₀))
  have hSU : ∀ c : S, mk L c ∈ U := by
    rintro ⟨c, -, ⟨c', -, rfl⟩⟩
    exact c'.2
  have hSO : ∀ c : S, φ ⟨mk L c, hSU c⟩ ∈ O' := by
    rintro ⟨c, -, ⟨c', hc', rfl⟩⟩
    exact hc'
  have hzS : z ∈ S := ⟨mem_ball_self hR0, ⟨z, hz⟩, by
    change φ ⟨mk L z, hz⟩ ∈ mk L '' S'
    exact ⟨z', mem_ball_self hR0, hz'⟩, rfl⟩
  -- the morphism `S → S'`
  have hj := (isMorphism_mk (L := L) hSo).codRestrict U hSU
  have hf₂ := (hφ.comp hj).codRestrict O' hSO
  have hG := (IsIso.symm hiso).comp hf₂
  obtain ⟨δ, Φ, r, hr0, hrS, hΦ, hΦe⟩ := rcDiff_of_isMorphism hSo hS'o hG ⟨z, hzS⟩
  refine ⟨δ, Φ, r, hr0, hΦ, fun w hw => ⟨hSU ⟨w, hrS hw⟩, ?_⟩⟩
  have := hΦe ⟨w, hrS hw⟩ hw
  simp only [Function.comp_apply] at this
  rw [← this, ← hh', Homeomorph.apply_symm_apply]

end Ell

end AutHol

end Iut
