/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.OfCover
import Iut.AutHolomorphic.Elliptic.Lie
import Iut.AutHolomorphic.Elliptic.RLinear

/-!
# Linear holomorphic automorphisms of the tangent space ([AbsTopIII] Corollary 2.7 (d), (e))

Let `Y` be a commutative topological group (for Corollary 2.7: the one-point compactification of
`E^top` with the group law of Corollary 2.7 (c)), `A` an Aut-holomorphic structure on `Y` and
`p ∈ Y`. Model-implicitly, from `(Y, +, A, p)` alone:

* `IsLinHol A p M`: an `ℝ`-linear endomorphism `M` of the tangent space `Lie Y` (one-parameter
  subgroups) is **holomorphic at `p`**: on all small connected open `W ⊆ Lie Y`, the map
  `exp_p(W) → exp_p(M W)` induced by `M` is a local morphism of Aut-holomorphic spaces
  ([AbsTopIII] Definition 2.1 (ii));
* `holGroup A p`: the `ℝ`-linear automorphisms that are holomorphic at `p`;
* `apSet A p`: their squares (the orientation-preserving ones), **the group `A_p`** of
  Corollary 2.7 (e); `fieldSet A p = A_p ∪ {0}`.

This replaces the orthogonal frames of Corollary 2.7 (d) (built there from one-parameter subgroups
of `A_V(V) ≅ SL₂(ℝ)/{±1}`, via the Riemann mapping theorem) by the morphism condition of
Definition 2.1 (ii) itself; see `Plans/MR10Plan.md` §4.

For the complex torus `T_Λ` with its Aut-holomorphic structure `torusStr L` (holomorphy along
`ℂ → T_Λ`):

* `isLinHol_iff`: `M` is holomorphic at `p` iff, in the coordinate `Lie T_Λ ≅ ℂ`, it is
  `c ↦ a c` or `c ↦ a c̄` with `a ≠ 0` (so `holGroup = ℂ^× ⋊ Gal(ℂ/ℝ)`, for every `p`);
* `mem_apSet_iff`: `A_p = {c ↦ b c | b ≠ 0} ≅ ℂ^×` ([AbsTopIII] Proposition 2.6 (a),
  Corollary 2.7 (e)), the same subset of `End_ℝ (Lie T_Λ)` for every `p` (the isomorphisms
  `A_p ≅ A_{p'}` of Corollary 2.7 (e) are identities).
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace ComplexConjugate Complex

section Generic

variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]

/-- **`M` is holomorphic at `p`**: there is a neighbourhood `N` of `0` in `Lie Y` on which `exp_p`
and `exp_p ∘ M` are injective such that, for every connected open `W ⊆ N`, the homeomorphism
`exp_p(W) ≅ exp_p(M W)` induced by `M` carries `A(exp_p W)` onto `A(exp_p (M W))`
([AbsTopIII] Definition 2.1 (ii)). -/
def IsLinHol (A : AutHolStr Y) (p : Y) (M : Lie Y →ₗ[ℝ] Lie Y) : Prop :=
  ∃ N ∈ 𝓝 (0 : Lie Y), InjOn (expAt p) N ∧ InjOn (expAt p) (M '' N) ∧
    ∀ (W : Set (Lie Y)) (U V : Opens Y) (e : U ≃ₜ V), W ⊆ N → IsOpen W → IsConnected W →
      (U : Set Y) = expAt p '' W → (V : Set Y) = expAt p '' (M '' W) →
      (∀ f ∈ W, ∀ h : expAt p f ∈ U, (e ⟨expAt p f, h⟩ : Y) = expAt p (M f)) →
      A.aut V = (A.aut U).map (AutHol.conj e).toMonoidHom

/-- The `ℝ`-linear automorphisms of `Lie Y` that are holomorphic at `p`. -/
def holGroup (A : AutHolStr Y) (p : Y) : Set (Lie Y ≃ₗ[ℝ] Lie Y) :=
  {M | IsLinHol A p M.toLinearMap}

/-- **The group `A_p`** ([AbsTopIII] Corollary 2.7 (e)): the squares of elements of
`holGroup A p` (orientation: squares are orientation preserving). -/
def apSet (A : AutHolStr Y) (p : Y) : Set (Lie Y →ₗ[ℝ] Lie Y) :=
  {M | ∃ N ∈ holGroup A p, M = (N.trans N).toLinearMap}

/-- **`A_p ∪ {0}`**. -/
def fieldSet (A : AutHolStr Y) (p : Y) : Set (Lie Y →ₗ[ℝ] Lie Y) := apSet A p ∪ {0}

end Generic

/-! ### The complex torus -/

variable {L : PeriodPair}

open Torus

/-- **The Aut-holomorphic structure of the complex torus** `T_Λ`: holomorphy along `ℂ → T_Λ`. -/
noncomputable def torusStr (L : PeriodPair) : AutHolStr (Torus L) :=
  ofCover (continuous_mk (L := L))

theorem expAt_line (q c : ℂ) : expAt (mk L q) (line c) = mk L (q + c) := by
  simp [expAt, line_apply, mk_add]

theorem rc_inv_left {a : ℂ} (ha : a ≠ 0) (ε : Bool) (c : ℂ) :
    rc (if ε then (conj a)⁻¹ else a⁻¹) ε (rc a ε c) = c := by
  cases ε
  · simp [rc, ← mul_assoc, inv_mul_cancel₀ ha]
  · simp [rc, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 ha)]

theorem rc_inv_right {a : ℂ} (ha : a ≠ 0) (ε : Bool) (c : ℂ) :
    rc a ε (rc (if ε then (conj a)⁻¹ else a⁻¹) ε c) = c := by
  cases ε
  · simp [rc, ← mul_assoc, mul_inv_cancel₀ ha]
  · simp [rc, ← mul_assoc, mul_inv_cancel₀ ha]

theorem continuous_rc (a : ℂ) (ε : Bool) : Continuous (rc a ε) := by
  cases ε
  · exact continuous_const.mul continuous_id
  · exact continuous_const.mul Complex.continuous_conj

theorem norm_rc (a c : ℂ) (ε : Bool) : ‖rc a ε c‖ = ‖a‖ * ‖c‖ := by
  cases ε <;> simp [rc]

theorem rcDiffAt_affine (q a : ℂ) (ε : Bool) (w : ℂ) :
    RCDiffAt ε (fun z => q + rc a ε (z - q)) w := by
  cases ε
  · rw [rcDiffAt_false]
    change DifferentiableAt ℂ (fun z => q + a * (z - q)) w
    fun_prop
  · rw [rcDiffAt_true]
    have : ((fun z => q + rc a true (z - q)) ∘ conj) = fun u => q + a * (u - conj q) := by
      funext u
      simp [rc, map_sub]
    rw [this]
    fun_prop

/-- A map of `T_Λ` given on `mk(W)` by an (anti)holomorphic map of `ℂ` is (anti)holomorphic along
`mk` there. -/
theorem rcAlong_of_lift {W : Set ℂ} (hW : IsOpen W) {S : Set (Torus L)} (hS : S ⊆ mk L '' W)
    {φ : ℂ → ℂ} {δ : Bool} (hφ : ∀ w, RCDiffAt δ φ w) {G : Torus L → Torus L}
    (hG : ∀ z ∈ W, G (mk L z) = mk L (φ z)) : RCAlong (mk L) S G δ := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hS hz
  have hl : z - w ∈ L.lattice := mk_eq_mk.1 hwz.symm
  refine ⟨fun u => φ (u - (z - w)), Eventually.of_forall fun u => ?_, ?_⟩
  · have h := RCDiffAt.comp (ε := δ) (δ := false) (Φ₁ := φ) (Φ₂ := fun u => u - (z - w))
      (w := u) (hφ _) (by rw [rcDiffAt_false]; fun_prop)
    rwa [Bool.xor_false] at h
  · have hev : ∀ᶠ u in 𝓝 z, u - (z - w) ∈ W := by
      have h1 : Tendsto (fun u : ℂ => u - (z - w)) (𝓝 z) (𝓝 (z - (z - w))) :=
        (continuous_id.sub continuous_const).tendsto z
      rw [sub_sub_cancel] at h1
      exact h1.eventually (hW.mem_nhds hw)
    filter_upwards [hev] with u hu
    have : mk L u = mk L (u - (z - w)) := mk_eq_mk.2 (by simpa using hl)
    rw [this, hG _ hu]

/-- Conversely, a map of `T_Λ` that is holomorphic along `mk` at `mk z₀` and is given near `z₀` by
a continuous `φ` is complex differentiable at `z₀`. -/
theorem differentiableAt_of_holAlong {U : Set (Torus L)} {G : Torus L → Torus L}
    (hG : HolAlong (mk L) U G) {z₀ : ℂ} (hz₀ : mk L z₀ ∈ U) {φ : ℂ → ℂ} (hφ : Continuous φ)
    (hGφ : ∀ᶠ z in 𝓝 z₀, G (mk L z) = mk L (φ z)) : DifferentiableAt ℂ φ z₀ := by
  obtain ⟨Φ, hΦ, hΦe⟩ := hG z₀ hz₀
  have hall : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ Φ z ∧ Φ z - φ z ∈ L.lattice := by
    filter_upwards [hΦ, hΦe, hGφ] with z h1 h2 h3
    exact ⟨h1, mk_eq_mk.1 (h2.trans h3)⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 hall
  let Z := Metric.ball z₀ ρ
  haveI : PreconnectedSpace Z :=
    isPreconnected_iff_preconnectedSpace.1 (convex_ball z₀ ρ).isPreconnected
  have hcont : Continuous fun z : Z => Φ z - φ z := by
    refine Continuous.sub ?_ (hφ.comp continuous_subtype_val)
    exact continuous_iff_continuousAt.2 fun z =>
      ((hball z.2).1.continuousAt).comp continuous_subtype_val.continuousAt
  have hconst : ∀ z ∈ Z, φ z = Φ z - (Φ z₀ - φ z₀) := by
    intro z hz
    have := eq_of_mem_lattice hcont (fun z => (hball z.2).2) ⟨z, hz⟩ ⟨z₀, Metric.mem_ball_self hρ⟩
    simp only at this
    linear_combination -this
  have hev : φ =ᶠ[𝓝 z₀] fun z => Φ z - (Φ z₀ - φ z₀) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hρ) hconst
  exact (((hball (Metric.mem_ball_self hρ)).1.sub_const _)).congr_of_eventuallyEq hev

/-! ### Charts -/

/-- `ψ_q c = mk (q + c)`, i.e. `exp_{mk q} ∘ line`. -/
noncomputable def psi (L : PeriodPair) (q c : ℂ) : Torus L := mk L (q + c)

theorem expAt_line' (q c : ℂ) : expAt (mk L q) (line c) = psi L q c := expAt_line q c

theorem continuous_psi (q : ℂ) : Continuous (psi L q) :=
  continuous_mk.comp (continuous_const.add continuous_id)

theorem isOpenMap_psi (q : ℂ) : IsOpenMap (psi L q) :=
  isOpenMap_mk.comp (Homeomorph.addLeft q).isOpenMap

theorem psi_image (q : ℂ) (B : Set ℂ) : psi L q '' B = mk L '' ((fun z => z - q) ⁻¹' B) := by
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨q + c, by simpa using hc, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z - q, hz, by simp [psi]⟩

theorem mk_eq_psi (q z : ℂ) : mk L z = psi L q (z - q) := by simp [psi]

theorem injOn_psi {r R : ℝ} (hr : ∀ l ∈ L.lattice, l ≠ 0 → r ≤ ‖l‖) (hR : 2 * R ≤ r) (q : ℂ) :
    InjOn (psi L q) (Metric.ball 0 R) := by
  intro c hc c' hc' h
  have hl : c - c' ∈ L.lattice := by
    have := mk_eq_mk.1 h
    simpa using this
  by_contra hne
  have h1 := hr _ hl (sub_ne_zero.2 hne)
  rw [Metric.mem_ball, dist_zero_right] at hc hc'
  have h2 : ‖c - c'‖ ≤ ‖c‖ + ‖c'‖ := norm_sub_le _ _
  linarith

/-- **The chart** `B ≅ ψ_q(B)` for an open `B ⊆ ℂ` on which `ψ_q` is injective. -/
noncomputable def chart (q : ℂ) {B : Set ℂ} (hB : IsOpen B) (hinj : InjOn (psi L q) B) :
    B ≃ₜ (psi L q '' B : Set (Torus L)) :=
  (Equiv.Set.imageOfInjOn (psi L q) B hinj).toHomeomorphOfContinuousOpen
    (((continuous_psi q).comp continuous_subtype_val).subtype_mk _)
    (by
      intro O hO
      rw [isOpen_induced_iff]
      refine ⟨psi L q '' (Subtype.val '' O), isOpenMap_psi q _ (hB.isOpenMap_subtype_val _ hO), ?_⟩
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨_, ⟨c, hc, rfl⟩, hcx⟩
        exact ⟨c, hc, Subtype.ext hcx⟩
      · rintro ⟨c, hc, hcx⟩
        refine ⟨c, ⟨c, hc, rfl⟩, ?_⟩
        rw [← hcx]
        rfl)

@[simp]
theorem chart_apply (q : ℂ) {B : Set ℂ} (hB : IsOpen B) (hinj : InjOn (psi L q) B) (c : B) :
    (chart q hB hinj c : Torus L) = psi L q c := rfl

theorem chart_symm_apply (q : ℂ) {B : Set ℂ} (hB : IsOpen B) (hinj : InjOn (psi L q) B)
    {c : ℂ} (hc : c ∈ B) (h : psi L q c ∈ psi L q '' B) :
    (chart q hB hinj).symm ⟨psi L q c, h⟩ = ⟨c, hc⟩ := by
  rw [Homeomorph.symm_apply_eq]
  rfl

/-! ### Holomorphic linear maps of `Lie T_Λ` -/

/-- **Sufficiency**: complex linear and complex antilinear automorphisms are holomorphic. -/
theorem isLinHol_of_rc (q : ℂ) (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) {a : ℂ} (ha : a ≠ 0)
    (ε : Bool) (hM : ∀ c, M (line c) = line (rc a ε c)) :
    IsLinHol (torusStr L) (mk L q) M := by
  obtain ⟨r, hr0, hr⟩ := exists_sep L
  set ρ := r / (4 * (1 + ‖a‖)) with hρ
  have h1a : 0 < 1 + ‖a‖ := by positivity
  have hρ0 : 0 < ρ := by positivity
  have hρa : (1 + ‖a‖) * ρ = r / 4 := by
    rw [hρ]; field_simp
  have hinj4 : InjOn (expAt (mk L q)) (line '' Metric.ball 0 (r / 4)) := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ h
    rw [expAt_line', expAt_line'] at h
    rw [injOn_psi hr (by linarith) q hc hc' h]
  have hNsub : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 (r / 4) :=
    Metric.ball_subset_ball (by nlinarith [norm_nonneg a])
  have hMsub : M '' (line '' Metric.ball 0 ρ) ⊆ line '' Metric.ball 0 (r / 4) := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨rc a ε c, ?_, (hM c).symm⟩
    rw [Metric.mem_ball, dist_zero_right] at hc ⊢
    rw [norm_rc]
    have : ‖a‖ * ‖c‖ ≤ ‖a‖ * ρ := mul_le_mul_of_nonneg_left hc.le (norm_nonneg a)
    nlinarith
  refine ⟨line '' Metric.ball 0 ρ, ?_, hinj4.mono (image_mono hNsub), hinj4.mono hMsub, ?_⟩
  · refine (lieHomeo (L := L)).isOpenMap _ Metric.isOpen_ball |>.mem_nhds ⟨0, ?_, ?_⟩
    · simpa using hρ0
    · exact map_zero (lieEquiv (L := L))
  intro W U V e hWN hWo _ hU hV he
  set B := line (L := L) ⁻¹' W with hB
  have hWB : W = line '' B := by
    rw [hB, image_preimage_eq_of_subset]
    intro f _
    obtain ⟨c, rfl⟩ := exists_line f
    exact ⟨c, rfl⟩
  have hBo : IsOpen B := hWo.preimage continuous_line
  have hBρ : B ⊆ Metric.ball 0 ρ := by
    intro c hc
    obtain ⟨c', hc', hcc'⟩ := hWN hc
    rwa [line_injective hcc'] at hc'
  set a' : ℂ := if ε then (conj a)⁻¹ else a⁻¹
  have hU' : (U : Set (Torus L)) = psi L q '' B := by
    rw [hU, hWB, image_image]
    simp only [expAt_line']
  have hrcB : rc a ε '' B = rc a' ε ⁻¹' B :=
    congrFun (image_eq_preimage_of_inverse (rc_inv_left ha ε) (rc_inv_right ha ε)) B
  have hV' : (V : Set (Torus L)) = psi L q '' (rc a ε '' B) := by
    rw [hV, hWB, image_image, image_image, image_image]
    simp only [hM, expAt_line']
  -- the formula for `e`
  have hex : ∀ c ∈ B, ∀ h : psi L q c ∈ U,
      (e ⟨psi L q c, h⟩ : Torus L) = psi L q (rc a ε c) := by
    intro c hc h
    have hx : psi L q c = expAt (mk L q) (line c) := (expAt_line' q c).symm
    have h' : expAt (mk L q) (line c) ∈ U := hx ▸ h
    have := he (line c) hc h'
    have hsub : (⟨psi L q c, h⟩ : U) = ⟨expAt (mk L q) (line c), h'⟩ := Subtype.ext hx
    rw [hsub, this, hM, expAt_line']
  have hW1 : IsOpen ((fun z : ℂ => z - q) ⁻¹' B) :=
    hBo.preimage (continuous_id.sub continuous_const)
  apply ofCover_conj _ e (δ := ε)
  · refine rcAlong_of_lift hW1 ?_
      (rcDiffAt_affine q a ε) fun z hz => ?_
    · rw [hU', psi_image]
    · have hz' : mk L z ∈ U := by
        rw [SetLike.mem_coe.symm, hU', psi_image]; exact ⟨z, hz, rfl⟩
      rw [extendU_of_mem _ hz']
      have h2 : mk L z = psi L q (z - q) := mk_eq_psi q z
      have := hex (z - q) hz (h2 ▸ hz')
      have hsub : (⟨mk L z, hz'⟩ : U) = ⟨psi L q (z - q), h2 ▸ hz'⟩ := Subtype.ext h2
      rw [hsub, this]
      rfl
  · have hB2o : IsOpen ((fun z => z - q) ⁻¹' (rc a ε '' B)) := by
      rw [hrcB]
      exact (hBo.preimage (continuous_rc a' ε)).preimage (continuous_id.sub continuous_const)
    refine rcAlong_of_lift hB2o ?_ (rcDiffAt_affine q a' ε) fun z hz => ?_
    · rw [hV', psi_image]
    · obtain ⟨c, hc, hcz⟩ := hz
      have hcz' : z - q = rc a ε c := hcz.symm
      have hz' : mk L z ∈ V := by
        rw [SetLike.mem_coe.symm, hV']
        exact ⟨rc a ε c, ⟨c, hc, rfl⟩, by rw [← hcz', ← mk_eq_psi]⟩
      have hcU : psi L q c ∈ U := by rw [SetLike.mem_coe.symm, hU']; exact ⟨c, hc, rfl⟩
      rw [extendU_of_mem _ hz']
      have hsymm : e.symm ⟨mk L z, hz'⟩ = ⟨psi L q c, hcU⟩ := by
        rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [hex c hc hcU, ← hcz', ← mk_eq_psi]
      rw [hsymm]
      simp only [psi]
      rw [hcz', rc_inv_left ha ε]

/-- The coordinate expression `ℂ ≃ₗ[ℝ] ℂ` of an `ℝ`-linear automorphism of `Lie T_Λ`. -/
noncomputable def coordEquiv (M : Lie (Torus L) ≃ₗ[ℝ] Lie (Torus L)) : ℂ ≃ₗ[ℝ] ℂ :=
  lieEquiv.trans (M.trans lieEquiv.symm)

theorem apply_line (M : Lie (Torus L) ≃ₗ[ℝ] Lie (Torus L)) (c : ℂ) :
    M (line c) = line (coordEquiv M c) := by
  simp [coordEquiv, ← lieEquiv_apply]

/-- **Necessity**: an `ℝ`-linear automorphism of `Lie T_Λ` that is holomorphic at `p` is complex
linear or complex antilinear. The proof conjugates the rotation `c ↦ i c` of a small disc (an
element of `A`) by the map induced by `M`. -/
theorem rc_of_isLinHol (q : ℂ) (M : Lie (Torus L) ≃ₗ[ℝ] Lie (Torus L))
    (h : IsLinHol (torusStr L) (mk L q) M.toLinearMap) :
    ∃ a ε, a ≠ 0 ∧ ∀ c, M (line c) = line (rc a ε c) := by
  obtain ⟨N, hN, hinj, hinjM, hcond⟩ := h
  set Mc := coordEquiv M with hMcdef
  let McH : ℂ ≃ₜ ℂ := (LinearEquiv.toContinuousLinearEquiv Mc).toHomeomorph
  have hMcH : ∀ c, McH c = Mc c := fun _ => rfl
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, line '' Metric.ball (0 : ℂ) ρ ⊆ N := by
    have h0 : line (L := L) 0 = 0 := map_zero (lieEquiv (L := L))
    have : line (L := L) ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
      continuous_line.continuousAt.preimage_mem_nhds (by rwa [h0])
    obtain ⟨ρ, hρ, h⟩ := Metric.mem_nhds_iff.1 this
    exact ⟨ρ, hρ, by rintro _ ⟨c, hc, rfl⟩; exact h hc⟩
  set B := Metric.ball (0 : ℂ) ρ with hBdef
  have hBo : IsOpen B := Metric.isOpen_ball
  have h0B : (0 : ℂ) ∈ B := Metric.mem_ball_self hρ
  have hinjB : InjOn (psi L q) B := by
    intro c hc c' hc' hcc
    have := hinj (hball ⟨c, hc, rfl⟩) (hball ⟨c', hc', rfl⟩) (by rwa [expAt_line', expAt_line'])
    exact line_injective this
  set B' := McH '' B with hB'def
  have hB'o : IsOpen B' := McH.isOpenMap _ hBo
  have hinjB' : InjOn (psi L q) B' := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hcc
    have := hinjM ⟨line c, hball ⟨c, hc, rfl⟩, rfl⟩ ⟨line c', hball ⟨c', hc', rfl⟩, rfl⟩
      (by
        simp only [LinearEquiv.coe_coe, apply_line, expAt_line']
        exact hcc)
    simp only [LinearEquiv.coe_coe, apply_line] at this
    rw [hMcH, hMcH, line_injective this]
  let U : Opens (Torus L) := ⟨psi L q '' B, isOpenMap_psi q _ hBo⟩
  let V : Opens (Torus L) := ⟨psi L q '' B', isOpenMap_psi q _ hB'o⟩
  let e : U ≃ₜ V := (chart q hBo hinjB).symm.trans ((McH.image B).trans (chart q hB'o hinjB'))
  have hex : ∀ c (hc : c ∈ B) (h : psi L q c ∈ U),
      (e ⟨psi L q c, h⟩ : Torus L) = psi L q (Mc c) := by
    intro c hc h
    change (chart q hB'o hinjB' (McH.image B ((chart q hBo hinjB).symm ⟨psi L q c, h⟩)) :
      Torus L) = _
    rw [chart_symm_apply q hBo hinjB hc]
    rfl
  -- the rotation `c ↦ i c` of `U`
  let rotH : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ I I_ne_zero
  have hrot : rotH '' B = B := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [rotH, hBdef, Metric.mem_ball, dist_zero_right] using hw
    · intro hz
      refine ⟨-I * z, ?_, ?_⟩
      · simpa [hBdef, Metric.mem_ball, dist_zero_right] using hz
      · simp [rotH, ← mul_assoc]
  let g : U ≃ₜ U := (chart q hBo hinjB).symm.trans
    (((rotH.image B).trans (Homeomorph.setCongr hrot)).trans (chart q hBo hinjB))
  have hgx : ∀ c (hc : c ∈ B) (h : psi L q c ∈ U),
      (g ⟨psi L q c, h⟩ : Torus L) = psi L q (I * c) := by
    intro c hc h
    change (chart q hBo hinjB (Homeomorph.setCongr hrot (rotH.image B
      ((chart q hBo hinjB).symm ⟨psi L q c, h⟩))) : Torus L) = _
    rw [chart_symm_apply q hBo hinjB hc]
    rfl
  have hW' : IsOpen ((fun z => z - q) ⁻¹' B) := hBo.preimage (continuous_id.sub continuous_const)
  have hUW : (U : Set (Torus L)) ⊆ mk L '' ((fun z => z - q) ⁻¹' B) := by
    rw [← psi_image]; exact subset_rfl
  have hg : g ∈ (torusStr L).aut U := by
    refine ⟨rcAlong_of_lift hW' hUW (rcDiffAt_affine q I false) fun z hz => ?_,
      rcAlong_of_lift hW' hUW (rcDiffAt_affine q (-I) false) fun z hz => ?_⟩
    · have hz' : mk L z ∈ U := ⟨z - q, hz, by simp [psi]⟩
      rw [extendU_of_mem _ hz']
      have := hgx (z - q) hz (by rw [← mk_eq_psi]; exact hz')
      simp only [mk_eq_psi q z] at hz' ⊢
      rw [this]
      rfl
    · have hz' : mk L z ∈ U := ⟨z - q, hz, by simp [psi]⟩
      rw [extendU_of_mem _ hz']
      have hm : -I * (z - q) ∈ B := by
        simpa [hBdef, Metric.mem_ball, dist_zero_right] using hz
      have hmU : psi L q (-I * (z - q)) ∈ U := ⟨_, hm, rfl⟩
      have hsymm : g.symm ⟨mk L z, hz'⟩ = ⟨psi L q (-I * (z - q)), hmU⟩ := by
        rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [hgx _ hm hmU]
        simp [psi, ← mul_assoc]
      rw [hsymm]
      rfl
  -- apply the morphism condition to `W = line '' B`
  have hAV := hcond (line '' B) U V e hball ((lieHomeo (L := L)).isOpenMap _ hBo)
    ((Metric.isConnected_ball hρ).image _ continuous_line.continuousOn)
    (by
      change psi L q '' B = _
      rw [image_image]
      simp only [expAt_line'])
    (by
      change psi L q '' (McH '' B) = expAt (mk L q) '' (M.toLinearMap '' (line '' B))
      rw [image_image, image_image, image_image]
      refine image_congr fun c _ => ?_
      simp only [LinearEquiv.coe_coe, apply_line, expAt_line', hMcH]
      rfl)
    (by
      rintro _ ⟨c, hc, rfl⟩ hcU
      have hcU' : psi L q c ∈ U := by rwa [expAt_line'] at hcU
      simp only [LinearEquiv.coe_coe, apply_line, expAt_line']
      rw [← hex c hc hcU'])
  have hconj : AutHol.conj e g ∈ (torusStr L).aut V := by
    rw [hAV]
    exact ⟨g, hg, rfl⟩
  -- the conjugate is `u ↦ Mc (i Mc⁻¹ u)` in the coordinate; it is holomorphic at `0`
  let Jl : ℂ →ₗ[ℝ] ℂ := Mc.toLinearMap ∘ₗ LinearMap.mulLeft ℝ I ∘ₗ Mc.symm.toLinearMap
  have hJl : ∀ w, Jl w = Mc (I * Mc.symm w) := fun _ => rfl
  have hJc : Continuous Jl := LinearMap.continuous_of_finiteDimensional Jl
  have hq : mk L q ∈ (V : Set (Torus L)) := ⟨0, ⟨0, h0B, by simp [hMcH]⟩, by simp [psi]⟩
  have hdiff := differentiableAt_of_holAlong (mem_ofCover_aut.1 hconj).1 hq
    (φ := fun z => q + Jl (z - q))
    (continuous_const.add (hJc.comp (continuous_id.sub continuous_const)))
    (by
      have : ∀ᶠ z in 𝓝 q, z - q ∈ B' := by
        have h1 : Tendsto (fun z : ℂ => z - q) (𝓝 q) (𝓝 (q - q)) :=
          (continuous_id.sub continuous_const).tendsto q
        rw [sub_self] at h1
        exact h1.eventually (hB'o.mem_nhds ⟨0, h0B, by simp [hMcH]⟩)
      filter_upwards [this] with z hz
      obtain ⟨c, hc, hcz⟩ := hz
      have hzV : mk L z ∈ V := ⟨_, ⟨c, hc, rfl⟩, by rw [hcz, ← mk_eq_psi]⟩
      have hcU : psi L q c ∈ U := ⟨c, hc, rfl⟩
      have hIc : I * c ∈ B := by
        simpa [hBdef, Metric.mem_ball, dist_zero_right] using hc
      have hIcU : psi L q (I * c) ∈ U := ⟨_, hIc, rfl⟩
      rw [extendU_of_mem _ hzV]
      have hsymm : e.symm ⟨mk L z, hzV⟩ = ⟨psi L q c, hcU⟩ := by
        rw [Homeomorph.symm_apply_eq]
        apply Subtype.ext
        rw [hex c hc hcU, ← hMcH, hcz, ← mk_eq_psi]
      change (e (g (e.symm ⟨mk L z, hzV⟩)) : Torus L) = _
      rw [hsymm]
      have hg' : g ⟨psi L q c, hcU⟩ = ⟨psi L q (I * c), hIcU⟩ := Subtype.ext (hgx c hc hcU)
      rw [hg', hex _ hIc hIcU, hJl, ← hcz, hMcH, LinearEquiv.symm_apply_apply]
      rfl)
  have hJdiff : DifferentiableAt ℂ Jl 0 := by
    have hq : DifferentiableAt ℂ (fun z => q + Jl (z - q)) ((fun w : ℂ => w + q) 0) := by
      simpa using hdiff
    have h1 :=
      (hq.comp (0 : ℂ) (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => w + q) 0)).sub_const q
    have h2 : (fun w => q + Jl (w + q - q) - q) = (Jl : ℂ → ℂ) := by
      funext w
      simp
    have h1' : DifferentiableAt ℂ (fun w => q + Jl (w + q - q) - q) 0 := h1
    rw [h2] at h1'
    exact h1'
  have hmul := eq_mul_of_differentiableAt Jl hJdiff
  rcases eq_mul_or_eq_mul_conj Mc (c := Jl 1) (fun w => by rw [← hJl, hmul w]) with hlin | hanti
  · refine ⟨Mc 1, false, ?_, fun c => by rw [apply_line, hlin c]; rfl⟩
    intro h0
    have : Mc 1 = Mc 0 := by rw [h0, map_zero]
    exact one_ne_zero (Mc.injective this)
  · refine ⟨Mc 1, true, ?_, fun c => by rw [apply_line, hanti c]; rfl⟩
    intro h0
    have : Mc 1 = Mc 0 := by rw [h0, map_zero]
    exact one_ne_zero (Mc.injective this)

/-- **[AbsTopIII] Corollary 2.7 (d) for `T_Λ`**: an `ℝ`-linear automorphism of the tangent space is
holomorphic at `p` iff it is `c ↦ a c` or `c ↦ a c̄` with `a ≠ 0`. -/
theorem isLinHol_iff (q : ℂ) (M : Lie (Torus L) ≃ₗ[ℝ] Lie (Torus L)) :
    IsLinHol (torusStr L) (mk L q) M.toLinearMap ↔
      ∃ a ε, a ≠ 0 ∧ ∀ c, M (line c) = line (rc a ε c) :=
  ⟨rc_of_isLinHol q M, fun ⟨_, ε, ha, hM⟩ => isLinHol_of_rc q M.toLinearMap ha ε hM⟩

end Ell

end AutHol

end Iut
