/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Disc.RiemannMap

/-!
# Morphisms of Aut-holomorphic spaces are RC-holomorphic ([AbsTopIII] Corollary 2.3 (i))

**Theorem** (`rcDiff_of_isMorphism`). Let `U, V ⊆ ℂ` be open, with their Aut-holomorphic
structures `ofEmbedding (↑)` (`A(W) = Aut^hol(W)`). Every morphism of Aut-holomorphic spaces
`φ : U → V` ([AbsTopIII] Definition 2.1 (ii)) is, near every point, holomorphic or
antiholomorphic: **[AbsTopIII] Corollary 2.3 (i)** ("every morphism arises from a unique étale
RC-holomorphic morphism"; uniqueness is clear).

Proof, as in loc. cit. ("by applying Proposition 2.2 (i) to sufficiently small open discs"): for
a small disc `D` around `x` on which `φ` is injective, `φ(D)` is open, bounded and simply
connected, hence biholomorphic to the unit disc (`exists_isBihol`, Riemann mapping); the morphism
condition for `D ≅ φ(D)` says that `φ|_D` is an isomorphism of Aut-holomorphic discs, so it is
RC-holomorphic by Proposition 2.2 (i) (`rc_of_normalizes_bihol`).

`mem_aut_iff`: the bridge between `ofEmbedding (↑)` on an open `W ⊆ U` and `holAutOn W`.
-/

namespace Iut

namespace AutHol

open Complex Metric Set Filter Topology TopologicalSpace Disc

open scoped ComplexConjugate

variable {U V : Set ℂ}

/-- The open subset `W ⊆ U` as a subset of `ℂ`. -/
def inC (W : Set U) : Set ℂ := Subtype.val '' W

/-- The canonical homeomorphism `W ≃ₜ W ⊆ ℂ`. -/
noncomputable def toC (W : Set U) : W ≃ₜ inC W := IsEmbedding.subtypeVal.homeomorphImage W

@[simp] theorem coe_toC (W : Set U) (z : W) : (toC W z : ℂ) = ((z : U) : ℂ) := rfl

theorem coe_toC_symm (W : Set U) (z : inC W) : (((toC W).symm z : U) : ℂ) = z := by
  have := congrArg Subtype.val ((toC W).apply_symm_apply z)
  rw [coe_toC] at this
  exact this

theorem holIn_iff (W : Set U) (g : W → W) :
    HolIn (Subtype.val : U → ℂ) W g ↔ HolOn (inC W) (fun z => toC W (g ((toC W).symm z))) := by
  constructor
  · rintro ⟨F, hF, hFg⟩
    refine ⟨F, hF, fun z => ?_⟩
    rw [coe_toC, hFg, coe_toC_symm]
  · rintro ⟨F, hF, hFg⟩
    refine ⟨F, hF, fun x => ?_⟩
    have := hFg (toC W x)
    simpa using this

/-- **`A(W)` for the Aut-holomorphic structure of an open subset of `ℂ` is `Aut^hol(W)`.** -/
theorem mem_aut_iff (W : Opens U) (g : W ≃ₜ W) :
    g ∈ (ofEmbedding (Subtype.val : U → ℂ)).aut W ↔ cjS (toC (W : Set U)) g ∈ holAutOn (inC W) := by
  rw [mem_ofEmbedding_aut, holIn_iff, holIn_iff]
  rfl

/-- **[AbsTopIII] Corollary 2.3 (i) for open subsets of `ℂ`**: a morphism of Aut-holomorphic
spaces `φ : U → V` is holomorphic or antiholomorphic on a disc around every point. -/
theorem rcDiff_of_isMorphism (hU : IsOpen U) (hV : IsOpen V) {φ : U → V}
    (hφ : IsMorphism (ofEmbedding (Subtype.val : U → ℂ)) (ofEmbedding (Subtype.val : V → ℂ)) φ)
    (x : U) : ∃ (δ : Bool) (Φ : ℂ → ℂ) (r : ℝ), 0 < r ∧ ball (x : ℂ) r ⊆ U ∧
      (∀ w ∈ ball (x : ℂ) r, RCDiffAt δ Φ w) ∧
      ∀ y : U, (y : ℂ) ∈ ball (x : ℂ) r → (φ y : ℂ) = Φ y := by
  obtain ⟨e, hxe, rfl⟩ := hφ.1 x
  -- a small closed disc inside the source of `e`
  have hS : IsOpen (Subtype.val '' e.source : Set ℂ) := hU.isOpenMap_subtype_val _ e.open_source
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hS x ⟨x, hxe, rfl⟩
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hcl : closedBall (x : ℂ) r ⊆ Subtype.val '' e.source :=
    (closedBall_subset_ball (by linarith)).trans hεS
  have hballU : ball (x : ℂ) r ⊆ U := fun w hw => by
    obtain ⟨y, -, rfl⟩ := hcl (ball_subset_closedBall hw); exact y.2
  -- the disc `D` and its image
  let D : Opens U := ⟨Subtype.val ⁻¹' ball (x : ℂ) r, isOpen_ball.preimage continuous_subtype_val⟩
  have hDsrc : (D : Set U) ⊆ e.source := fun y hy => by
    obtain ⟨y', hy', hyy'⟩ := hcl (ball_subset_closedBall hy)
    rwa [← Subtype.ext hyy']
  let V' : Opens V := ⟨e '' D, e.isOpen_image_of_subset_source D.2 hDsrc⟩
  let e' : D ≃ₜ V' := e.homeomorphOfImageSubsetSource hDsrc rfl
  have he' : ∀ y : D, (e' y : V) = e y := fun _ => rfl
  have hinD : inC (D : Set U) = ball (x : ℂ) r := by
    ext w
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hw; exact ⟨⟨w, hballU hw⟩, hw, rfl⟩
  have hDconn : IsConnected (D : Set U) := by
    have : IsConnected (inC (D : Set U)) := by
      rw [hinD]; exact (convex_ball _ _).isConnected (nonempty_ball.2 hr0)
    rw [isConnected_iff_connectedSpace] at this ⊢
    exact (toC (D : Set U)).symm.surjective.connectedSpace (toC (D : Set U)).symm.continuous
  have hmor := hφ.2 D hDconn V' (isConnected_of_homeomorph e' hDconn) e' he'
  -- the isomorphism `ball x r ≃ₜ φ(D) ⊆ ℂ`
  set Ω₁ := inC (D : Set U)
  set Ω₂ := inC (V' : Set V)
  set e₀ : Ω₁ ≃ₜ Ω₂ := ((toC (D : Set U)).symm.trans e').trans (toC (V' : Set V))
  have he₀ : ∀ g : Ω₁ ≃ₜ Ω₁, g ∈ holAutOn Ω₁ ↔ cjS e₀ g ∈ holAutOn Ω₂ := by
    intro g
    have h1 : cjS (toC (D : Set U)) (cjS (toC (D : Set U)).symm g) = g := by ext; simp
    have h2 : cjS e₀ g =
        cjS (toC (V' : Set V)) (AutHol.conj e' (cjS (toC (D : Set U)).symm g)) := by
      ext z; rfl
    have h3 : ∀ k : D ≃ₜ D, AutHol.conj e'.symm (AutHol.conj e' k) = k := by
      intro k; ext; simp
    rw [h2, ← mem_aut_iff, hmor, mem_map_conj, h3, mem_aut_iff, h1]
  -- `Ω₁` is a disc
  have hΩ₁ : Ω₁ = ball (x : ℂ) r := hinD
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have h₁ : IsBihol Dk Ω₁ (fun z => (x : ℂ) + r * z) (fun w => (w - x) / r) := by
    rw [hΩ₁]
    refine ⟨fun z hz => ?_, fun w hw => ?_, fun z _ => by field_simp; ring,
      fun w _ => by field_simp; ring, by fun_prop, by fun_prop⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr0]
      have := mem_Dk.1 hz
      nlinarith [norm_nonneg z]
    · rw [mem_ball, dist_eq_norm] at hw
      rw [mem_Dk, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]
      exact hw
  -- `Ω₂` is a bounded simply connected domain
  have hΩ₂o : IsOpen Ω₂ := hV.isOpenMap_subtype_val _ V'.2
  have hK : IsCompact ((Subtype.val : U → ℂ) ⁻¹' closedBall (x : ℂ) r) := by
    rw [IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact isCompact_closedBall _ _
    · intro w hw
      obtain ⟨y, -, rfl⟩ := hcl hw
      exact ⟨y, rfl⟩
  have hΩ₂b : Bornology.IsBounded Ω₂ := by
    refine ((hK.image hφ.1.continuous).image continuous_subtype_val).isBounded.subset ?_
    exact image_mono (image_mono fun y hy => ball_subset_closedBall hy)
  have hΩ₂n : Ω₂.Nonempty := ⟨_, ⟨e x, ⟨x, (by simp [D, hr0] : x ∈ (D : Set U)), rfl⟩, rfl⟩⟩
  haveI : SimplyConnectedSpace (ball (x : ℂ) r) :=
    haveI := (convex_ball (x : ℂ) r).contractibleSpace (nonempty_ball.2 hr0)
    SimplyConnectedSpace.ofContractible _
  haveI : SimplyConnectedSpace Ω₁ :=
    (Homeomorph.setCongr hΩ₁).toHomotopyEquiv.simplyConnectedSpace
  haveI : SimplyConnectedSpace Ω₂ := e₀.symm.toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨F₂, G₂, h₂⟩ := exists_isBihol hΩ₂o hΩ₂b hΩ₂n
  have hΩ₁o : IsOpen Ω₁ := by rw [hΩ₁]; exact isOpen_ball
  obtain ⟨δ, Φ, hΦ, heΦ⟩ := rc_of_normalizes_bihol hΩ₁o h₁ h₂ e₀ he₀
  refine ⟨δ, Φ, r, hr0, hballU, fun w hw => hΦ w (hΩ₁ ▸ hw), fun y hy => ?_⟩
  have hyD : y ∈ (D : Set U) := hy
  have hz : (y : ℂ) ∈ Ω₁ := ⟨y, hyD, rfl⟩
  have := heΦ ⟨y, hz⟩
  have e1 : (toC (D : Set U)).symm ⟨y, hz⟩ = ⟨y, hyD⟩ := by
    apply (toC (D : Set U)).injective
    apply Subtype.ext
    rw [Homeomorph.apply_symm_apply, coe_toC]
  simp only [e₀, Homeomorph.trans_apply, e1] at this
  exact this

end AutHol

end Iut
