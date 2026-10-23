/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Aut-holomorphic structures of uniformised Riemann surfaces; restriction to open subsets

[AbsTopIII] Definition 2.1 (i) attaches to a Riemann surface `X` the Aut-holomorphic structure
`U ↦ A_X(U) = Aut^hol(U)`. `ofEmbedding` (`Basic.lean`) covers open subsets of `ℂ`. Here:

* `RCDiffAt δ Φ w`: `Φ : ℂ → ℂ` is complex differentiable (`δ = false`) or anti-differentiable
  (`δ = true`, i.e. `Φ ∘ conj` is differentiable at `conj w`) at `w`; `RCDiffAt.comp`.
* `RCAlong π U G δ`: a self-map `G` of `X` is **holomorphic (`δ = false`) or antiholomorphic
  (`δ = true`) on `U` along `π : ℂ → X`**: near every `z` with `π z ∈ U` it lifts through `π` to a
  map that is (anti-)holomorphic near `z`. `RCAlong.comp`: composites (with `δ` adding up in
  `ℤ/2`).
* `ofCover hπ`: the Aut-holomorphic structure of a Riemann surface whose holomorphic structure is
  given by a continuous map `π : ℂ → X` (e.g. the uniformisation `ℂ → ℂ ⧸ Λ` of a complex torus):
  `g ∈ A(U)` iff `g` and `g⁻¹` are holomorphic along `π`.
* `ofCover_conj`: conjugation by a homeomorphism `e : U ≃ₜ V` which, together with its inverse, is
  holomorphic or antiholomorphic along `π`, carries `A(U)` onto `A(V)` (the easy half of
  [AbsTopIII] Corollary 2.3 (i): RC-holomorphic isomorphisms are isomorphisms of Aut-holomorphic
  spaces).
* `AutHolStr.restrict A W`: the Aut-holomorphic space determined by an open subset `W ⊆ X`
  ([AbsTopIII] Corollary 2.4 (b), Corollary 2.7 (b), (d)): `A_W(U) = A_X(U)` for `U ⊆ W`.
  `isMorphism_val`: the inclusion `W → X` is a morphism of Aut-holomorphic spaces (an "open
  immersion" of Corollary 2.7 (b)).
-/

namespace Iut

namespace AutHol

open Set Topology Filter TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-! ### Holomorphic and antiholomorphic maps -/

/-- Complex conjugation. -/
local notation "cc" => starRingEnd ℂ

/-- `Φ` is holomorphic (`δ = false`) or antiholomorphic (`δ = true`) at `w`. -/
def RCDiffAt (δ : Bool) (Φ : ℂ → ℂ) (w : ℂ) : Prop :=
  if δ then DifferentiableAt ℂ (Φ ∘ cc) (cc w) else DifferentiableAt ℂ Φ w

theorem rcDiffAt_false {Φ : ℂ → ℂ} {w : ℂ} : RCDiffAt false Φ w ↔ DifferentiableAt ℂ Φ w :=
  Iff.rfl

theorem rcDiffAt_true {Φ : ℂ → ℂ} {w : ℂ} :
    RCDiffAt true Φ w ↔ DifferentiableAt ℂ (Φ ∘ cc) (cc w) := Iff.rfl

theorem RCDiffAt.continuousAt {δ : Bool} {Φ : ℂ → ℂ} {w : ℂ} (h : RCDiffAt δ Φ w) :
    ContinuousAt Φ w := by
  cases δ
  · exact DifferentiableAt.continuousAt (rcDiffAt_false.1 h)
  · have h1 : ContinuousAt (Φ ∘ cc) (cc w) := DifferentiableAt.continuousAt (rcDiffAt_true.1 h)
    have h2 : ContinuousAt (cc : ℂ → ℂ) w := Complex.continuous_conj.continuousAt
    have := h1.comp (x := w) h2
    simpa [Function.comp_def] using this

theorem RCDiffAt.comp {ε δ : Bool} {Φ₁ Φ₂ : ℂ → ℂ} {w : ℂ} (h₁ : RCDiffAt ε Φ₁ (Φ₂ w))
    (h₂ : RCDiffAt δ Φ₂ w) : RCDiffAt (xor ε δ) (Φ₁ ∘ Φ₂) w := by
  cases ε <;> cases δ
  · exact DifferentiableAt.comp w h₁ h₂
  · -- `Φ₁` holomorphic, `Φ₂` antiholomorphic
    change RCDiffAt true _ _
    rw [rcDiffAt_true] at h₂ ⊢
    have h₁' : DifferentiableAt ℂ Φ₁ ((Φ₂ ∘ cc) (cc w)) := by
      simpa [Function.comp_def] using rcDiffAt_false.1 h₁
    exact h₁'.comp (cc w) h₂
  · -- `Φ₁` antiholomorphic, `Φ₂` holomorphic
    change RCDiffAt true _ _
    rw [rcDiffAt_true] at h₁ ⊢
    have h₂' := h₂.conj_conj
    have h₁' : DifferentiableAt ℂ (Φ₁ ∘ cc) ((cc ∘ Φ₂ ∘ cc) (cc w)) := by
      simpa [Function.comp_def] using h₁
    have := h₁'.comp (cc w) h₂'
    simpa [Function.comp_def] using this
  · -- both antiholomorphic
    change RCDiffAt false _ _
    rw [rcDiffAt_true] at h₁ h₂
    have h₂' := h₂.conj_conj
    have h₁' : DifferentiableAt ℂ (Φ₁ ∘ cc) ((cc ∘ (Φ₂ ∘ cc) ∘ cc) (cc (cc w))) := by
      simpa [Function.comp_def] using h₁
    have := h₁'.comp (cc (cc w)) h₂'
    simpa [Function.comp_def, RCDiffAt] using this

/-! ### Holomorphy along a coordinate map -/

/-- `G : X → X` is **holomorphic (`δ = false`) or antiholomorphic (`δ = true`) on `U` along
`π : ℂ → X`**: for every `z` with `π z ∈ U` there is `Φ`, (anti)holomorphic near `z`, with
`π ∘ Φ = G ∘ π` near `z`. -/
def RCAlong (π : ℂ → X) (U : Set X) (G : X → X) (δ : Bool) : Prop :=
  ∀ z, π z ∈ U → ∃ Φ : ℂ → ℂ, (∀ᶠ w in 𝓝 z, RCDiffAt δ Φ w) ∧ ∀ᶠ w in 𝓝 z, π (Φ w) = G (π w)

/-- Holomorphy along `π`. -/
abbrev HolAlong (π : ℂ → X) (U : Set X) (G : X → X) : Prop := RCAlong π U G false

omit [TopologicalSpace X] in
theorem RCAlong.id (π : ℂ → X) (U : Set X) : HolAlong π U _root_.id :=
  fun _ _ => ⟨_root_.id, Eventually.of_forall fun _ => differentiableAt_id,
    Eventually.of_forall fun _ => rfl⟩

omit [TopologicalSpace X] in
theorem RCAlong.comp {π : ℂ → X} {U₁ U₂ : Set X}
    {G H : X → X} {ε δ : Bool} (hG : RCAlong π U₂ G ε) (hH : RCAlong π U₁ H δ)
    (hHU : ∀ x ∈ U₁, H x ∈ U₂) : RCAlong π U₁ (G ∘ H) (xor ε δ) := by
  intro z hz
  obtain ⟨Φ₂, hΦ₂, hΦ₂e⟩ := hH z hz
  have hz' : π (Φ₂ z) ∈ U₂ := by
    rw [hΦ₂e.self_of_nhds]
    exact hHU _ hz
  obtain ⟨Φ₁, hΦ₁, hΦ₁e⟩ := hG (Φ₂ z) hz'
  refine ⟨Φ₁ ∘ Φ₂, ?_, ?_⟩
  · have hc : Tendsto Φ₂ (𝓝 z) (𝓝 (Φ₂ z)) := hΦ₂.self_of_nhds.continuousAt.tendsto
    filter_upwards [hΦ₂, hc.eventually hΦ₁] with w h2 h1
    exact h1.comp h2
  · have hc : Tendsto Φ₂ (𝓝 z) (𝓝 (Φ₂ z)) := hΦ₂.self_of_nhds.continuousAt.tendsto
    filter_upwards [hΦ₂e, hc.eventually hΦ₁e] with w h1 h2
    simp only [Function.comp_apply, h2, h1]

open Classical in
/-- Extension of `g : U → V` to a self-map of `X`, by the identity outside `U`. -/
noncomputable def extendU {U V : Set X} (g : U → V) : X → X :=
  fun x => if h : x ∈ U then (g ⟨x, h⟩ : X) else x

omit [TopologicalSpace X] in
theorem extendU_of_mem {U V : Set X} (g : U → V) {x : X} (hx : x ∈ U) :
    extendU g x = g ⟨x, hx⟩ := by
  simp [extendU, hx]

omit [TopologicalSpace X] in
theorem extendU_mem {U V : Set X} (g : U → V) {x : X} (hx : x ∈ U) : extendU g x ∈ V := by
  rw [extendU_of_mem g hx]
  exact (g _).2

omit [TopologicalSpace X] in
theorem extendU_comp {U V W : Set X} (g : V → W) (h : U → V) :
    EqOn (extendU (g ∘ h)) (extendU g ∘ extendU h) U := by
  intro x hx
  simp only [Function.comp_apply, extendU_of_mem _ hx]
  rw [extendU_of_mem _ (h ⟨x, hx⟩).2]

theorem extendU_mul {U : Set X} (g h : U ≃ₜ U) :
    EqOn (extendU ⇑g ∘ extendU ⇑h) (extendU ⇑(g * h)) U := by
  intro x hx
  simp only [Function.comp_apply, extendU_of_mem _ hx]
  rw [extendU_of_mem _ (h ⟨x, hx⟩).2]
  rfl

theorem RCAlong.congr {π : ℂ → X} (hπ : Continuous π) {U : Set X} (hU : IsOpen U) {G G' : X → X}
    {δ : Bool} (h : RCAlong π U G δ) (hGG' : EqOn G G' U) : RCAlong π U G' δ := by
  intro z hz
  obtain ⟨Φ, hΦ, hΦe⟩ := h z hz
  refine ⟨Φ, hΦ, ?_⟩
  have hU' : ∀ᶠ w in 𝓝 z, π w ∈ U := hπ.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)
  filter_upwards [hΦe, hU'] with w h1 h2
  rw [h1, hGG' h2]

/-! ### The Aut-holomorphic structure -/

/-- **The Aut-holomorphic structure along a coordinate map** `π : ℂ → X`: `A(U)` consists of the
homeomorphisms `g` of `U` such that `g` and `g⁻¹` are holomorphic along `π`. -/
def ofCover {π : ℂ → X} (hπ : Continuous π) : AutHolStr X where
  aut U :=
    { carrier := {g | HolAlong π U (extendU g) ∧ HolAlong π U (extendU g.symm)}
      mul_mem' := by
        intro g h hg hh
        refine ⟨?_, ?_⟩
        · have := hg.1.comp hh.1 fun x hx => extendU_mem _ hx
          exact this.congr hπ U.2 (extendU_mul g h)
        · have e : (g * h).symm = h.symm * g.symm := rfl
          rw [e]
          have := hh.2.comp hg.2 fun x hx => extendU_mem _ hx
          exact this.congr hπ U.2 (extendU_mul h.symm g.symm)
      one_mem' := by
        have : EqOn _root_.id (extendU ⇑(1 : U ≃ₜ U)) U := fun x hx => by
          rw [extendU_of_mem _ hx]
          rfl
        exact ⟨(RCAlong.id π U).congr hπ U.2 this, (RCAlong.id π U).congr hπ U.2 this⟩
      inv_mem' := fun hg => ⟨hg.2, hg.1⟩ }

theorem mem_ofCover_aut {π : ℂ → X} {hπ : Continuous π} {U : Opens X} {g : U ≃ₜ U} :
    g ∈ (ofCover hπ).aut U ↔ HolAlong π U (extendU g) ∧ HolAlong π U (extendU g.symm) :=
  Iff.rfl

/-- Conjugation by a homeomorphism that is (anti)holomorphic along `π` in both directions maps
`A(U)` into `A(V)`. -/
theorem ofCover_conj_mem {π : ℂ → X} (hπ : Continuous π) {U V : Opens X} (e : U ≃ₜ V) {δ : Bool}
    (he : RCAlong π U (extendU e) δ) (he' : RCAlong π V (extendU e.symm) δ) {g : U ≃ₜ U}
    (hg : g ∈ (ofCover hπ).aut U) : conj e g ∈ (ofCover hπ).aut V := by
  have key : ∀ k : U ≃ₜ U, HolAlong π U (extendU k) →
      HolAlong π V (extendU (conj e k)) := by
    intro k hk
    have h1 := hk.comp he' fun x hx => extendU_mem _ hx
    have h2 := he.comp h1 fun x hx => by
      simp only [Function.comp_apply]
      exact extendU_mem _ (extendU_mem _ hx)
    have hxor : xor δ (xor false δ) = false := by cases δ <;> rfl
    rw [hxor] at h2
    refine h2.congr hπ V.2 fun x hx => ?_
    simp only [Function.comp_apply, extendU_of_mem _ hx]
    rw [extendU_of_mem _ (e.symm ⟨x, hx⟩).2, extendU_of_mem _ (k _).2]
    rfl
  refine ⟨key g hg.1, ?_⟩
  have : (conj e g).symm = conj e g.symm := by ext; rfl
  rw [this]
  exact key g.symm hg.2

/-- **RC-holomorphic homeomorphisms are isomorphisms of Aut-holomorphic structures**: if
`e : U ≃ₜ V` and `e⁻¹` are holomorphic (or both antiholomorphic) along `π`, then conjugation by `e`
carries `A(U)` onto `A(V)`. -/
theorem ofCover_conj {π : ℂ → X} (hπ : Continuous π) {U V : Opens X} (e : U ≃ₜ V) {δ : Bool}
    (he : RCAlong π U (extendU e) δ) (he' : RCAlong π V (extendU e.symm) δ) :
    (ofCover hπ).aut V = ((ofCover hπ).aut U).map (conj e).toMonoidHom := by
  ext g
  rw [mem_map_conj]
  constructor
  · intro hg
    exact ofCover_conj_mem hπ e.symm he' he hg
  · intro hg
    have := ofCover_conj_mem hπ e he he' hg
    have h2 : conj e (conj e.symm g) = g := by ext; simp
    rwa [h2] at this

/-! ### Restriction to an open subset -/

namespace AutHolStr

/-- The open subset of `X` underlying an open subset of `W`. -/
def openImage (W : Opens X) (U : Opens W) : Opens X :=
  ⟨Subtype.val '' (U : Set W), W.isOpenEmbedding'.isOpenMap _ U.2⟩

theorem mem_openImage {W : Opens X} {U : Opens W} {x : X} :
    x ∈ openImage W U ↔ ∃ h : x ∈ W, (⟨x, h⟩ : W) ∈ U := by
  simp [openImage]

/-- The tautological homeomorphism `U ≃ₜ openImage W U`. -/
noncomputable def openImageHomeo (W : Opens X) (U : Opens W) : U ≃ₜ openImage W U :=
  (W.isOpenEmbedding'.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by ext x; simp [openImage]))

@[simp]
theorem openImageHomeo_apply (W : Opens X) (U : Opens W) (x : U) :
    (openImageHomeo W U x : X) = (x : W) := rfl

/-- **The Aut-holomorphic space determined by an open subset** `W ⊆ X`: `A_W(U) = A_X(U)`. -/
noncomputable def restrict (A : AutHolStr X) (W : Opens X) : AutHolStr W where
  aut U := (A.aut (openImage W U)).map (conj (openImageHomeo W U).symm).toMonoidHom

theorem mem_restrict_aut {A : AutHolStr X} {W : Opens X} {U : Opens W} {g : U ≃ₜ U} :
    g ∈ (A.restrict W).aut U ↔ conj (openImageHomeo W U) g ∈ A.aut (openImage W U) := by
  rw [restrict, mem_map_conj, Homeomorph.symm_symm]

/-- **The inclusion of an open subset is a morphism of Aut-holomorphic spaces** (an open immersion
in the sense of [AbsTopIII] Corollary 2.7 (b)). -/
theorem aut_eq_map_of_coe {A : AutHolStr X} {O V : Opens X} (k : O ≃ₜ V)
    (hk : ∀ x, (k x : X) = x) : A.aut V = (A.aut O).map (conj k).toMonoidHom := by
  have hOV : O = V := by
    ext x
    constructor
    · intro hx
      have := (k ⟨x, hx⟩).2
      rwa [hk] at this
    · intro hx
      obtain ⟨y, hy⟩ := k.surjective ⟨x, hx⟩
      have h1 := congrArg Subtype.val hy
      rw [hk] at h1
      have h2 : (y : X) = x := h1
      rw [← h2]
      exact y.2
  subst hOV
  have : k = Homeomorph.refl O := by
    ext x
    exact hk x
  subst this
  ext g
  rw [mem_map_conj]
  rfl

theorem isMorphism_val (A : AutHolStr X) (W : Opens X) :
    IsMorphism (A.restrict W) A (Subtype.val : W → X) := by
  refine ⟨W.isOpenEmbedding'.isLocalHomeomorph, ?_⟩
  intro U _ V _ e he
  rw [restrict, map_conj_trans]
  refine aut_eq_map_of_coe _ fun x => ?_
  rw [Homeomorph.trans_apply, he]
  have := congrArg Subtype.val ((openImageHomeo W U).apply_symm_apply x)
  rw [openImageHomeo_apply] at this
  exact this

end AutHolStr

end AutHol

end Iut
