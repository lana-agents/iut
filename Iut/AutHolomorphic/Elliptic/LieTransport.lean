/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.AutHolomorphic.Elliptic.TorusField

/-!
# Transport of `A_p` along additive homeomorphisms that are local isomorphisms

[AbsTopIII] Corollary 2.7 (e) defines `A_p` from the germ at `p` of the Aut-holomorphic structure
and from the local additive structure of Corollary 2.7 (c). Here, for commutative topological
groups `Y`, `Y'` with Aut-holomorphic structures `A`, `A'`:

* `lieMap Θ hΘ : Lie Y ≃ₗ[ℝ] Lie Y'`: post-composition of one-parameter subgroups with an
  additive homeomorphism `Θ : Y ≃ₜ Y'`; it is a homeomorphism (`lieHomeoMap`) and
  `exp_{Θ p} ∘ lieMap Θ = Θ ∘ exp_p` (`expAt_lieMap`); `lieConj Θ hΘ M` is the conjugate of an
  endomorphism `M` of `Lie Y`;
* `IsIsoNear A A' Θ O`: `Θ` is an isomorphism of Aut-holomorphic spaces on the connected opens
  inside `O` ([AbsTopIII] Definition 2.1 (ii), restricted to `O`);
* **`IsLinHol.transport`, `mem_fieldSet_transport`**: if `Θ` is an isomorphism near `p`, then
  `M` is holomorphic at `p` iff `lieConj Θ M` is holomorphic at `Θ p`, and
  `fieldSet A p = A_p ∪ {0}` corresponds to `fieldSet A' (Θ p)` under `lieConj Θ` (**locality**:
  only the germ of `A` at `p` matters; **functoriality**: isomorphisms carry `A_p` to `A_{Θ p}`).

For the complex torus: every `ℝ`-linear endomorphism of `Lie T_Λ` is continuous
(`continuous_linearMap_lie`), and `fieldSet (torusStr L) x` is the set of maps `c ↦ b c` for every
`x : T_Λ` (`mem_fieldSet_iff'`).
-/

namespace Iut

namespace AutHol

namespace Ell

open Set Topology Filter TopologicalSpace

section Generic

variable {Y Y' : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [AddCommGroup Y'] [TopologicalSpace Y'] [IsTopologicalAddGroup Y']
  (Θ : Y ≃ₜ Y') (hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y)

omit [IsTopologicalAddGroup Y] [IsTopologicalAddGroup Y'] in
include hΘ in
theorem symm_add : ∀ x y, Θ.symm (x + y) = Θ.symm x + Θ.symm y := by
  intro x y
  apply Θ.injective
  rw [hΘ]
  simp

/-- Post-composition of a one-parameter subgroup with an additive homeomorphism. -/
def lieFun (f : Lie Y) : Lie Y' :=
  ⟨AddMonoidHom.mk' (fun t => Θ (f t)) (fun s t => by simp only [map_add, hΘ]),
    Θ.continuous.comp f.continuous⟩

omit [IsTopologicalAddGroup Y] [IsTopologicalAddGroup Y'] in
@[simp]
theorem lieFun_apply (f : Lie Y) (t : ℝ) : lieFun Θ hΘ f t = Θ (f t) := rfl

/-- **The isomorphism of tangent spaces** `Lie Y ≃ Lie Y'` induced by an additive homeomorphism. -/
def lieMap : Lie Y ≃ₗ[ℝ] Lie Y' where
  toFun := lieFun Θ hΘ
  invFun := lieFun Θ.symm (symm_add Θ hΘ)
  map_add' f g := by ext t; simp [hΘ]
  map_smul' r f := by ext t; rfl
  left_inv f := by ext t; simp
  right_inv f := by ext t; simp

@[simp]
theorem lieMap_apply (f : Lie Y) (t : ℝ) : lieMap Θ hΘ f t = Θ (f t) := rfl

@[simp]
theorem lieMap_symm_apply (f : Lie Y') (t : ℝ) : (lieMap Θ hΘ).symm f t = Θ.symm (f t) := rfl

theorem lieMap_symm_eq (f : Lie Y') : lieMap Θ.symm (symm_add Θ hΘ) f = (lieMap Θ hΘ).symm f :=
  rfl

theorem lieMap_symm_symm_eq (f : Lie Y) :
    (lieMap Θ.symm (symm_add Θ hΘ)).symm f = lieMap Θ hΘ f := rfl

omit [IsTopologicalAddGroup Y] [IsTopologicalAddGroup Y'] in
theorem continuous_lieFun : Continuous (lieFun Θ hΘ) := by
  refine (ContinuousAddMonoidHom.isInducing_toContinuousMap ℝ Y').continuous_iff.2 ?_
  exact (ContinuousMap.continuous_postcomp (⟨Θ, Θ.continuous⟩ : C(Y, Y'))).comp
    (ContinuousAddMonoidHom.isInducing_toContinuousMap ℝ Y).continuous

theorem continuous_lieMap : Continuous (lieMap Θ hΘ) := continuous_lieFun Θ hΘ

theorem continuous_lieMap_symm : Continuous (lieMap Θ hΘ).symm :=
  continuous_lieFun Θ.symm (symm_add Θ hΘ)

/-- `lieMap` as a homeomorphism for the compact-open topologies. -/
noncomputable def lieHomeoMap : Lie Y ≃ₜ Lie Y' where
  toEquiv := (lieMap Θ hΘ).toEquiv
  continuous_toFun := continuous_lieMap Θ hΘ
  continuous_invFun := continuous_lieMap_symm Θ hΘ

theorem expAt_lieMap (p : Y) (f : Lie Y) : expAt (Θ p) (lieMap Θ hΘ f) = Θ (expAt p f) := by
  simp only [expAt, lieMap_apply, hΘ]

/-- The conjugate `lieMap Θ ∘ M ∘ (lieMap Θ)⁻¹` of an endomorphism of `Lie Y`. -/
def lieConj (M : Lie Y →ₗ[ℝ] Lie Y) : Lie Y' →ₗ[ℝ] Lie Y' :=
  (lieMap Θ hΘ).toLinearMap ∘ₗ M ∘ₗ (lieMap Θ hΘ).symm.toLinearMap

theorem lieConj_apply (M : Lie Y →ₗ[ℝ] Lie Y) (f : Lie Y') :
    lieConj Θ hΘ M f = lieMap Θ hΘ (M ((lieMap Θ hΘ).symm f)) := rfl

@[simp]
theorem lieConj_lieMap (M : Lie Y →ₗ[ℝ] Lie Y) (f : Lie Y) :
    lieConj Θ hΘ M (lieMap Θ hΘ f) = lieMap Θ hΘ (M f) := by
  simp [lieConj_apply]

theorem lieConj_symm_lieConj (M : Lie Y →ₗ[ℝ] Lie Y) :
    lieConj Θ.symm (symm_add Θ hΘ) (lieConj Θ hΘ M) = M := by
  refine LinearMap.ext fun f => ?_
  rw [lieConj_apply, lieMap_symm_symm_eq Θ hΘ, lieConj_lieMap Θ hΘ, lieMap_symm_eq Θ hΘ,
    LinearEquiv.symm_apply_apply]

theorem lieConj_lieConj_symm (M : Lie Y' →ₗ[ℝ] Lie Y') :
    lieConj Θ hΘ (lieConj Θ.symm (symm_add Θ hΘ) M) = M := by
  refine LinearMap.ext fun f => ?_
  obtain ⟨g, rfl⟩ := (lieMap Θ hΘ).surjective f
  rw [lieConj_lieMap Θ hΘ, lieConj_apply, lieMap_symm_symm_eq Θ hΘ, lieMap_symm_eq Θ hΘ,
    LinearEquiv.apply_symm_apply]

theorem lieConj_add (M M' : Lie Y →ₗ[ℝ] Lie Y) :
    lieConj Θ hΘ (M + M') = lieConj Θ hΘ M + lieConj Θ hΘ M' :=
  LinearMap.ext fun f => by simp [lieConj_apply]

theorem lieConj_mul (M M' : Lie Y →ₗ[ℝ] Lie Y) :
    lieConj Θ hΘ (M * M') = lieConj Θ hΘ M * lieConj Θ hΘ M' :=
  LinearMap.ext fun f => by simp [lieConj_apply]

theorem lieConj_zero : lieConj Θ hΘ (0 : Lie Y →ₗ[ℝ] Lie Y) = 0 :=
  LinearMap.ext fun f => by simp [lieConj_apply]

theorem lieConj_injective : Function.Injective (lieConj Θ hΘ) := by
  intro M M' h
  rw [← lieConj_symm_lieConj Θ hΘ M, h, lieConj_symm_lieConj]

theorem lieConj_eq_zero_iff (M : Lie Y →ₗ[ℝ] Lie Y) : lieConj Θ hΘ M = 0 ↔ M = 0 := by
  rw [← lieConj_zero Θ hΘ]
  exact (lieConj_injective Θ hΘ).eq_iff

/-- The conjugate of an automorphism of `Lie Y`. -/
def lieConjEquiv (N : Lie Y ≃ₗ[ℝ] Lie Y) : Lie Y' ≃ₗ[ℝ] Lie Y' :=
  ((lieMap Θ hΘ).symm.trans N).trans (lieMap Θ hΘ)

theorem lieConjEquiv_toLinearMap (N : Lie Y ≃ₗ[ℝ] Lie Y) :
    (lieConjEquiv Θ hΘ N).toLinearMap = lieConj Θ hΘ N.toLinearMap :=
  LinearMap.ext fun _ => rfl

theorem lieConj_trans (N : Lie Y ≃ₗ[ℝ] Lie Y) :
    lieConj Θ hΘ (N.trans N).toLinearMap =
      ((lieConjEquiv Θ hΘ N).trans (lieConjEquiv Θ hΘ N)).toLinearMap :=
  LinearMap.ext fun f => by simp [lieConj_apply, lieConjEquiv]

theorem continuous_of_lieConj {M : Lie Y →ₗ[ℝ] Lie Y} (hM : Continuous (lieConj Θ hΘ M)) :
    Continuous M := by
  have h : (M : Lie Y → Lie Y) = (lieMap Θ hΘ).symm ∘ lieConj Θ hΘ M ∘ lieMap Θ hΘ := by
    funext f
    simp
  rw [h]
  exact (continuous_lieMap_symm Θ hΘ).comp (hM.comp (continuous_lieMap Θ hΘ))

end Generic

/-! ### Isomorphisms near a subset -/

section Near

variable {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X']

/-- **`Θ` is an isomorphism of Aut-holomorphic spaces on the connected opens inside `O`**
([AbsTopIII] Definition 2.1 (ii), with `𝒰` the connected opens inside `O`). -/
def IsIsoNear (A : AutHolStr X) (A' : AutHolStr X') (Θ : X ≃ₜ X') (O : Set X) : Prop :=
  ∀ U : Opens X, (U : Set X) ⊆ O → IsConnected (U : Set X) → ∀ V : Opens X', ∀ e : U ≃ₜ V,
    (∀ x : U, (e x : X') = Θ x) → A'.aut V = (A.aut U).map (conj e).toMonoidHom

theorem IsIsoNear.symm {A : AutHolStr X} {A' : AutHolStr X'} {Θ : X ≃ₜ X'} {O : Set X}
    (h : IsIsoNear A A' Θ O) : IsIsoNear A' A Θ.symm (Θ '' O) := by
  intro V hVO hV U e he
  have hU : IsConnected (U : Set X) := isConnected_of_homeomorph e hV
  have he' : ∀ x : U, (e.symm x : X') = Θ x := by
    intro x
    have h1 := he (e.symm x)
    rw [Homeomorph.apply_symm_apply] at h1
    rw [h1, Homeomorph.apply_symm_apply]
  have hUO : (U : Set X) ⊆ O := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hVO (e.symm ⟨x, hx⟩).2
    rw [he' ⟨x, hx⟩] at hyx
    have hyx' : y = x := Θ.injective hyx
    exact hyx' ▸ hy
  rw [h U hUO hU V e.symm he', map_conj_trans]
  have : e.symm.trans e = Homeomorph.refl U := by ext; simp
  rw [this]
  ext g
  rw [mem_map_conj]
  rfl

theorem IsIso.isIsoNear {A : AutHolStr X} {A' : AutHolStr X'} {Θ : X ≃ₜ X'} (h : IsIso A A' Θ)
    (O : Set X) : IsIsoNear A A' Θ O := fun U _ hU V e he => (IsIso.iff Θ).1 h U hU V e he

end Near

section Generic

variable {Y Y' : Type*} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y]
  [AddCommGroup Y'] [TopologicalSpace Y'] [IsTopologicalAddGroup Y']
  {Θ : Y ≃ₜ Y'} (hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y) {A : AutHolStr Y} {A' : AutHolStr Y'}
  {p : Y} {O : Set Y}

include hΘ in
/-- **Transport and locality of holomorphy at `p`**: if the additive homeomorphism `Θ` is an
isomorphism of Aut-holomorphic spaces near `p`, it carries the continuous endomorphisms of
`Lie Y` holomorphic at `p` to endomorphisms of `Lie Y'` holomorphic at `Θ p`. -/
theorem IsLinHol.transport (hO : O ∈ 𝓝 p) (hΘO : IsIsoNear A A' Θ O)
    {M : Lie Y →ₗ[ℝ] Lie Y} (hM : Continuous M) (h : IsLinHol A p M) :
    IsLinHol A' (Θ p) (lieConj Θ hΘ M) := by
  obtain ⟨N, hN, hinj, hinjM, hcond⟩ := h
  have hexp0 : expAt p (0 : Lie Y) = p := by simp [expAt]
  have hO1 : expAt p ⁻¹' O ∈ 𝓝 (0 : Lie Y) :=
    (continuous_expAt p).continuousAt.preimage_mem_nhds (by rwa [hexp0])
  have hO2 : M ⁻¹' (expAt p ⁻¹' O) ∈ 𝓝 (0 : Lie Y) :=
    hM.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact hO1)
  set N₁ := N ∩ expAt p ⁻¹' O ∩ M ⁻¹' (expAt p ⁻¹' O) with hN₁def
  have hN₁ : N₁ ∈ 𝓝 (0 : Lie Y) := inter_mem (inter_mem hN hO1) hO2
  refine ⟨lieMap Θ hΘ '' N₁, ?_, ?_, ?_, ?_⟩
  · have := (lieHomeoMap Θ hΘ).isOpenMap.image_mem_nhds hN₁
    exact (by simpa [lieHomeoMap] using this)
  · rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩ hfg
    rw [expAt_lieMap, expAt_lieMap] at hfg
    rw [hinj hf.1.1 hg.1.1 (Θ.injective hfg)]
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩ _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩ hfg
    rw [lieConj_lieMap, lieConj_lieMap, expAt_lieMap, expAt_lieMap] at hfg
    rw [lieConj_lieMap, lieConj_lieMap,
      hinjM (mem_image_of_mem M hf.1.1) (mem_image_of_mem M hg.1.1) (Θ.injective hfg)]
  · intro W' U' V' e' hW'N hW'o hW'c hU' hV' he'
    set W := lieMap Θ hΘ ⁻¹' W' with hWdef
    have hWN : W ⊆ N₁ := fun f hf => by
      obtain ⟨g, hg, hgf⟩ := hW'N hf
      rwa [(lieMap Θ hΘ).injective hgf] at hg
    have hWo : IsOpen W := hW'o.preimage (continuous_lieMap Θ hΘ)
    have hWc : IsConnected W := by
      have : W = (lieMap Θ hΘ).symm '' W' := ((lieMap Θ hΘ).image_symm_eq_preimage W').symm
      rw [this]
      exact hW'c.image _ (continuous_lieMap_symm Θ hΘ).continuousOn
    let U : Opens Y := ⟨Θ ⁻¹' U', U'.2.preimage Θ.continuous⟩
    let V : Opens Y := ⟨Θ ⁻¹' V', V'.2.preimage Θ.continuous⟩
    have hU : (U : Set Y) = expAt p '' W := by
      ext x
      change Θ x ∈ (U' : Set Y') ↔ _
      rw [hU']
      constructor
      · rintro ⟨f', hf', hfx⟩
        obtain ⟨f, rfl⟩ := (lieMap Θ hΘ).surjective f'
        rw [expAt_lieMap] at hfx
        exact ⟨f, hf', Θ.injective hfx⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨lieMap Θ hΘ f, hf, expAt_lieMap Θ hΘ p f⟩
    have hV : (V : Set Y) = expAt p '' (M '' W) := by
      ext x
      change Θ x ∈ (V' : Set Y') ↔ _
      rw [hV']
      constructor
      · rintro ⟨_, ⟨f', hf', rfl⟩, hfx⟩
        obtain ⟨f, rfl⟩ := (lieMap Θ hΘ).surjective f'
        rw [lieConj_lieMap, expAt_lieMap] at hfx
        exact ⟨M f, ⟨f, hf', rfl⟩, Θ.injective hfx⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨_, ⟨lieMap Θ hΘ f, hf, rfl⟩, by rw [lieConj_lieMap, expAt_lieMap]⟩
    let eU : U ≃ₜ U' := Θ.subtype fun _ => Iff.rfl
    let eV : V ≃ₜ V' := Θ.subtype fun _ => Iff.rfl
    let e : U ≃ₜ V := eU.trans (e'.trans eV.symm)
    have he : ∀ f ∈ W, ∀ h : expAt p f ∈ U, (e ⟨expAt p f, h⟩ : Y) = expAt p (M f) := by
      intro f hf h
      have h' : expAt (Θ p) (lieMap Θ hΘ f) ∈ U' := by rw [expAt_lieMap]; exact h
      have h1 : (e' ⟨_, h'⟩ : Y') = Θ (expAt p (M f)) := by
        rw [he' _ hf h', lieConj_lieMap, expAt_lieMap]
      have hx : eU ⟨expAt p f, h⟩ = ⟨expAt (Θ p) (lieMap Θ hΘ f), h'⟩ :=
        Subtype.ext (expAt_lieMap Θ hΘ p f).symm
      change Θ.symm (e' (eU ⟨expAt p f, h⟩)) = _
      rw [hx, h1, Homeomorph.symm_apply_apply]
    have hUc : IsConnected (U : Set Y) := by
      rw [hU]
      exact hWc.image _ (continuous_expAt p).continuousOn
    have hUO : (U : Set Y) ⊆ O := by
      rw [hU]
      rintro _ ⟨f, hf, rfl⟩
      exact (hWN hf).1.2
    have hVO : (V : Set Y) ⊆ O := by
      rw [hV]
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      exact (hWN hf).2
    have hVc : IsConnected (V : Set Y) := isConnected_of_homeomorph e hUc
    have h1 := hcond W U V e (hWN.trans (inter_subset_left.trans inter_subset_left)) hWo hWc hU
      hV he
    have h2 := hΘO U hUO hUc U' eU fun _ => rfl
    have h3 := hΘO V hVO hVc V' eV fun _ => rfl
    rw [h3, h1, h2, map_conj_trans, map_conj_trans]
    have : e.trans eV = eU.trans e' := by
      ext x
      simp [e]
    rw [this]

include hΘ in
/-- **Holomorphy at `p` is invariant under additive homeomorphisms that are isomorphisms near
`p`.** -/
theorem isLinHol_transport_iff (hO : O ∈ 𝓝 p) (hΘO : IsIsoNear A A' Θ O)
    {M : Lie Y →ₗ[ℝ] Lie Y} (hM : Continuous M) (hM' : Continuous (lieConj Θ hΘ M)) :
    IsLinHol A p M ↔ IsLinHol A' (Θ p) (lieConj Θ hΘ M) := by
  refine ⟨IsLinHol.transport hΘ hO hΘO hM, fun h => ?_⟩
  have hO' : Θ '' O ∈ 𝓝 (Θ p) := Θ.isOpenMap.image_mem_nhds hO
  have := IsLinHol.transport (symm_add Θ hΘ) hO' hΘO.symm hM' h
  rwa [Homeomorph.symm_apply_apply, lieConj_symm_lieConj] at this

include hΘ in
/-- **`A_p ∪ {0}` is carried to `A_{Θ p} ∪ {0}`** by an additive homeomorphism that is an
isomorphism of Aut-holomorphic spaces near `p`, provided all `ℝ`-linear endomorphisms of `Lie Y'`
are continuous. -/
theorem mem_apSet_transport (hO : O ∈ 𝓝 p) (hΘO : IsIsoNear A A' Θ O)
    (hcont : ∀ M : Lie Y' →ₗ[ℝ] Lie Y', Continuous M) (M : Lie Y →ₗ[ℝ] Lie Y) :
    M ∈ apSet A p ↔ lieConj Θ hΘ M ∈ apSet A' (Θ p) := by
  have hc : ∀ M : Lie Y →ₗ[ℝ] Lie Y, Continuous M := fun M =>
    continuous_of_lieConj Θ hΘ (hcont _)
  constructor
  · rintro ⟨N, hN, rfl⟩
    refine ⟨lieConjEquiv Θ hΘ N, ?_, lieConj_trans Θ hΘ N⟩
    change IsLinHol A' (Θ p) (lieConjEquiv Θ hΘ N).toLinearMap
    rw [lieConjEquiv_toLinearMap]
    exact (isLinHol_transport_iff hΘ hO hΘO (hc _) (hcont _)).1 hN
  · rintro ⟨N', hN', hM⟩
    let N := lieConjEquiv Θ.symm (symm_add Θ hΘ) N'
    have hNN : lieConj Θ hΘ N.toLinearMap = N'.toLinearMap := by
      rw [lieConjEquiv_toLinearMap, lieConj_lieConj_symm]
    refine ⟨N, ?_, ?_⟩
    · change IsLinHol A p N.toLinearMap
      rw [isLinHol_transport_iff hΘ hO hΘO (hc _) (hcont _), hNN]
      exact hN'
    · have hN2 : lieConjEquiv Θ hΘ N = N' := by
        apply LinearEquiv.toLinearMap_injective
        rw [lieConjEquiv_toLinearMap, hNN]
      apply lieConj_injective Θ hΘ
      rw [hM, lieConj_trans, hN2]

include hΘ in
theorem mem_fieldSet_transport (hO : O ∈ 𝓝 p) (hΘO : IsIsoNear A A' Θ O)
    (hcont : ∀ M : Lie Y' →ₗ[ℝ] Lie Y', Continuous M) (M : Lie Y →ₗ[ℝ] Lie Y) :
    M ∈ fieldSet A p ↔ lieConj Θ hΘ M ∈ fieldSet A' (Θ p) := by
  rw [fieldSet, fieldSet, mem_union, mem_union, mem_apSet_transport hΘ hO hΘO hcont,
    mem_singleton_iff, mem_singleton_iff, lieConj_eq_zero_iff]

end Generic

/-! ### The complex torus -/

variable {L : PeriodPair}

open Torus

/-- **Every `ℝ`-linear endomorphism of `Lie T_Λ` is continuous** (`Lie T_Λ ≃ₜ ℂ`). -/
theorem continuous_linearMap_lie (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) : Continuous M := by
  let M₀ : ℂ →ₗ[ℝ] ℂ :=
    (lieEquiv (L := L)).symm.toLinearMap ∘ₗ M ∘ₗ (lieEquiv (L := L)).toLinearMap
  have hc : Continuous M₀ := LinearMap.continuous_of_finiteDimensional M₀
  have h : (M : Lie (Torus L) → Lie (Torus L)) = line ∘ M₀ ∘ (lieEquiv (L := L)).symm := by
    funext f
    simp [M₀, ← lieEquiv_apply]
  rw [h]
  exact continuous_line.comp (hc.comp continuous_lieEquiv_symm)

/-- `fieldSet` of the torus at any point. -/
theorem mem_fieldSet_iff' (x : Torus L) (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) :
    M ∈ fieldSet (torusStr L) x ↔ ∃ b, M = mulMap b := by
  obtain ⟨q, rfl⟩ := mk_surjective x
  exact mem_fieldSet_iff q M

theorem mem_apSet_iff' (x : Torus L) (M : Lie (Torus L) →ₗ[ℝ] Lie (Torus L)) :
    M ∈ apSet (torusStr L) x ↔ ∃ b, b ≠ 0 ∧ M = mulMap b := by
  obtain ⟨q, rfl⟩ := mk_surjective x
  exact mem_apSet_iff q M

end Ell

end AutHol

end Iut
