/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.Heisenberg
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Constructions

/-!
# The cyclotomic envelope ([EtTh], Definition 2.10, Propositions 2.11, 2.12(ii))

For a topological group `Π` with an augmentation `Π ↠ G_K` and the cyclotome `μ_N`, the
**cyclotomic envelope** is `Π[μ_N] = Π ×_{G_K} (μ_N ⋊ G_K)` ([EtTh], Definition 2.10). Since
`Π` acts on `μ_N` through `G_K`, this is the semidirect product `μ_N ⋊ Π` for the action
`φ : Π →* MulAut μ_N` through the augmentation; the **tautological section** is
`inr : Π → μ_N ⋊ Π` and the kernel of `Π[μ_N] ↠ Π` is `inl(μ_N)`. We give `μ ⋊[φ] Π` the
product topology (a scoped instance, `Envelope.instTopologicalSpace`).

A topological group is **temp-slim** (`TempSlim`) if every open subgroup has trivial
centralizer ([EtTh], proof of Proposition 2.11; [Mzk14], Example 3.10).

## Main results

* `Envelope.mem_range_inl_iff`: **[EtTh], Proposition 2.11(ii)**: if `Π` is temp-slim, `μ` is
  discrete and `Π` acts on `μ` through an open kernel, then the kernel `μ` of `Π[μ] ↠ Π` is the
  union of the centralizers of the open subgroups of `Π[μ]`.
* `Envelope.map_range_inl`, `Envelope.rightEquiv`, `Envelope.rightEquiv_rightHom`: hence any
  isomorphism of topological groups `Π_α[μ_α] ≅ Π_β[μ_β]` maps `μ_α` onto `μ_β` and is
  compatible with the surjections `Π_□[μ_□] ↠ Π_□`.
* `Envelope.center_eq_range_inl`: **[EtTh], Proposition 2.11(i)**: for the geometric part `Δ`
  (acting trivially on `μ`), the kernel of `Δ[μ] ↠ Δ` is the center of `Δ[μ]`.
* `commutator_prod_inf`: **[EtTh], Proposition 2.12(ii) from 2.12(i)**: if `S ⊆ [Δ, Δ]` then
  `[Δ × μ, Δ × μ] ∩ S[μ]` is the image of `S` under the tautological section;
  `ThetaGroup.commutator_envelope_inf` is the case of the theta group `Δ^Θ` and `S = l·Δ_Θ`
  (Proposition 2.12(i) is `ThetaGroup.commutator_eq_theta`).

Temp-slimness of the tempered fundamental groups of hyperbolic orbicurves over `p`-adic fields
is not proved here (see `README.md`, research-level items).
-/

namespace Iut.EtaleTheta

open SemidirectProduct

/-- **Temp-slim topological groups** ([EtTh], proof of Prop. 2.11; [Mzk14], Example 3.10): the
centralizer of every open subgroup is trivial. -/
def TempSlim (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ H : Subgroup P, IsOpen (H : Set P) → Subgroup.centralizer (H : Set P) = ⊥

lemma TempSlim.center_eq_bot {P : Type*} [Group P] [TopologicalSpace P] (h : TempSlim P) :
    Subgroup.center P = ⊥ := by
  rw [← Subgroup.centralizer_univ]
  exact h ⊤ isOpen_univ

namespace Envelope

variable {μ P : Type*} [CommGroup μ] [Group P] [TopologicalSpace μ] [TopologicalSpace P]
  {φ : P →* MulAut μ}

/-- The product topology on the cyclotomic envelope `μ ⋊[φ] P`. -/
scoped instance instTopologicalSpace : TopologicalSpace (μ ⋊[φ] P) :=
  TopologicalSpace.induced equivProd inferInstance

/-- `μ ⋊[φ] P ≃ₜ μ × P`. -/
def homeomorphProd : (μ ⋊[φ] P) ≃ₜ μ × P where
  toEquiv := equivProd
  continuous_toFun := continuous_induced_dom
  continuous_invFun := continuous_induced_rng.2 (by
    change Continuous (equivProd ∘ equivProd.symm)
    simpa using continuous_id)

lemma isOpenMap_rightHom : IsOpenMap (rightHom : μ ⋊[φ] P → P) :=
  isOpenMap_snd.comp (homeomorphProd (φ := φ)).isOpenMap

/-- The open subgroup `inr(ker φ)`, which centralizes `inl(μ)`. -/
def kerSection (φ : P →* MulAut μ) : Subgroup (μ ⋊[φ] P) := φ.ker.map inr

lemma isOpen_kerSection [DiscreteTopology μ] (hφ : IsOpen (φ.ker : Set P)) :
    IsOpen (kerSection φ : Set (μ ⋊[φ] P)) := by
  have : (kerSection φ : Set (μ ⋊[φ] P)) =
      homeomorphProd ⁻¹' (({1} : Set μ) ×ˢ (φ.ker : Set P)) := by
    ext x
    simp only [kerSection, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨rfl, hg⟩
    · rintro ⟨h1, h2⟩
      exact ⟨x.right, h2, SemidirectProduct.ext h1.symm rfl⟩
  rw [this]
  exact (isOpen_discrete _).prod hφ |>.preimage homeomorphProd.continuous

omit [TopologicalSpace μ] [TopologicalSpace P] in
lemma inl_mem_centralizer_kerSection (m : μ) :
    inl m ∈ Subgroup.centralizer (kerSection φ : Set (μ ⋊[φ] P)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : φ g = 1 := hg
  ext <;> simp [hg']

/-- **[EtTh], Proposition 2.11(ii)**: for `P` temp-slim, `μ` discrete and the action of `P` on
`μ` having open kernel, the kernel `inl(μ)` of `P[μ] ↠ P` is the union of the centralizers of
the open subgroups of `P[μ]`. -/
theorem mem_range_inl_iff [DiscreteTopology μ] (hP : TempSlim P) (hφ : IsOpen (φ.ker : Set P))
    (x : μ ⋊[φ] P) :
    x ∈ (inl : μ →* μ ⋊[φ] P).range ↔
      ∃ V : Subgroup (μ ⋊[φ] P), IsOpen (V : Set (μ ⋊[φ] P)) ∧
        x ∈ Subgroup.centralizer (V : Set (μ ⋊[φ] P)) := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨kerSection φ, isOpen_kerSection hφ, inl_mem_centralizer_kerSection m⟩
  · rintro ⟨V, hV, hx⟩
    have hW : IsOpen ((V.map rightHom : Subgroup P) : Set P) := by
      rw [Subgroup.coe_map]
      exact isOpenMap_rightHom _ hV
    have hxr : x.right ∈ Subgroup.centralizer ((V.map rightHom : Subgroup P) : Set P) := by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      rintro _ ⟨v, hv, rfl⟩
      have := congrArg rightHom (hx v hv)
      rw [map_mul, map_mul] at this
      exact this
    rw [hP _ hW, Subgroup.mem_bot] at hxr
    rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    exact hxr

variable {μ' P' : Type*} [CommGroup μ'] [Group P'] [TopologicalSpace μ'] [TopologicalSpace P']
  {φ' : P' →* MulAut μ'}

/-- Isomorphisms of topological groups preserve the union of the centralizers of open
subgroups. -/
lemma exists_open_centralizer_map (e : (μ ⋊[φ] P) ≃ₜ* (μ' ⋊[φ'] P')) {x : μ ⋊[φ] P}
    (h : ∃ V : Subgroup (μ ⋊[φ] P), IsOpen (V : Set (μ ⋊[φ] P)) ∧
      x ∈ Subgroup.centralizer (V : Set (μ ⋊[φ] P))) :
    ∃ V : Subgroup (μ' ⋊[φ'] P'), IsOpen (V : Set (μ' ⋊[φ'] P')) ∧
      e x ∈ Subgroup.centralizer (V : Set (μ' ⋊[φ'] P')) := by
  obtain ⟨V, hV, hx⟩ := h
  refine ⟨V.map e.toMulEquiv.toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact e.toHomeomorph.isOpenMap _ hV
  · rw [Subgroup.mem_centralizer_iff] at hx ⊢
    rintro _ ⟨v, hv, rfl⟩
    have := congrArg e (hx v hv)
    rw [map_mul, map_mul] at this
    exact this

/-- **Isomorphisms of cyclotomic envelopes preserve the kernel** ([EtTh], Prop. 2.11(ii)): for
`P`, `P'` temp-slim, an isomorphism of topological groups `P[μ] ≅ P'[μ']` maps `μ` onto `μ'`. -/
theorem apply_mem_range_inl_iff [DiscreteTopology μ] [DiscreteTopology μ'] (hP : TempSlim P)
    (hP' : TempSlim P') (hφ : IsOpen (φ.ker : Set P)) (hφ' : IsOpen (φ'.ker : Set P'))
    (e : (μ ⋊[φ] P) ≃ₜ* (μ' ⋊[φ'] P')) (x : μ ⋊[φ] P) :
    e x ∈ (inl : μ' →* μ' ⋊[φ'] P').range ↔ x ∈ (inl : μ →* μ ⋊[φ] P).range := by
  rw [mem_range_inl_iff hP' hφ', mem_range_inl_iff hP hφ]
  refine ⟨fun h => ?_, exists_open_centralizer_map e⟩
  have := exists_open_centralizer_map e.symm h
  simpa using this

theorem map_range_inl [DiscreteTopology μ] [DiscreteTopology μ'] (hP : TempSlim P)
    (hP' : TempSlim P') (hφ : IsOpen (φ.ker : Set P)) (hφ' : IsOpen (φ'.ker : Set P'))
    (e : (μ ⋊[φ] P) ≃ₜ* (μ' ⋊[φ'] P')) :
    (inl : μ →* μ ⋊[φ] P).range.map e.toMulEquiv.toMonoidHom = (inl : μ' →* μ' ⋊[φ'] P').range := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (apply_mem_range_inl_iff hP hP' hφ hφ' e x).2 hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [← apply_mem_range_inl_iff hP hP' hφ hφ' e]
    simpa using hy

section RightEquiv

variable [DiscreteTopology μ] [DiscreteTopology μ'] (hP : TempSlim P) (hP' : TempSlim P')
  (hφ : IsOpen (φ.ker : Set P)) (hφ' : IsOpen (φ'.ker : Set P'))
  (e : (μ ⋊[φ] P) ≃ₜ* (μ' ⋊[φ'] P'))

/-- The homomorphism `P → P'` induced by an isomorphism of envelopes. -/
def rightHomOf (e : (μ ⋊[φ] P) ≃ₜ* (μ' ⋊[φ'] P')) : P →* P' :=
  rightHom.comp (e.toMulEquiv.toMonoidHom.comp inr)

include hP hP' hφ hφ' in
/-- The induced map is compatible with the surjections onto `P`, `P'`. -/
theorem rightHomOf_rightHom (x : μ ⋊[φ] P) : rightHomOf e (rightHom x) = rightHom (e x) := by
  have hx : x = inl x.left * inr x.right := by ext <;> simp
  have h1 : rightHom (e (inl x.left)) = 1 := by
    have := (apply_mem_range_inl_iff hP hP' hφ hφ' e (inl x.left)).2 ⟨x.left, rfl⟩
    rw [range_inl_eq_ker_rightHom, MonoidHom.mem_ker] at this
    exact this
  conv_rhs => rw [hx]
  rw [map_mul, map_mul, h1, one_mul]
  rfl

include hP hP' hφ hφ' in
lemma rightHomOf_symm_comp (p : P) : rightHomOf e.symm (rightHomOf e p) = p := by
  have h := rightHomOf_rightHom hP' hP hφ' hφ e.symm (e (inr p))
  rw [ContinuousMulEquiv.symm_apply_apply, rightHom_inr] at h
  have h2 := rightHomOf_rightHom hP hP' hφ hφ' e (inr p)
  rw [rightHom_inr] at h2
  rw [h2, h]

/-- **[EtTh], Prop. 2.11(ii)**: an isomorphism of topological groups `P[μ] ≅ P'[μ']` induces an
isomorphism `P ≃* P'` compatible with the natural surjections (`rightEquiv_rightHom`). -/
def rightEquiv : P ≃* P' where
  toFun := rightHomOf e
  invFun := rightHomOf e.symm
  left_inv := rightHomOf_symm_comp hP hP' hφ hφ' e
  right_inv p := by
    have := rightHomOf_symm_comp hP' hP hφ' hφ e.symm p
    simpa using this
  map_mul' := map_mul _

theorem rightEquiv_rightHom (x : μ ⋊[φ] P) :
    rightEquiv hP hP' hφ hφ' e (rightHom x) = rightHom (e x) :=
  rightHomOf_rightHom hP hP' hφ hφ' e x

end RightEquiv

/-- **[EtTh], Proposition 2.11(i)**: if `Δ` is temp-slim and acts trivially on `μ` (the
geometric part), the kernel `inl(μ)` of `Δ[μ] ↠ Δ` is the center of `Δ[μ]`. -/
theorem center_eq_range_inl [DiscreteTopology μ] (hP : TempSlim P) (hφ1 : ∀ g, φ g = 1) :
    Subgroup.center (μ ⋊[φ] P) = (inl : μ →* μ ⋊[φ] P).range := by
  have hker : IsOpen (φ.ker : Set P) := by
    have : (φ.ker : Set P) = Set.univ := Set.eq_univ_of_forall fun g => hφ1 g
    rw [this]
    exact isOpen_univ
  apply le_antisymm
  · intro x hx
    rw [mem_range_inl_iff hP hker]
    refine ⟨⊤, isOpen_univ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.1 hx y)
  · rintro _ ⟨m, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    ext <;> simp [hφ1, mul_comm]

end Envelope

/-- **[EtTh], Proposition 2.12(ii) from 2.12(i)**: for a subgroup `S ⊆ [Δ, Δ]` and an abelian
`μ` (acting trivially), the intersection of the commutator subgroup of `Δ[μ] = Δ × μ` with
`S[μ] = S × μ` is the image of `S` under the tautological section `x ↦ (x, 1)`. -/
theorem commutator_prod_inf {Δ μ : Type*} [Group Δ] [CommGroup μ] (S : Subgroup Δ)
    (hS : S ≤ commutator Δ) :
    commutator (Δ × μ) ⊓ S.prod ⊤ = S.map (MonoidHom.inl Δ μ) := by
  have hμ : ⁅(⊤ : Subgroup μ), ⊤⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 fun x _ =>
      Subgroup.mem_centralizer_iff.2 fun y _ => mul_comm y x
  rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, hμ]
  ext ⟨x, m⟩
  simp only [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_bot, Subgroup.mem_top,
    and_true, Subgroup.mem_map, MonoidHom.inl_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨-, rfl⟩, hx⟩
    exact ⟨x, hx, rfl, rfl⟩
  · rintro ⟨y, hy, rfl, rfl⟩
    exact ⟨⟨hS hy, rfl⟩, hy⟩

namespace ThetaGroup

variable {M : Type*} [AddCommGroup M] {l : ℤ}

/-- **[EtTh], Proposition 2.12(ii)** for the theta group: in `Δ^Θ[μ] = Δ^Θ × μ`, the
intersection `[Δ^Θ[μ], Δ^Θ[μ]] ∩ (l·Δ_Θ)[μ]` is the image of `l·Δ_Θ` under the tautological
section. -/
theorem commutator_envelope_inf (μ : Type*) [CommGroup μ] :
    commutator (ThetaGroup M l × μ) ⊓ (thetaKernel M l).prod ⊤ =
      (thetaKernel M l).map (MonoidHom.inl (ThetaGroup M l) μ) :=
  commutator_prod_inf _ (commutator_eq_theta (M := M) (l := l)).ge

end ThetaGroup

end Iut.EtaleTheta
