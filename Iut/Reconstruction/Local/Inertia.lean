/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Invariants
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Group-theoretic reconstruction of the inertia subgroup (roadmap P17, M1d)

[AbsAnab], Proposition 1.2.1 (ii) (used throughout IUT I–III, e.g. for the decomposition and
inertia groups of the prime-strips): the inertia subgroup `I_K ≤ G_K` of a finite extension
`K/ℚ_p` is determined by the topological group `G_K`. Here

`recInertia G = ⋂ {H ≤ G open | recF(H) = [G : H] · recF(G)}`

(`recF` the reconstructed residue degree of `Local/Invariants.lean`): an open subgroup
`H = Gal(Ω/L)` satisfies `f(L) = [L : K] f(K)` iff `L/K` is unramified, i.e. iff `H ⊇ I_K`, and
the closed subgroup `I_K = Gal(Ω/K^ur)` is the intersection of the open subgroups containing it.

## Main results

* `Iut.Reconstruction.fixingSubgroupContEquiv`: `Gal(Ω/K) ⊇ Gal(Ω/L) ≃ₜ* Gal(Ω/L)` (subspace
  topology versus Krull topology) for `L/K` finite;
* `Iut.Reconstruction.recF_fixingSubgroup`: `recF(Gal(Ω/L)) = f(L/ℚ_p)`;
* `Iut.Reconstruction.recInertia`, `Iut.Reconstruction.map_recInertia` (group-theoretic);
* `Iut.Reconstruction.recInertia_gal`: `recInertia (Gal(Ω/K)) = PadicField.absInertia p K Ω`;
* `Iut.Reconstruction.galEquiv_inertia`: every isomorphism of topological groups
  `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` maps `I_K` onto `I_{K'}`.
-/

open PadicField IntermediateField

namespace Iut.Reconstruction

section Transport

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- An isomorphism of groups restricts to the preimage of a subgroup. -/
def comapMulEquiv (ψ : G' ≃ₜ* G) (H : Subgroup G) :
    (H.comap ψ.toMulEquiv.toMonoidHom) ≃* H where
  toFun x := ⟨ψ x.1, x.2⟩
  invFun y := ⟨ψ.symm y.1, by
    change ψ (ψ.symm y.1) ∈ H
    rw [ψ.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (ψ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (ψ.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul ψ x.1 y.1)

/-- An isomorphism of topological groups restricts to the preimage of a subgroup. -/
def comapContEquiv (ψ : G' ≃ₜ* G) (H : Subgroup G) :
    (H.comap ψ.toMulEquiv.toMonoidHom) ≃ₜ* H :=
  { toMulEquiv := comapMulEquiv ψ H
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact ψ.continuous.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact ψ.symm.continuous.comp continuous_subtype_val }

/-- The open subgroups with `recF(H) = [G : H] · recF(G)`. -/
def UnrOpen (G : Type*) [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsOpen (H : Set G) ∧ recF H = H.index * recF G

theorem UnrOpen.comap (ψ : G' ≃ₜ* G) {H : Subgroup G} (hH : UnrOpen G H) :
    UnrOpen G' (H.comap ψ.toMulEquiv.toMonoidHom) := by
  refine ⟨hH.1.preimage ψ.continuous, ?_⟩
  have h1 : recF (H.comap ψ.toMulEquiv.toMonoidHom) = recF H := by
    simp only [recF, charCountFun_congr (comapContEquiv ψ H)]
  have h2 : recF G' = recF G := by simp only [recF, charCountFun_congr ψ]
  rw [h1, h2, Subgroup.index_comap_of_surjective _ ψ.surjective]
  exact hH.2

/-- **The reconstructed inertia subgroup** of a topological group. -/
noncomputable def recInertia (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  ⨅ (H : Subgroup G) (_ : UnrOpen G H), H

theorem mem_recInertia {x : G} : x ∈ recInertia G ↔ ∀ H, UnrOpen G H → x ∈ H := by
  simp [recInertia, Subgroup.mem_iInf]

/-- **The reconstructed inertia subgroup is group-theoretic.** -/
theorem comap_recInertia (ψ : G' ≃ₜ* G) :
    (recInertia G).comap ψ.toMulEquiv.toMonoidHom = recInertia G' := by
  ext x
  rw [Subgroup.mem_comap, mem_recInertia, mem_recInertia]
  constructor
  · intro h H' hH'
    have hH := hH'.comap ψ.symm
    have := h _ hH
    rw [Subgroup.mem_comap] at this
    change ψ.symm (ψ x) ∈ H' at this
    rwa [ψ.symm_apply_apply] at this
  · intro h H hH
    exact h _ (hH.comap ψ)

theorem map_recInertia (φ : G ≃ₜ* G') :
    (recInertia G).map φ.toMulEquiv.toMonoidHom = recInertia G' := by
  rw [← comap_recInertia φ.symm]
  exact Subgroup.map_equiv_eq_comap_symm' φ.toMulEquiv _

end Transport

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω]

omit [IsAlgClosed Ω] [IsGalois K Ω] in
theorem continuous_fixingSubgroupEquiv (L : IntermediateField K Ω) [FiniteDimensional K L] :
    Continuous (fixingSubgroupEquiv L) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff L Ω U).1 hU
  haveI : FiniteDimensional L E := hE
  set E' : IntermediateField K Ω := E.restrictScalars K
  haveI : FiniteDimensional K E' := by
    haveI : FiniteDimensional K E := Module.Finite.trans L E
    exact this
  have hopen : IsOpen ((E'.fixingSubgroup : Subgroup (Ω ≃ₐ[K] Ω)) : Set (Ω ≃ₐ[K] Ω)) :=
    E'.fixingSubgroup_isOpen
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((hopen.preimage continuous_subtype_val).mem_nhds (by simp [one_mem])) ?_
  intro σ hσ
  apply hEU
  intro x
  exact hσ ⟨x, x.2⟩

/-- `Gal(Ω/L) ⊆ Gal(Ω/K)` with the subspace topology is `Gal(Ω/L)` with its Krull topology. -/
noncomputable def fixingSubgroupContEquiv (L : IntermediateField K Ω) [FiniteDimensional K L] :
    L.fixingSubgroup ≃ₜ* (Ω ≃ₐ[L] Ω) :=
  haveI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  haveI : CompactSpace L.fixingSubgroup :=
    isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  { toMulEquiv := fixingSubgroupEquiv L
    continuous_toFun := continuous_fixingSubgroupEquiv L
    continuous_invFun :=
      ((continuous_fixingSubgroupEquiv L).homeoOfEquivCompactToT2
        (f := (fixingSubgroupEquiv L).toEquiv)).symm.continuous }

variable (p) in
/-- `recF(Gal(Ω/L)) = f(L/ℚ_p)` for `L/K` finite. -/
theorem recF_fixingSubgroup (L : IntermediateField K Ω) [FiniteDimensional K L] :
    recF L.fixingSubgroup = f p ℚ_[p] L := by
  haveI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  haveI : FiniteDimensional ℚ_[p] L := Module.Finite.trans K L
  rw [recF, charCountFun_congr (fixingSubgroupContEquiv L)]
  exact recF_gal p (K := L) (Ω := Ω)

variable (p) in
/-- The criterion: `Gal(Ω/L)` satisfies `recF(H) = [G : H] recF(G)` iff `L/K` is unramified. -/
theorem unrOpen_iff (L : IntermediateField K Ω) [FiniteDimensional K L] :
    UnrOpen (Ω ≃ₐ[K] Ω) L.fixingSubgroup ↔ IsUnramified p K L := by
  haveI : FiniteDimensional ℚ_[p] L := Module.Finite.trans K L
  rw [UnrOpen, recF_fixingSubgroup p L, recF_gal p, ← finrank_eq_fixingSubgroup_index L,
    isUnramified_iff_f_eq, ← f_mul_f (p := p) (K := ℚ_[p]) (E := K) (L := L)]
  have hf : 0 < f p ℚ_[p] K := f_pos
  constructor
  · rintro ⟨-, h⟩
    rw [mul_comm (Module.finrank K L)] at h
    exact Nat.eq_of_mul_eq_mul_left hf h
  · intro h
    refine ⟨L.fixingSubgroup_isOpen, ?_⟩
    rw [h, mul_comm]

variable [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p) in
/-- **The reconstructed inertia subgroup of `G_K` is the inertia subgroup.** (The instance
`Algebra.IsAlgebraic ℚ_[p] Ω`, needed to state `absInertia`, follows from the others,
`PadicField.isAlgebraic_of_tower`.) -/
theorem recInertia_gal : recInertia (Ω ≃ₐ[K] Ω) = absInertia p K Ω := by
  rw [absInertia_eq]
  ext σ
  rw [mem_recInertia]
  constructor
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨n, hn, hxn⟩ := (mem_maxUnramified_iff (p := p)).1 hx
    have hU := (unrOpen_iff p (unramifiedOfDegree p K Ω n)).2
      (isUnramified_unramifiedOfDegree (p := p) (K := K) (Ω := Ω) n)
    have := h _ hU
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 this x hxn
  · intro hσ H hH
    have hcl : IsClosed (H : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen H hH.1
    have hfix : (fixedField H).fixingSubgroup = H :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨H, hcl⟩
    haveI : FiniteDimensional K (fixedField H) :=
      (InfiniteGalois.isOpen_iff_finite (fixedField H)).1 (by rw [hfix]; exact hH.1)
    rw [← hfix] at hH ⊢
    have hun := (unrOpen_iff p (fixedField H)).1 hH
    exact fixingSubgroup_antitone hun.le_maxUnramified hσ

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- **[AbsAnab], Proposition 1.2.1 (ii)** (invariance form): every isomorphism of topological
groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` maps the inertia subgroup onto the inertia subgroup. -/
theorem galEquiv_inertia (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) :
    (absInertia p K Ω).map φ.toMulEquiv.toMonoidHom = absInertia p' K' Ω' := by
  rw [← recInertia_gal p, ← recInertia_gal p', map_recInertia]

end Galois

end Iut.Reconstruction
