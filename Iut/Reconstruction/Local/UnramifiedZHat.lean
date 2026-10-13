/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Valuation

/-!
# The unramified quotient `G_K / I_K ≅ Ẑ` is group-theoretic (roadmap P17, M1h)

[AbsAnab], Proposition 1.2.1 (iv); [AbsTopIII], Proposition 5.8 (i): the quotient of `G_K` by the
inertia subgroup, together with its isomorphism with `Ẑ` sending the Frobenius to `1`, is
determined by the topological group `G_K`.

For a topological group `G`, the **reconstructed unramified quotient** is
`recUnr G = G ⧸ recInertia G` (with the quotient topology; `recInertia G` is normal,
`recInertia_normal`, since conjugations are automorphisms of topological groups). A
**`Ẑ`-structure** on it is an isomorphism of topological groups `e : recUnr G ≃ₜ* Ẑ` sending
the class of every lift of the Frobenius (`IsFrobLift`) to `1` (`IsUnrZHat G e`).

* `IsUnrZHat.eq`: if `G` has a Frobenius lift, there is at most one `Ẑ`-structure (`ℤ` is dense
  in `Ẑ`, `zhat_hom_ext`);
* `IsUnrZHat.map`: `Ẑ`-structures are transported along isomorphisms of topological groups
  (`unrEquiv ψ : recUnr G ≃ₜ* recUnr G'`);
* **`unrZHat p K Ω : recUnr G_K ≃ₜ* Ẑ`**, `σ ↦ σ|_{K^ur}` followed by
  `PadicField.galMaxUnramifiedEquiv : Gal(K^ur/K) ≃ₜ* Ẑ` of `local-class-field-theory`, is a
  `Ẑ`-structure (`isUnrZHat_gal`);
* **`galEquiv_unrZHat`**: every isomorphism of topological groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')`
  (`K/ℚ_p`, `K'/ℚ_{p'}`) induces an isomorphism of the unramified quotients compatible with the
  identifications with `Ẑ`. This strengthens `galEquiv_arithFrob` (the Frobenius classes
  correspond) from the Frobenius to the whole profinite group `G_K / I_K`.
-/

open PadicField IntermediateField Brauer

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- Conjugation by `g`, as an automorphism of topological groups. -/
def conjContEquiv (g : G) : G ≃ₜ* G :=
  { MulAut.conj g with
    continuous_toFun := by
      change Continuous fun h => g * h * g⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun h => g⁻¹ * h * g
      fun_prop }

/-- The reconstructed inertia subgroup is normal. -/
instance recInertia_normal : (recInertia G).Normal where
  conj_mem n hn g := by
    rw [← map_recInertia (conjContEquiv g)]
    exact ⟨n, hn, rfl⟩

variable (G) in
/-- **The reconstructed unramified quotient** `G ⧸ recInertia G` (`G_K / I_K` for `G = G_K`). -/
abbrev recUnr := G ⧸ recInertia G

/-- The isomorphism of reconstructed unramified quotients induced by `ψ : G ≃ₜ* G'`. -/
noncomputable def unrEquiv (ψ : G ≃ₜ* G') : recUnr G ≃ₜ* recUnr G' :=
  { toMulEquiv := QuotientGroup.congr _ _ ψ.toMulEquiv (map_recInertia ψ)
    continuous_toFun := by
      rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      exact continuous_quot_mk.comp ψ.continuous
    continuous_invFun := by
      rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      exact continuous_quot_mk.comp ψ.symm.continuous }

theorem unrEquiv_mk (ψ : G ≃ₜ* G') (g : G) :
    unrEquiv ψ (QuotientGroup.mk g) = QuotientGroup.mk (ψ g) := rfl

theorem unrEquiv_symm_mk (ψ : G ≃ₜ* G') (g : G') :
    (unrEquiv ψ).symm (QuotientGroup.mk g) = QuotientGroup.mk (ψ.symm g) := rfl

variable (G) in
/-- A **`Ẑ`-structure** on the reconstructed unramified quotient: an isomorphism of
topological groups with `Ẑ` sending the class of every lift of the Frobenius to `1`. -/
def IsUnrZHat (e : recUnr G ≃ₜ* Multiplicative ZHat) : Prop :=
  ∀ φ : G, IsFrobLift G φ → e (QuotientGroup.mk φ) = Multiplicative.ofAdd (intToZHat 1)

/-- **Uniqueness of the `Ẑ`-structure** (when a Frobenius lift exists). -/
theorem IsUnrZHat.eq (hG : ∃ φ : G, IsFrobLift G φ) {e e' : recUnr G ≃ₜ* Multiplicative ZHat}
    (he : IsUnrZHat G e) (he' : IsUnrZHat G e') : e = e' := by
  obtain ⟨φ, hφ⟩ := hG
  have h1 : e.symm (Multiplicative.ofAdd (intToZHat 1)) = QuotientGroup.mk φ := by
    rw [ContinuousMulEquiv.symm_apply_eq, he φ hφ]
  have h : (e'.toMulEquiv.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom) = MonoidHom.id _ :=
    zhat_hom_ext (e'.continuous.comp e.symm.continuous) continuous_id (by
      change e' (e.symm _) = _
      rw [h1, he' φ hφ]
      rfl)
  refine DFunLike.ext _ _ fun x => ?_
  have := DFunLike.congr_fun h (e x)
  change e' (e.symm (e x)) = e x at this
  rw [ContinuousMulEquiv.symm_apply_apply] at this
  exact this.symm

/-- **`Ẑ`-structures are group-theoretic**: they are transported along isomorphisms of
topological groups. -/
theorem IsUnrZHat.map (ψ : G ≃ₜ* G') {e : recUnr G ≃ₜ* Multiplicative ZHat}
    (he : IsUnrZHat G e) : IsUnrZHat G' ((unrEquiv ψ).symm.trans e) := by
  intro φ hφ
  change e ((unrEquiv ψ).symm (QuotientGroup.mk φ)) = _
  rw [unrEquiv_symm_mk]
  exact he _ ((isFrobLift_map_iff ψ.symm).2 hφ)

/-- `Ẑ`-structures are compatible with every isomorphism of topological groups. -/
theorem IsUnrZHat.apply_unrEquiv (hG' : ∃ φ : G', IsFrobLift G' φ) (ψ : G ≃ₜ* G')
    {e : recUnr G ≃ₜ* Multiplicative ZHat} {e' : recUnr G' ≃ₜ* Multiplicative ZHat}
    (he : IsUnrZHat G e) (he' : IsUnrZHat G' e') (x : recUnr G) : e' (unrEquiv ψ x) = e x := by
  rw [← IsUnrZHat.eq hG' (he.map ψ) he']
  change e ((unrEquiv ψ).symm (unrEquiv ψ x)) = e x
  rw [ContinuousMulEquiv.symm_apply_apply]

end GroupTheoretic

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p K Ω) in
/-- `σ ↦ (σ|_{K^ur} ∈ Gal(K^ur/K) ≅ Ẑ)`. -/
noncomputable def unrZHatHom : (Ω ≃ₐ[K] Ω) →* Multiplicative ZHat :=
  (galMaxUnramifiedEquiv p K Ω).toMulEquiv.toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (maxUnramified p K Ω))

theorem continuous_unrZHatHom : Continuous (unrZHatHom p K Ω) :=
  (galMaxUnramifiedEquiv p K Ω).continuous.comp
    (InfiniteGalois.restrictNormalHom_continuous (maxUnramified p K Ω))

theorem unrZHatHom_surjective : Function.Surjective (unrZHatHom p K Ω) :=
  (galMaxUnramifiedEquiv p K Ω).surjective.comp (AlgEquiv.restrictNormalHom_surjective Ω)

theorem ker_unrZHatHom : (unrZHatHom p K Ω).ker = recInertia (Ω ≃ₐ[K] Ω) := by
  ext σ
  rw [recInertia_gal p, ← ker_restrictNormalHom_maxUnramified, MonoidHom.mem_ker,
    MonoidHom.mem_ker]
  change galMaxUnramifiedEquiv p K Ω (AlgEquiv.restrictNormalHom _ σ) = 1 ↔ _
  exact EmbeddingLike.map_eq_one_iff

variable (p K Ω) in
/-- **`G_K / I_K ≅ Ẑ`** as topological groups, on the reconstructed unramified quotient:
`σ ↦ σ|_{K^ur}` followed by `Gal(K^ur/K) ≃ₜ* Ẑ`. -/
noncomputable def unrZHat : recUnr (Ω ≃ₐ[K] Ω) ≃ₜ* Multiplicative ZHat :=
  let e : recUnr (Ω ≃ₐ[K] Ω) ≃* Multiplicative ZHat :=
    QuotientGroup.liftEquiv _ (unrZHatHom_surjective (p := p) (K := K) (Ω := Ω))
      (ker_unrZHatHom (p := p)).symm
  have hc : Continuous e := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    exact continuous_unrZHatHom (p := p)
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem unrZHat_mk (σ : Ω ≃ₐ[K] Ω) :
    unrZHat p K Ω (QuotientGroup.mk σ) =
      galMaxUnramifiedEquiv p K Ω (AlgEquiv.restrictNormalHom (maxUnramified p K Ω) σ) :=
  rfl

/-- A lift of the arithmetic Frobenius restricts to the Frobenius of `K^ur`. -/
theorem restrict_eq_frobUr {σ : Ω ≃ₐ[K] Ω}
    (hσ : (QuotientGroup.mk σ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω) :
    AlgEquiv.restrictNormalHom (maxUnramified p K Ω) σ = frobUr p K Ω := by
  rw [← unramifiedQuotientEquiv_arithFrob, ← hσ]
  rfl

variable (p) in
include p in
/-- `G_K` has lifts of the Frobenius. -/
theorem exists_isFrobLift_gal : ∃ φ : Ω ≃ₐ[K] Ω, IsFrobLift (Ω ≃ₐ[K] Ω) φ := by
  obtain ⟨φ, hφ⟩ := QuotientGroup.mk_surjective (arithFrob p K Ω)
  exact ⟨φ, (isFrobLift_gal_iff p φ).2 hφ⟩

/-- **`unrZHat` is a `Ẑ`-structure**: Frobenius lifts are sent to `1`. -/
theorem isUnrZHat_gal : IsUnrZHat (Ω ≃ₐ[K] Ω) (unrZHat p K Ω) := by
  intro φ hφ
  rw [unrZHat_mk, restrict_eq_frobUr ((isFrobLift_gal_iff p φ).1 hφ),
    galMaxUnramifiedEquiv_frobUr]

/-- On the reconstructed Weil group, `unrZHat` is the exponent of the Frobenius
(`σ ≡ Frob^k mod I_K`). -/
theorem unrZHat_mk_of_isFrobLift {φ τ : Ω ≃ₐ[K] Ω} (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ)
    (hτ : τ ∈ recInertia (Ω ≃ₐ[K] Ω)) (k : ℤ) :
    unrZHat p K Ω (QuotientGroup.mk (φ ^ k * τ)) = Multiplicative.ofAdd (intToZHat k) := by
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff τ).2 hτ, mul_one, QuotientGroup.mk_zpow,
    map_zpow, isUnrZHat_gal φ hφ]
  exact (ofAdd_intToZHat_eq_zpow k).symm

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- **The `Ẑ`-structure of the unramified quotient is group-theoretic**: for every isomorphism
of topological groups `ψ : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')`, the induced isomorphism
`G_K / I_K ≃ₜ* G_{K'} / I_{K'}` becomes the identity of `Ẑ`. -/
theorem galEquiv_unrZHat (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (x : recUnr (Ω ≃ₐ[K] Ω)) :
    unrZHat p' K' Ω' (unrEquiv ψ x) = unrZHat p K Ω x :=
  IsUnrZHat.apply_unrEquiv (exists_isFrobLift_gal p') ψ (isUnrZHat_gal (p := p))
    (isUnrZHat_gal (p := p')) x

/-- The restrictions to the maximal unramified extensions correspond under
`Gal(K^ur/K) ≃ₜ* Ẑ ≃ₜ* Gal(K'^ur/K')`. -/
theorem galEquiv_restrict_maxUnramified (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (σ : Ω ≃ₐ[K] Ω) :
    galMaxUnramifiedEquiv p' K' Ω' (AlgEquiv.restrictNormalHom (maxUnramified p' K' Ω') (ψ σ)) =
      galMaxUnramifiedEquiv p K Ω (AlgEquiv.restrictNormalHom (maxUnramified p K Ω) σ) :=
  galEquiv_unrZHat ψ (QuotientGroup.mk σ)

end Galois

end Iut.Reconstruction
