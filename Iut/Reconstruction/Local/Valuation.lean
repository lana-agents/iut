/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Abelianization
import Iut.Reconstruction.Local.ZHat

/-!
# The valuation is group-theoretic (roadmap P17, M1g)

[AbsTopIII], Corollary 1.10 (i) (b) and Proposition 5.8 (i); [AbsAnab], Proposition 1.2.1 (iv):
the surjection `G_K^ab ↠ G_K/I_K ≅ ℤ^∧` determined by the Frobenius element is group-theoretic,
and on the image of `Kˣ` it is the valuation. Here: an element `x ∈ G^ab` has
**reconstructed valuation `k ∈ ℤ`** (`HasRecVal G x k`) if `x` is the image of `φ^k τ` for a
lift `φ` of the Frobenius (`IsFrobLift`) and `τ ∈ recInertia G`.

* `HasRecVal.map`: this is group-theoretic;
* `zpow_arithFrob_eq_one_iff`: the Frobenius has infinite order in `G_K/I_K`;
* **`hasRecVal_gal_iff`**: for `G = G_K`, `HasRecVal G (x ∈ Kˣ) k ↔ k = v(x)`;
* **`v_galEquiv_multEquiv`**: the isomorphism `Kˣ ≃* K'ˣ` induced by an isomorphism of
  topological groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` (`galEquiv_multEquiv`) preserves the normalised
  valuations.
-/

open PadicField IntermediateField

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- `x ∈ G^ab` has reconstructed valuation `k`: it is the image of `φ^k τ` for a lift `φ` of the
Frobenius and `τ` in the reconstructed inertia subgroup. -/
def HasRecVal (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : TopologicalAbelianization G) (k : ℤ) : Prop :=
  ∃ φ τ : G, IsFrobLift G φ ∧ τ ∈ recInertia G ∧ x = QuotientGroup.mk (φ ^ k * τ)

/-- **The reconstructed valuation is group-theoretic.** -/
theorem HasRecVal.map (ψ : G ≃ₜ* G') {x : TopologicalAbelianization G} {k : ℤ}
    (h : HasRecVal G x k) : HasRecVal G' (abEquiv ψ x) k := by
  obtain ⟨φ, τ, hφ, hτ, rfl⟩ := h
  refine ⟨ψ φ, ψ τ, hφ.map ψ, (mem_recInertia_iff_map ψ).2 hτ, ?_⟩
  change QuotientGroup.mk (ψ (φ ^ k * τ)) = _
  rw [map_mul, map_zpow]

theorem hasRecVal_map_iff (ψ : G ≃ₜ* G') {x : TopologicalAbelianization G} {k : ℤ} :
    HasRecVal G' (abEquiv ψ x) k ↔ HasRecVal G x k := by
  refine ⟨fun h => ?_, fun h => h.map ψ⟩
  have := h.map ψ.symm
  have e : abEquiv ψ.symm (abEquiv ψ x) = x := by
    induction x using QuotientGroup.induction_on with
    | H g =>
      change QuotientGroup.mk (ψ.symm (ψ g)) = _
      rw [ψ.symm_apply_apply]
  rwa [e] at this

end GroupTheoretic

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- **The Frobenius has infinite order in `G_K / I_K`.** -/
theorem zpow_arithFrob_eq_one_iff (n : ℤ) : arithFrob p K Ω ^ n = 1 ↔ n = 0 := by
  rw [← frobUr_zpow_eq_one_iff (p := p) (K := K) (Ω := Ω), ← unramifiedQuotientEquiv_arithFrob,
    ← map_zpow]
  exact ((unramifiedQuotientEquiv p K Ω).map_eq_one_iff).symm

/-- Restriction to `K^ab` determines the class modulo inertia. -/
theorem mk_eq_of_restrict_eq {σ τ : Ω ≃ₐ[K] Ω}
    (h : AlgEquiv.restrictNormalHom (maxAbelian K Ω) σ =
      AlgEquiv.restrictNormalHom (maxAbelian K Ω) τ) :
    (QuotientGroup.mk σ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = QuotientGroup.mk τ := by
  rw [QuotientGroup.eq, absInertia_eq, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have := congrArg (fun ρ => ((ρ ⟨y, maxUnramified_le_maxAbelian hy⟩ : maxAbelian K Ω) : Ω)) h
  simp only [AlgEquiv.restrictNormalHom_apply] at this
  rw [AlgEquiv.mul_apply, ← this, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

/-- The decomposition `artin x = (φ^{v(x)} τ)|_{K^ab}`. -/
theorem exists_restrict_eq_artin (x : Kˣ) :
    ∃ φ τ : Ω ≃ₐ[K] Ω, QuotientGroup.mk φ = arithFrob p K Ω ∧ τ ∈ absInertia p K Ω ∧
      AlgEquiv.restrictNormalHom (maxAbelian K Ω) (φ ^ v p (x : K) * τ) = artin p K Ω x := by
  obtain ⟨π, φ, hπ, hφ, hφF⟩ := exists_frob_lift_artin (p := p) (K := K) (Ω := Ω)
  set k := v p (x : K)
  set u : Kˣ := x * π ^ (-k)
  have hu : v p (u : K) = 0 := by
    simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val]
    rw [v_mul x.ne_zero (zpow_ne_zero _ π.ne_zero), v_zpow π.ne_zero, hπ]
    ring
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω (artin p K Ω u)
  have hτI : τ ∈ absInertia p K Ω := mem_absInertia_of_artin u hu τ fun y => by
    rw [← hτ, AlgEquiv.restrictNormalHom_apply]
  refine ⟨φ, τ, hφF, hτI, ?_⟩
  rw [map_mul, map_zpow, hφ, hτ, ← map_zpow, ← map_mul]
  congr 1
  simp only [u]
  rw [← mul_assoc, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

/-- **The reconstructed valuation of `x ∈ Kˣ` is `v(x)`.** -/
theorem hasRecVal_gal_iff (x : Kˣ) (k : ℤ) :
    HasRecVal (Ω ≃ₐ[K] Ω) (multAbEquiv p K Ω x) k ↔ k = v p (x : K) := by
  obtain ⟨φ, τ, hφF, hτI, hres⟩ := exists_restrict_eq_artin (p := p) (Ω := Ω) x
  constructor
  · rintro ⟨φ', τ', hφ', hτ', he⟩
    have hφ'F := (isFrobLift_gal_iff p φ').1 hφ'
    rw [recInertia_gal p] at hτ'
    have h1 : AlgEquiv.restrictNormalHom (maxAbelian K Ω) (φ' ^ k * τ') =
        AlgEquiv.restrictNormalHom (maxAbelian K Ω) (φ ^ v p (x : K) * τ) := by
      rw [hres, ← galAbEquiv_multAbEquiv (p := p), he]
      rfl
    have h2 := mk_eq_of_restrict_eq (p := p) h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff τ').2 hτ',
      (QuotientGroup.eq_one_iff τ).2 hτI, mul_one, mul_one, QuotientGroup.mk_zpow,
      QuotientGroup.mk_zpow, hφ'F, hφF] at h2
    have h3 : arithFrob p K Ω ^ (k - v p (x : K)) = 1 := by
      rw [zpow_sub, h2, mul_inv_cancel]
    exact sub_eq_zero.1 ((zpow_arithFrob_eq_one_iff (p := p) (K := K) (Ω := Ω) _).1 h3)
  · rintro rfl
    refine ⟨φ, τ, (isFrobLift_gal_iff p φ).2 hφF, by rw [recInertia_gal p]; exact hτI, ?_⟩
    apply (galAbEquiv p K Ω).injective
    rw [galAbEquiv_multAbEquiv, galAbEquiv_mk, hres]

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

/-- **The valuation is group-theoretic**: the isomorphism `Kˣ ≃* K'ˣ` induced by
`Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` preserves the normalised valuations. -/
theorem v_galEquiv_multEquiv (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (x : Kˣ) :
    v p' (galEquiv_multEquiv p p' φ x : K') = v p (x : K) := by
  have h := (hasRecVal_gal_iff (p := p) (Ω := Ω) x (v p (x : K))).2 rfl
  have h' := h.map φ
  rw [← multAbEquiv_galEquiv_multEquiv (p := p) (p' := p')] at h'
  exact ((hasRecVal_gal_iff (p := p') (Ω := Ω') _ _).1 h').symm

end Galois

end Iut.Reconstruction
