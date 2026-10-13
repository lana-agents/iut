/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.UnramifiedZHat
import LocalClassFieldTheory.Reciprocity.GaloisStructure

/-!
# `G_K^ab ≅ 𝒪_Kˣ × Ẑ`, group-theoretically (roadmap P17, M1i)

[AbsAnab], Proposition 1.2.1 (iv)–(v); [AbsTopIII], Proposition 5.8 (i): local class field theory
identifies `G_K^ab` with the profinite completion of `Kˣ`, i.e. (after the choice of a
uniformiser `π`) with `𝒪_Kˣ × Ẑ`; the inertia subgroup is `𝒪_Kˣ × 1` and a Frobenius lift has
`Ẑ`-component `1`. We show that this decomposition is determined by the topological group `G_K`.

**Group-theoretic construction.** For a topological group `G` whose abelianisation `G^ab` is
profinite and an element `φ ∈ G`, let

`recAbHom G φ : abUnits G × Ẑ → G^ab`,  `(u, a) ↦ u · [φ]^a`,

(`abUnits G` the image of `recInertia G`, `[φ]^a = Brauer.zhatPow [φ] a`). It is natural:
every `ψ : G ≃ₜ* G'` satisfies `ψ^ab (recAbHom G φ (u, a)) = recAbHom G' (ψ φ) (ψ u, a)`
(`abContEquiv_recAbHom`, with `abContEquiv ψ : G^ab ≃ₜ* G'^ab` and
`abUnitsContEquiv ψ : abUnits G ≃ₜ* abUnits G'`).

**`G = G_K`.**
* `abZHatEquiv p K Ω hπ : G_K^ab ≃ₜ* 𝒪_Kˣ × Ẑ` is `G_K^ab ≅ Gal(K^ab/K)` (`galAbEquiv`)
  followed by `PadicField.galAbEquiv` of `local-class-field-theory`; on `Kˣ` it is
  `x ↦ (x π^{-v(x)}, v(x))` (`abZHatEquiv_multAbEquiv`), the reconstructed units `abUnits G_K`
  are `𝒪ˣ × 1` (`abZHatEquiv_snd_eq_one_iff`), the `Ẑ`-component is the `Ẑ`-structure of the
  unramified quotient (`abZHatEquiv_snd_mk`), so Frobenius lifts have `Ẑ`-component `1` and
  elements of reconstructed valuation `k` have `Ẑ`-component `k` (`abZHatEquiv_snd_of_hasRecVal`);
* `unitsAbContEquiv : 𝒪_Kˣ ≃ₜ* abUnits G_K` (topological form of `unitsAbEquiv`);
* the uniformisers are exactly the images of the Frobenius lifts
  (`exists_uniformizer_of_isFrobLift`, `exists_isFrobLift_of_uniformizer`), and for `[φ] = π`
  the group-theoretic `recAbHom G_K φ` is `(unitsAbContEquiv × id)` followed by
  `abZHatEquiv hπ⁻¹` (`abZHatEquiv_recAbHom`). Hence
  **`recAbEquiv φ hφ : abUnits G_K × Ẑ ≃ₜ* G_K^ab`** for every Frobenius lift `φ`;
* **`abZHatEquiv_abContEquiv`**: for `ψ : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` and a uniformiser `π` of `K`,
  `π' = ψ(π)` (the image under `galEquiv_multEquiv`) is a uniformiser of `K'`, and under
  `G_K^ab ≅ 𝒪_Kˣ × Ẑ`, `G_{K'}^ab ≅ 𝒪_{K'}ˣ × Ẑ` the isomorphism `ψ^ab` becomes
  `(u, a) ↦ (ψ(u), a)` — the isomorphism `𝒪_Kˣ ≃ₜ* 𝒪_{K'}ˣ` induced by `ψ` (`galEquiv_unitsEquiv`,
  the restriction of `galEquiv_multEquiv`, which is in particular a **homeomorphism**) times the
  identity of `Ẑ`.

The `TotallyDisconnectedSpace` instance on `G_K^ab`, needed to form `Brauer.zhatPow` there, is
taken as an instance argument where it is needed; it holds (`totallyDisconnectedSpace_abGal`),
but cannot be registered as a global instance since its proof depends on the prime `p`.
-/

open PadicField IntermediateField Brauer

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

/-! ### Group-theoretic part -/

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- The isomorphism of topological abelianisations induced by `ψ : G ≃ₜ* G'`. -/
noncomputable def abContEquiv (ψ : G ≃ₜ* G') :
    TopologicalAbelianization G ≃ₜ* TopologicalAbelianization G' :=
  { toMulEquiv := abEquiv ψ
    continuous_toFun := by
      rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      exact continuous_quot_mk.comp ψ.continuous
    continuous_invFun := by
      rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      exact continuous_quot_mk.comp ψ.symm.continuous }

theorem abContEquiv_apply (ψ : G ≃ₜ* G') (x : TopologicalAbelianization G) :
    abContEquiv ψ x = abEquiv ψ x := rfl

theorem abContEquiv_mk (ψ : G ≃ₜ* G') (g : G) :
    abContEquiv ψ (QuotientGroup.mk g) = QuotientGroup.mk (ψ g) := rfl

theorem abEquiv_mem_abUnits_iff (ψ : G ≃ₜ* G') (x : TopologicalAbelianization G) :
    abEquiv ψ x ∈ abUnits G' ↔ x ∈ abUnits G := by
  rw [← map_abUnits ψ]
  exact ⟨fun ⟨y, hy, hxy⟩ => by rwa [(abEquiv ψ).injective hxy] at hy,
    fun h => Subgroup.mem_map_of_mem _ h⟩

theorem abEquiv_symm_mem_abUnits_iff (ψ : G ≃ₜ* G') (x : TopologicalAbelianization G') :
    (abEquiv ψ).symm x ∈ abUnits G ↔ x ∈ abUnits G' := by
  rw [← abEquiv_mem_abUnits_iff ψ, MulEquiv.apply_symm_apply]

/-- The isomorphism of the images of the reconstructed inertia subgroups induced by
`ψ : G ≃ₜ* G'` (with the subspace topologies). -/
noncomputable def abUnitsContEquiv (ψ : G ≃ₜ* G') : abUnits G ≃ₜ* abUnits G' where
  toFun u := ⟨abEquiv ψ (u : TopologicalAbelianization G), (abEquiv_mem_abUnits_iff ψ _).2 u.2⟩
  invFun u := ⟨(abEquiv ψ).symm (u : TopologicalAbelianization G'),
    (abEquiv_symm_mem_abUnits_iff ψ _).2 u.2⟩
  left_inv u := Subtype.ext ((abEquiv ψ).symm_apply_apply (u : TopologicalAbelianization G))
  right_inv u := Subtype.ext ((abEquiv ψ).apply_symm_apply (u : TopologicalAbelianization G'))
  map_mul' u v := Subtype.ext (map_mul (abEquiv ψ) (u : TopologicalAbelianization G) v)
  continuous_toFun := ((abContEquiv ψ).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((abContEquiv ψ).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem coe_abUnitsContEquiv (ψ : G ≃ₜ* G') (u : abUnits G) :
    (abUnitsContEquiv ψ u : TopologicalAbelianization G') =
      abEquiv ψ (u : TopologicalAbelianization G) := rfl

variable [CompactSpace (TopologicalAbelianization G)]
  [TotallyDisconnectedSpace (TopologicalAbelianization G)]
  [CompactSpace (TopologicalAbelianization G')]
  [TotallyDisconnectedSpace (TopologicalAbelianization G')]

variable (G) in
/-- **The group-theoretic decomposition map** `abUnits G × Ẑ → G^ab`, `(u, a) ↦ u · [φ]^a`. -/
noncomputable def recAbHom (φ : G) :
    abUnits G × Multiplicative ZHat →* TopologicalAbelianization G :=
  (abUnits G).subtype.coprod
    (zhatPow (QuotientGroup.mk φ : TopologicalAbelianization G)).toMonoidHom

theorem recAbHom_apply (φ : G) (x : abUnits G × Multiplicative ZHat) :
    recAbHom G φ x = (x.1 : TopologicalAbelianization G) * zhatPow (QuotientGroup.mk φ) x.2 := rfl

theorem continuous_recAbHom (φ : G) : Continuous (recAbHom G φ) :=
  (continuous_subtype_val.comp continuous_fst).mul ((zhatPow _).continuous.comp continuous_snd)

/-- Continuous homomorphisms commute with `a ↦ g ^ a`. -/
theorem map_zhatPow {H H' : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] [Group H'] [TopologicalSpace H']
    [IsTopologicalGroup H'] [CompactSpace H'] [TotallyDisconnectedSpace H'] (f : H →ₜ* H')
    (g : H) (a : Multiplicative ZHat) : f (zhatPow g a) = zhatPow (f g) a := by
  have h := eq_zhatPow (f g) (f.comp (zhatPow g)) (by
    change f (zhatPow g _) = f g
    rw [zhatPow_one])
  exact DFunLike.congr_fun h a

/-- **The decomposition map is group-theoretic**: `ψ^ab (u · [φ]^a) = ψ(u) · [ψ φ]^a`. -/
theorem abContEquiv_recAbHom (ψ : G ≃ₜ* G') (φ : G) (x : abUnits G × Multiplicative ZHat) :
    abContEquiv ψ (recAbHom G φ x) = recAbHom G' (ψ φ) (abUnitsContEquiv ψ x.1, x.2) := by
  rw [recAbHom_apply, recAbHom_apply, map_mul]
  congr 1
  exact map_zhatPow ⟨(abContEquiv ψ).toMulEquiv.toMonoidHom, (abContEquiv ψ).continuous⟩ _ x.2

end GroupTheoretic

/-! ### `G = G_K` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

variable (p K Ω) in
include p in
theorem t2Space_abGal : T2Space (TopologicalAbelianization (Ω ≃ₐ[K] Ω)) := by
  haveI := isAlgebraic_tower_top p K Ω
  haveI : Algebra.IsIntegral K (maxAbelian K Ω) := inferInstance
  haveI : T2Space (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) := krullTopology_t2
  exact (galAbEquiv p K Ω).toHomeomorph.symm.t2Space

variable (p K Ω) in
include p in
/-- `G_K^ab` is totally disconnected (it is `Gal(K^ab/K)`). -/
theorem totallyDisconnectedSpace_abGal :
    TotallyDisconnectedSpace (TopologicalAbelianization (Ω ≃ₐ[K] Ω)) := by
  haveI := isAlgebraic_tower_top p K Ω
  haveI : Algebra.IsIntegral K (maxAbelian K Ω) := inferInstance
  exact (galAbEquiv p K Ω).toHomeomorph.symm.totallyDisconnectedSpace

variable (p K Ω) in
/-- **`G_K^ab ≅ 𝒪_Kˣ × Ẑ`** as topological groups, for a uniformiser `π`: `G_K^ab ≅ Gal(K^ab/K)`
followed by `PadicField.galAbEquiv`. -/
noncomputable def abZHatEquiv {π : Kˣ} (hπ : v p (π : K) = 1) :
    TopologicalAbelianization (Ω ≃ₐ[K] Ω) ≃ₜ* unitGroup p K × Multiplicative ZHat :=
  (galAbEquiv p K Ω).trans (_root_.PadicField.galAbEquiv p K Ω hπ)

theorem abZHatEquiv_apply {π : Kˣ} (hπ : v p (π : K) = 1)
    (x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    abZHatEquiv p K Ω hπ x = _root_.PadicField.galAbEquiv p K Ω hπ (galAbEquiv p K Ω x) := rfl

/-- On `Kˣ`: `x ↦ (x π^{-v(x)}, v(x))`. -/
theorem abZHatEquiv_multAbEquiv {π : Kˣ} (hπ : v p (π : K) = 1) (x : Kˣ) :
    abZHatEquiv p K Ω hπ (multAbEquiv p K Ω x) =
      (unitComponent p π hπ x, Multiplicative.ofAdd (intToZHat (v p (x : K)))) := by
  rw [abZHatEquiv_apply, galAbEquiv_multAbEquiv, galAbEquiv_artin']

/-- On `𝒪_Kˣ`: `u ↦ (u, 0)`. -/
theorem abZHatEquiv_unitsAbEquiv {π : Kˣ} (hπ : v p (π : K) = 1) (u : unitGroup p K) :
    abZHatEquiv p K Ω hπ (unitsAbEquiv p K Ω u) = (u, 1) := by
  rw [abZHatEquiv_apply, galAbEquiv_unitsAbEquiv, galAbEquiv_artin_unit]

/-- The uniformiser corresponds to `(1, 1)`. -/
theorem abZHatEquiv_multAbEquiv_uniformizer {π : Kˣ} (hπ : v p (π : K) = 1) :
    abZHatEquiv p K Ω hπ (multAbEquiv p K Ω π) = (1, Multiplicative.ofAdd (intToZHat 1)) := by
  rw [abZHatEquiv_apply, galAbEquiv_multAbEquiv, galAbEquiv_artin_uniformizer]

/-- **Inertia**: the reconstructed units `abUnits G_K` are `𝒪ˣ × 1`. -/
theorem abZHatEquiv_snd_eq_one_iff {π : Kˣ} (hπ : v p (π : K) = 1)
    (x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    (abZHatEquiv p K Ω hπ x).2 = 1 ↔ x ∈ abUnits (Ω ≃ₐ[K] Ω) := by
  rw [abZHatEquiv_apply, galAbEquiv_snd_eq_one_iff, ← map_abUnits_gal (p := p)]
  exact ⟨fun ⟨y, hy, hxy⟩ => by rwa [(galAbEquiv p K Ω).injective hxy] at hy,
    fun h => Subgroup.mem_map_of_mem _ h⟩

/-- **The `Ẑ`-component is the `Ẑ`-structure of the unramified quotient.** -/
theorem abZHatEquiv_snd_mk {π : Kˣ} (hπ : v p (π : K) = 1) (σ : Ω ≃ₐ[K] Ω) :
    (abZHatEquiv p K Ω hπ (QuotientGroup.mk σ)).2 = unrZHat p K Ω (QuotientGroup.mk σ) := by
  rw [abZHatEquiv_apply, galAbEquiv_snd, unrZHat_mk, galAbEquiv_mk]
  congr 1
  ext y
  rw [resUr_apply, AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]

/-- **Frobenius**: a lift of the Frobenius has `Ẑ`-component `1`. -/
theorem abZHatEquiv_snd_of_isFrobLift {π : Kˣ} (hπ : v p (π : K) = 1) {φ : Ω ≃ₐ[K] Ω}
    (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ) :
    (abZHatEquiv p K Ω hπ (QuotientGroup.mk φ)).2 = Multiplicative.ofAdd (intToZHat 1) := by
  rw [abZHatEquiv_snd_mk, isUnrZHat_gal φ hφ]

/-- An element of reconstructed valuation `k` has `Ẑ`-component `k`. -/
theorem abZHatEquiv_snd_of_hasRecVal {π : Kˣ} (hπ : v p (π : K) = 1)
    {x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)} {k : ℤ} (h : HasRecVal (Ω ≃ₐ[K] Ω) x k) :
    (abZHatEquiv p K Ω hπ x).2 = Multiplicative.ofAdd (intToZHat k) := by
  obtain ⟨φ, τ, hφ, hτ, rfl⟩ := h
  rw [abZHatEquiv_snd_mk, unrZHat_mk_of_isFrobLift hφ hτ]

variable (p K Ω) in
/-- **`𝒪_Kˣ ≅ abUnits G_K`** as topological groups (the Artin map). -/
noncomputable def unitsAbContEquiv : unitGroup p K ≃ₜ* abUnits (Ω ≃ₐ[K] Ω) :=
  haveI := t2Space_abGal p K Ω
  have hc : Continuous (unitsAbEquiv p K Ω) := by
    have h : (fun u : unitGroup p K =>
        (unitsAbEquiv p K Ω u : TopologicalAbelianization (Ω ≃ₐ[K] Ω))) =
        fun u : unitGroup p K => (galAbEquiv p K Ω).symm (artin p K Ω (u : Kˣ)) := by
      funext u
      rw [ContinuousMulEquiv.eq_symm_apply, galAbEquiv_unitsAbEquiv]
    refine continuous_induced_rng.2 ?_
    change Continuous fun u => (unitsAbEquiv p K Ω u : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
    rw [h]
    exact (galAbEquiv p K Ω).symm.continuous.comp continuous_artin_unitGroup
  { toMulEquiv := unitsAbEquiv p K Ω
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2
      (f := (unitsAbEquiv p K Ω).toEquiv)).symm.continuous }

theorem unitsAbContEquiv_apply (u : unitGroup p K) :
    unitsAbContEquiv p K Ω u = unitsAbEquiv p K Ω u := rfl

/-- A unit of `K` has the same image in `G_K^ab` as a unit and as an element of `Kˣ`. -/
theorem multAbEquiv_coe_unit (u : unitGroup p K) :
    (multAbEquiv p K Ω u : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = unitsAbEquiv p K Ω u := by
  apply (galAbEquiv p K Ω).injective
  rw [galAbEquiv_multAbEquiv, galAbEquiv_unitsAbEquiv]

/-- The image of a Frobenius lift in `G_K^ab` is the image of a uniformiser. -/
theorem exists_uniformizer_of_isFrobLift {φ : Ω ≃ₐ[K] Ω} (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ) :
    ∃ π : Kˣ, v p (π : K) = 1 ∧
      (multAbEquiv p K Ω π : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = QuotientGroup.mk φ := by
  have hW : (QuotientGroup.mk φ : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) ∈
      abWeil (Ω ≃ₐ[K] Ω) :=
    Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Or.inl hφ))
  set π := (multAbEquiv p K Ω).symm ⟨_, hW⟩
  have hπ : (multAbEquiv p K Ω π : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
      QuotientGroup.mk φ := by
    rw [MulEquiv.apply_symm_apply]
  refine ⟨π, ?_, hπ⟩
  refine ((hasRecVal_gal_iff (p := p) (Ω := Ω) π 1).1 ⟨φ, 1, hφ, one_mem _, ?_⟩).symm
  rw [hπ, zpow_one, mul_one]

/-- Every uniformiser is the image of a Frobenius lift in `G_K^ab`. -/
theorem exists_isFrobLift_of_uniformizer {π : Kˣ} (hπ : v p (π : K) = 1) :
    ∃ φ : Ω ≃ₐ[K] Ω, IsFrobLift (Ω ≃ₐ[K] Ω) φ ∧
      (multAbEquiv p K Ω π : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = QuotientGroup.mk φ := by
  obtain ⟨φ, τ, hφ, hτ, he⟩ :=
    (hasRecVal_gal_iff (p := p) (Ω := Ω) π 1).2 hπ.symm
  refine ⟨φ * τ, ?_, by rw [he, zpow_one]⟩
  rw [isFrobLift_gal_iff p, QuotientGroup.mk_mul, ← (isFrobLift_gal_iff p φ).1 hφ,
    (QuotientGroup.eq_one_iff τ).2 (by rw [← recInertia_gal p]; exact hτ), mul_one]

/-- **The group-theoretic decomposition map is `(unitsAbContEquiv × id)` followed by
`abZHatEquiv hπ⁻¹`**, when the Frobenius lift `φ` and the uniformiser `π` have the same image
in `G_K^ab`. -/
theorem abZHatEquiv_recAbHom [TotallyDisconnectedSpace (TopologicalAbelianization (Ω ≃ₐ[K] Ω))]
    {π : Kˣ} (hπ : v p (π : K) = 1) {φ : Ω ≃ₐ[K] Ω}
    (hφπ : (multAbEquiv p K Ω π : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) = QuotientGroup.mk φ)
    (x : abUnits (Ω ≃ₐ[K] Ω) × Multiplicative ZHat) :
    abZHatEquiv p K Ω hπ (recAbHom (Ω ≃ₐ[K] Ω) φ x) = ((unitsAbContEquiv p K Ω).symm x.1, x.2) := by
  haveI := t2Space_abGal p K Ω
  have hz : (zhatPow (QuotientGroup.mk φ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))).toMonoidHom =
      (abZHatEquiv p K Ω hπ).symm.toMulEquiv.toMonoidHom.comp (MonoidHom.inr _ _) :=
    zhat_hom_ext (zhatPow _).continuous
      ((abZHatEquiv p K Ω hπ).symm.continuous.comp (continuous_const.prodMk continuous_id)) (by
        change zhatPow _ _ = (abZHatEquiv p K Ω hπ).symm (1, _)
        rw [zhatPow_one, ← hφπ, ContinuousMulEquiv.eq_symm_apply,
          abZHatEquiv_multAbEquiv_uniformizer])
  have h2 : zhatPow (QuotientGroup.mk φ : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) x.2 =
      (abZHatEquiv p K Ω hπ).symm (1, x.2) := DFunLike.congr_fun hz x.2
  have h1 : (x.1 : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
      unitsAbEquiv p K Ω ((unitsAbContEquiv p K Ω).symm x.1) := by
    rw [← unitsAbContEquiv_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [recAbHom_apply, map_mul, h2, ContinuousMulEquiv.apply_symm_apply, h1,
    abZHatEquiv_unitsAbEquiv, Prod.mk_mul_mk, mul_one, one_mul]

include p in
theorem recAbHom_bijective [TotallyDisconnectedSpace (TopologicalAbelianization (Ω ≃ₐ[K] Ω))]
    {φ : Ω ≃ₐ[K] Ω} (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ) :
    Function.Bijective (recAbHom (Ω ≃ₐ[K] Ω) φ) := by
  obtain ⟨π, hπ, hφπ⟩ := exists_uniformizer_of_isFrobLift (p := p) hφ
  have h : (recAbHom (Ω ≃ₐ[K] Ω) φ : _ → _) = (abZHatEquiv p K Ω hπ).symm ∘
      fun x => ((unitsAbContEquiv p K Ω).symm x.1, x.2) := by
    funext x
    rw [Function.comp_apply, ContinuousMulEquiv.eq_symm_apply, abZHatEquiv_recAbHom hπ hφπ]
  rw [h]
  refine (abZHatEquiv p K Ω hπ).symm.bijective.comp ⟨fun x y hxy => ?_, fun y => ?_⟩
  · simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at hxy
    exact Prod.ext hxy.1 hxy.2
  · exact ⟨(unitsAbContEquiv p K Ω y.1, y.2), by simp⟩

/-- **`G_K^ab ≅ 𝒪^×(G_K) × Ẑ`, group-theoretically**: for every Frobenius lift `φ`, the
group-theoretic map `(u, a) ↦ u · [φ]^a` is an isomorphism of topological groups
`abUnits G_K × Ẑ ≃ₜ* G_K^ab`. -/
noncomputable def recAbEquiv [TotallyDisconnectedSpace (TopologicalAbelianization (Ω ≃ₐ[K] Ω))]
    {φ : Ω ≃ₐ[K] Ω} (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ) :
    abUnits (Ω ≃ₐ[K] Ω) × Multiplicative ZHat ≃ₜ* TopologicalAbelianization (Ω ≃ₐ[K] Ω) :=
  haveI := t2Space_abGal p K Ω
  haveI : CompactSpace (abUnits (Ω ≃ₐ[K] Ω)) :=
    (unitsAbContEquiv p K Ω).toHomeomorph.compactSpace
  let e := MulEquiv.ofBijective _ (recAbHom_bijective (p := p) hφ)
  { toMulEquiv := e
    continuous_toFun := continuous_recAbHom φ
    continuous_invFun := ((continuous_recAbHom φ).homeoOfEquivCompactToT2
      (f := e.toEquiv)).symm.continuous }

theorem recAbEquiv_apply [TotallyDisconnectedSpace (TopologicalAbelianization (Ω ≃ₐ[K] Ω))]
    {φ : Ω ≃ₐ[K] Ω} (hφ : IsFrobLift (Ω ≃ₐ[K] Ω) φ)
    (x : abUnits (Ω ≃ₐ[K] Ω) × Multiplicative ZHat) :
    recAbEquiv (p := p) hφ x = recAbHom (Ω ≃ₐ[K] Ω) φ x := rfl

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

variable (p p') in
/-- **The isomorphism `𝒪_Kˣ ≃ₜ* 𝒪_{K'}ˣ` induced by `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')`**: the restriction
of `galEquiv_multEquiv` to the units (`galEquiv_unitsEquiv_apply`), a homeomorphism. -/
noncomputable def galEquiv_unitsEquiv (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) :
    unitGroup p K ≃ₜ* unitGroup p' K' :=
  (unitsAbContEquiv p K Ω).trans ((abUnitsContEquiv ψ).trans (unitsAbContEquiv p' K' Ω').symm)

theorem galEquiv_unitsEquiv_apply (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (u : unitGroup p K) :
    (galEquiv_unitsEquiv p p' ψ u : K'ˣ) = galEquiv_multEquiv p p' ψ u := by
  apply (multAbEquiv p' K' Ω').injective
  apply Subtype.ext
  rw [multAbEquiv_coe_unit, multAbEquiv_galEquiv_multEquiv, multAbEquiv_coe_unit,
    galEquiv_unitsEquiv, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.trans_apply,
    ← unitsAbContEquiv_apply, ContinuousMulEquiv.apply_symm_apply, coe_abUnitsContEquiv,
    unitsAbContEquiv_apply]

/-- The image of a uniformiser under `galEquiv_multEquiv` is a uniformiser. -/
theorem v_galEquiv_multEquiv_uniformizer (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) {π : Kˣ}
    (hπ : v p (π : K) = 1) : v p' (galEquiv_multEquiv p p' ψ π : K') = 1 := by
  rw [v_galEquiv_multEquiv, hπ]

/-- **`G_K^ab ≅ 𝒪_Kˣ × Ẑ` is group-theoretic**: under `G_K^ab ≅ 𝒪_Kˣ × Ẑ` (uniformiser `π`)
and `G_{K'}^ab ≅ 𝒪_{K'}ˣ × Ẑ` (uniformiser `ψ(π)`), the isomorphism `ψ^ab` induced by
`ψ : Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` is `(u, a) ↦ (ψ(u), a)`. -/
theorem abZHatEquiv_abContEquiv (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) {π : Kˣ}
    (hπ : v p (π : K) = 1) (x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    abZHatEquiv p' K' Ω' (v_galEquiv_multEquiv_uniformizer ψ hπ) (abContEquiv ψ x) =
      (galEquiv_unitsEquiv p p' ψ (abZHatEquiv p K Ω hπ x).1, (abZHatEquiv p K Ω hπ x).2) := by
  haveI := totallyDisconnectedSpace_abGal p K Ω
  haveI := totallyDisconnectedSpace_abGal p' K' Ω'
  obtain ⟨φ, hφ, hφπ⟩ := exists_isFrobLift_of_uniformizer (Ω := Ω) hπ
  set y := abZHatEquiv p K Ω hπ x
  have hx : x = recAbHom (Ω ≃ₐ[K] Ω) φ (unitsAbContEquiv p K Ω y.1, y.2) := by
    apply (abZHatEquiv p K Ω hπ).injective
    rw [abZHatEquiv_recAbHom hπ hφπ, ContinuousMulEquiv.symm_apply_apply]
  have hφπ' : (multAbEquiv p' K' Ω' (galEquiv_multEquiv p p' ψ π) :
      TopologicalAbelianization (Ω' ≃ₐ[K'] Ω')) = QuotientGroup.mk (ψ φ) := by
    rw [multAbEquiv_galEquiv_multEquiv, hφπ]
    rfl
  rw [hx, abContEquiv_recAbHom, abZHatEquiv_recAbHom _ hφπ']
  rfl

/-- The `Ẑ`-components correspond (independently of the uniformisers). -/
theorem abZHatEquiv_snd_abContEquiv (ψ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) {π : Kˣ}
    (hπ : v p (π : K) = 1) {π' : K'ˣ} (hπ' : v p' (π' : K') = 1)
    (x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :
    (abZHatEquiv p' K' Ω' hπ' (abContEquiv ψ x)).2 = (abZHatEquiv p K Ω hπ x).2 := by
  induction x using QuotientGroup.induction_on with
  | H σ =>
    rw [abContEquiv_mk, abZHatEquiv_snd_mk, abZHatEquiv_snd_mk]
    exact galEquiv_unrZHat ψ (QuotientGroup.mk σ)

end Galois

end Iut.Reconstruction
