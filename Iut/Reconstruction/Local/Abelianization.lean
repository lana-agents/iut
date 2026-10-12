/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Frobenius
import LocalClassFieldTheory.Reciprocity.ArtinInertia
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# The images of `𝒪_Kˣ` and `Kˣ` in `G_K^ab` (roadmap P17, M1f)

[AbsAnab], Proposition 1.2.1 (iv)–(v) and [AbsTopIII], Proposition 5.8 (i): via local class
field theory, `Kˣ` and `𝒪_Kˣ` embed into the abelianisation `G_K^ab`, and their images are
determined by the topological group `G_K`:

* `G_K^ab = G_K / closure([G_K, G_K])` is `Gal(K^ab/K)` as a topological group
  (`galAbEquiv`): the closure of the commutator subgroup is `Gal(Ω/K^ab)`
  (`closure_commutator_eq`), because an element fixed by all commutators lies in a finite
  abelian subextension (`fixedField_commutator_le`);
* the image of `𝒪_Kˣ` (under the Artin map) is the image of the inertia subgroup
  (`map_abUnits_gal`), and the image of `Kˣ` is the image of the Weil group
  `W_K = ⟨Frobenius lifts, I_K⟩` (`map_abWeil_gal`);
* both are group-theoretic (`map_abUnits`, `map_abWeil`), as `recInertia` and `recWeil` are.

## Main definitions and results

* `Iut.Reconstruction.abUnits G`, `Iut.Reconstruction.abWeil G`: the images of `recInertia G`
  and `recWeil G` in `TopologicalAbelianization G`;
* `Iut.Reconstruction.galAbEquiv : G_K^ab ≃ₜ* Gal(K^ab/K)`;
* `Iut.Reconstruction.unitsAbEquiv : 𝒪_Kˣ ≃* abUnits G_K`,
  `Iut.Reconstruction.multAbEquiv : Kˣ ≃* abWeil G_K` (compatible with the Artin map);
* `Iut.Reconstruction.galEquiv_multEquiv`: every `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` induces
  `Kˣ ≃* K'ˣ` mapping `𝒪_Kˣ` onto `𝒪_{K'}ˣ` (`galEquiv_multEquiv_units`).
-/

open PadicField IntermediateField
open scoped commutatorElement

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

/-! ### Group-theoretic part -/

section GroupTheoretic

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- The image of the reconstructed inertia subgroup in `G^ab` (`𝒪ˣ` for `G = G_K`). -/
noncomputable def abUnits (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup (TopologicalAbelianization G) :=
  (recInertia G).map (QuotientGroup.mk' _)

/-- The image of the reconstructed Weil group in `G^ab` (`Kˣ` for `G = G_K`). -/
noncomputable def abWeil (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Subgroup (TopologicalAbelianization G) :=
  (recWeil G).map (QuotientGroup.mk' _)

theorem map_closure_commutator (ψ : G ≃ₜ* G') :
    (commutator G).topologicalClosure.map (ψ : G ≃* G') =
      (commutator G').topologicalClosure := by
  apply SetLike.coe_injective
  rw [Subgroup.coe_map, Subgroup.topologicalClosure_coe, Subgroup.topologicalClosure_coe]
  have h1 := ψ.toHomeomorph.image_closure (commutator G : Set G)
  have h2 : (commutator G).map (ψ : G ≃* G').toMonoidHom = commutator G' := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.surjective]
  have h3 : ψ.toHomeomorph '' (commutator G : Set G) = (commutator G' : Set G') := by
    rw [← h2, Subgroup.coe_map]
    rfl
  rw [← h3, ← h1]
  rfl

/-- The isomorphism of abelianisations induced by an isomorphism of topological groups. -/
noncomputable def abEquiv (ψ : G ≃ₜ* G') :
    TopologicalAbelianization G ≃* TopologicalAbelianization G' :=
  QuotientGroup.congr _ _ (ψ : G ≃* G') (map_closure_commutator ψ)

theorem abEquiv_comp_mk (ψ : G ≃ₜ* G') :
    (abEquiv ψ : TopologicalAbelianization G →* TopologicalAbelianization G').comp
        (QuotientGroup.mk' _) = (QuotientGroup.mk' _).comp (ψ.toMulEquiv.toMonoidHom) := by
  ext x
  rfl

/-- **The image of `𝒪ˣ` is group-theoretic.** -/
theorem map_abUnits (ψ : G ≃ₜ* G') :
    (abUnits G).map (abEquiv ψ : TopologicalAbelianization G →* _) = abUnits G' := by
  rw [abUnits, abUnits, Subgroup.map_map, abEquiv_comp_mk, ← Subgroup.map_map,
    map_recInertia]

/-- **The image of `Kˣ` is group-theoretic.** -/
theorem map_abWeil (ψ : G ≃ₜ* G') :
    (abWeil G).map (abEquiv ψ : TopologicalAbelianization G →* _) = abWeil G' := by
  rw [abWeil, abWeil, Subgroup.map_map, abEquiv_comp_mk, ← Subgroup.map_map, map_recWeil]

end GroupTheoretic

/-! ### `G_K^ab = Gal(K^ab/K)` -/

section Galois

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω] [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

instance normal_maxAbelian : Normal K (maxAbelian K Ω) := by
  unfold maxAbelian
  infer_instance

/-- Commutators act trivially on `K^ab`. -/
theorem commutator_le_fixingSubgroup :
    commutator (Ω ≃ₐ[K] Ω) ≤ (maxAbelian K Ω).fixingSubgroup := by
  rw [commutator, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  obtain ⟨L, hxL⟩ := mem_maxAbelian_iff.1 hx
  have h1 : ⁅g₁, g₂⁆ ∈ L.1.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_def,
      (IsMulCommutative.is_comm (M := L.1 ≃ₐ[K] L.1)).comm (AlgEquiv.restrictNormalHom L.1 g₁),
      mul_assoc,
      mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h1 x hxL

/-- A subgroup containing the commutator subgroup is normal. -/
theorem normal_of_commutator_le {Γ : Type*} [Group Γ] {H : Subgroup Γ}
    (h : commutator Γ ≤ H) : H.Normal where
  conj_mem n hn g := by
    have : g * n * g⁻¹ = ⁅g, n⁆ * n := by group
    rw [this]
    exact mul_mem (h (Subgroup.commutator_mem_commutator (Subgroup.mem_top g)
      (Subgroup.mem_top n))) hn

/-- **Elements fixed by all commutators are abelian**: they lie in a finite abelian
subextension. -/
theorem fixedField_commutator_le :
    fixedField (commutator (Ω ≃ₐ[K] Ω)) ≤ maxAbelian K Ω := by
  intro x hx
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  haveI : FiniteDimensional K K⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Normal K Ω := IsGalois.to_normal
  set L := normalClosure K K⟮x⟯ Ω
  have hxL : x ∈ L := IntermediateField.le_normalClosure _
    (IntermediateField.mem_adjoin_simple_self K x)
  set H := L.fixingSubgroup ⊔ commutator (Ω ≃ₐ[K] Ω)
  have hHopen : IsOpen (H : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isOpen_mono le_sup_left L.fixingSubgroup_isOpen
  have hHcl : IsClosed (H : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen H hHopen
  set M := fixedField H
  have hfixM : M.fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHcl⟩
  have hML : M ≤ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    exact IntermediateField.fixedField_antitone le_sup_left
  haveI : FiniteDimensional K M := FiniteDimensional.of_injective
    (IntermediateField.inclusion hML).toLinearMap (IntermediateField.inclusion hML).injective
  haveI : H.Normal := normal_of_commutator_le le_sup_right
  have hgal : IsGalois K M := by
    rw [← InfiniteGalois.normal_iff_isGalois, hfixM]
    infer_instance
  have hab : IsAbelianGalois K M :=
    { toIsGalois := hgal
      is_comm := ⟨fun a b => by
        obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω a
        obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω b
        have hc : ⁅a', b'⁆ ∈ M.fixingSubgroup := by
          rw [hfixM]
          exact le_sup_right (b := commutator (Ω ≃ₐ[K] Ω))
            (Subgroup.commutator_mem_commutator (Subgroup.mem_top a') (Subgroup.mem_top b'))
        rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm] at hc
        rw [← map_mul, ← map_mul, map_mul, map_mul]
        exact hc⟩ }
  have hxM : x ∈ M := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hle : H ≤ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := by
      refine sup_le ?_ ?_
      · intro g hg
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x hxL
      · intro g hg
        exact (IntermediateField.mem_fixedField_iff _ _).1 hx g hg
    exact hle hf
  exact le_maxAbelian ⟨M, inferInstance, hab⟩ hxM

/-- **The closure of the commutator subgroup of `G_K` is `Gal(Ω/K^ab)`.** -/
theorem closure_commutator_eq :
    (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure = (maxAbelian K Ω).fixingSubgroup := by
  apply le_antisymm
  · exact Subgroup.topologicalClosure_minimal _ commutator_le_fixingSubgroup
      (InfiniteGalois.fixingSubgroup_isClosed _)
  · set C := (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure
    have hC : (fixedField C).fixingSubgroup = C :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨C, Subgroup.isClosed_topologicalClosure _⟩
    rw [← hC]
    apply IntermediateField.fixingSubgroup_antitone
    exact (IntermediateField.fixedField_antitone (Subgroup.le_topologicalClosure _)).trans
      fixedField_commutator_le

theorem ker_restrict_maxAbelian :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxAbelian K Ω)).ker =
      (commutator (Ω ≃ₐ[K] Ω)).topologicalClosure := by
  rw [IntermediateField.restrictNormalHom_ker, closure_commutator_eq]

variable (p K Ω) in
/-- **`G_K^ab = Gal(K^ab/K)`** as topological groups, induced by restriction. -/
noncomputable def galAbEquiv :
    TopologicalAbelianization (Ω ≃ₐ[K] Ω) ≃ₜ* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
  haveI := isAlgebraic_tower_top p K Ω
  haveI : Algebra.IsIntegral K (maxAbelian K Ω) := inferInstance
  haveI : T2Space (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) := krullTopology_t2
  let e : TopologicalAbelianization (Ω ≃ₐ[K] Ω) ≃* (maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) :=
    QuotientGroup.liftEquiv _ (AlgEquiv.restrictNormalHom_surjective Ω)
      ker_restrict_maxAbelian.symm
  have hc : Continuous e := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    exact InfiniteGalois.restrictNormalHom_continuous (maxAbelian K Ω)
  { toMulEquiv := e
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem galAbEquiv_mk (σ : Ω ≃ₐ[K] Ω) :
    galAbEquiv p K Ω (QuotientGroup.mk σ) = AlgEquiv.restrictNormalHom (maxAbelian K Ω) σ :=
  rfl

theorem galAbEquiv_comp_mk :
    ((galAbEquiv p K Ω).toMulEquiv.toMonoidHom).comp (QuotientGroup.mk' _) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) (maxAbelian K Ω) := by
  ext σ
  rfl

theorem map_abUnits_gal :
    (abUnits (Ω ≃ₐ[K] Ω)).map (galAbEquiv p K Ω).toMulEquiv.toMonoidHom =
      abInertia p K Ω := by
  rw [abUnits, Subgroup.map_map, galAbEquiv_comp_mk, recInertia_gal p]
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩ y hy
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    have hτ' : τ ∈ (maxUnramified p K Ω).fixingSubgroup := by rw [← absInertia_eq]; exact hτ
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ' _ hy
  · intro hσ
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω σ
    refine ⟨τ, ?_, rfl⟩
    change τ ∈ absInertia p K Ω
    rw [absInertia_eq, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have := congrArg Subtype.val (hσ ⟨y, maxUnramified_le_maxAbelian hy⟩ hy)
    rwa [AlgEquiv.restrictNormalHom_apply] at this

/-- A lift of the image of a uniformiser under the Artin map is a lift of the Frobenius. -/
theorem exists_frob_lift_artin :
    ∃ (π : Kˣ) (φ : Ω ≃ₐ[K] Ω), v p (π : K) = 1 ∧
      AlgEquiv.restrictNormalHom (maxAbelian K Ω) φ = artin p K Ω π ∧
      (QuotientGroup.mk φ : (Ω ≃ₐ[K] Ω) ⧸ absInertia p K Ω) = arithFrob p K Ω := by
  set π : Kˣ := Units.mk0 (uniformizer p K) (uniformizer_spec (p := p) (K := K)).ne_zero
  have hπ : v p ((π : Kˣ) : K) = 1 := uniformizer_spec
  obtain ⟨φ, hφ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω (artin p K Ω π)
  refine ⟨π, φ, hπ, hφ, mk_eq_arithFrob_of_artin π hπ φ fun y => ?_⟩
  rw [← hφ, AlgEquiv.restrictNormalHom_apply]

theorem restrict_mem_abInertia {τ : Ω ≃ₐ[K] Ω} (hτ : τ ∈ absInertia p K Ω) :
    AlgEquiv.restrictNormalHom (maxAbelian K Ω) τ ∈ abInertia p K Ω := by
  intro y hy
  apply Subtype.ext
  rw [AlgEquiv.restrictNormalHom_apply]
  have hτ' : τ ∈ (maxUnramified p K Ω).fixingSubgroup := by rw [← absInertia_eq]; exact hτ
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ' _ hy

/-- **The image of `Kˣ`**: the image of the Weil group in `G_K^ab = Gal(K^ab/K)` is the image
of the Artin map. -/
theorem map_abWeil_gal :
    (abWeil (Ω ≃ₐ[K] Ω)).map (galAbEquiv p K Ω).toMulEquiv.toMonoidHom =
      (artin p K Ω).range := by
  rw [abWeil, Subgroup.map_map, galAbEquiv_comp_mk]
  obtain ⟨π, φ, hπ, hφ, hφF⟩ := exists_frob_lift_artin (p := p) (K := K) (Ω := Ω)
  have hφW : φ ∈ recWeil (Ω ≃ₐ[K] Ω) :=
    Subgroup.subset_closure (Or.inl ((isFrobLift_gal_iff p φ).2 hφF))
  ext σ
  constructor
  · rintro ⟨σ', hσ', rfl⟩
    obtain ⟨k, hk⟩ := (mem_recWeil_gal_iff p σ').1 hσ'
    have hτ : (φ ^ k)⁻¹ * σ' ∈ absInertia p K Ω := by
      rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hφF, hk]
    obtain ⟨u, hu⟩ := (unitsInertiaEquiv p K Ω).surjective ⟨_, restrict_mem_abInertia hτ⟩
    refine ⟨π ^ k * u, ?_⟩
    have hu' : artin p K Ω u = AlgEquiv.restrictNormalHom (maxAbelian K Ω) ((φ ^ k)⁻¹ * σ') := by
      rw [← unitsInertiaEquiv_apply, hu]
    rw [map_mul, map_zpow, ← hφ, hu', ← map_zpow, ← map_mul, mul_inv_cancel_left]
  · rintro ⟨x, rfl⟩
    set k := v p (x : K)
    set u : Kˣ := x * π ^ (-k)
    have hu : v p (u : K) = 0 := by
      simp only [u, Units.val_mul, Units.val_zpow_eq_zpow_val]
      rw [v_mul x.ne_zero (zpow_ne_zero _ π.ne_zero), v_zpow π.ne_zero, hπ]
      ring
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω (artin p K Ω u)
    have hτI : τ ∈ absInertia p K Ω := mem_absInertia_of_artin u hu τ fun y => by
      rw [← hτ, AlgEquiv.restrictNormalHom_apply]
    refine ⟨φ ^ k * τ, mul_mem (zpow_mem hφW k)
      (Subgroup.subset_closure (Or.inr (by rw [SetLike.mem_coe, recInertia_gal p]; exact hτI))),
      ?_⟩
    rw [map_mul, map_zpow, hφ, hτ, ← map_zpow, ← map_mul]
    congr 1
    simp only [u]
    rw [← mul_assoc, mul_right_comm, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

variable (p K Ω) in
/-- **`𝒪_Kˣ` is the image of inertia in `G_K^ab`** (via the Artin map). -/
noncomputable def unitsAbEquiv : unitGroup p K ≃* abUnits (Ω ≃ₐ[K] Ω) :=
  (unitsInertiaEquiv p K Ω).trans ((MulEquiv.subgroupCongr (map_abUnits_gal (p := p)).symm).trans
    ((galAbEquiv p K Ω).toMulEquiv.subgroupMap (abUnits _)).symm)

theorem galAbEquiv_unitsAbEquiv (u : unitGroup p K) :
    galAbEquiv p K Ω (unitsAbEquiv p K Ω u) = artin p K Ω u := by
  set z : (abUnits (Ω ≃ₐ[K] Ω)).map (galAbEquiv p K Ω).toMulEquiv.toMonoidHom :=
    MulEquiv.subgroupCongr (map_abUnits_gal (p := p)).symm (unitsInertiaEquiv p K Ω u)
  have := congrArg Subtype.val
    (((galAbEquiv p K Ω).toMulEquiv.subgroupMap (abUnits _)).apply_symm_apply z)
  exact this

variable (p K Ω) in
/-- **`Kˣ` is the image of the Weil group in `G_K^ab`** (via the Artin map). -/
noncomputable def multAbEquiv : Kˣ ≃* abWeil (Ω ≃ₐ[K] Ω) :=
  (MonoidHom.ofInjective (artin_injective (p := p) (K := K) (Ω := Ω))).trans
    ((MulEquiv.subgroupCongr (map_abWeil_gal (p := p)).symm).trans
      ((galAbEquiv p K Ω).toMulEquiv.subgroupMap (abWeil _)).symm)

theorem galAbEquiv_multAbEquiv (x : Kˣ) :
    galAbEquiv p K Ω (multAbEquiv p K Ω x) = artin p K Ω x := by
  set z : (abWeil (Ω ≃ₐ[K] Ω)).map (galAbEquiv p K Ω).toMulEquiv.toMonoidHom :=
    MulEquiv.subgroupCongr (map_abWeil_gal (p := p)).symm
      (MonoidHom.ofInjective (artin_injective (p := p) (K := K) (Ω := Ω)) x)
  have := congrArg Subtype.val
    (((galAbEquiv p K Ω).toMulEquiv.subgroupMap (abWeil _)).apply_symm_apply z)
  exact this

/-- The units are exactly the elements of `Kˣ` whose image lies in the image of inertia. -/
theorem multAbEquiv_mem_abUnits_iff (x : Kˣ) :
    (multAbEquiv p K Ω x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) ∈ abUnits (Ω ≃ₐ[K] Ω) ↔
      x ∈ unitGroup p K := by
  constructor
  · intro h
    have h1 : galAbEquiv p K Ω (multAbEquiv p K Ω x) ∈ abInertia p K Ω := by
      rw [← map_abUnits_gal (p := p)]
      exact Subgroup.mem_map_of_mem _ h
    rw [galAbEquiv_multAbEquiv] at h1
    obtain ⟨u, hu⟩ := (unitsInertiaEquiv p K Ω).surjective ⟨_, h1⟩
    have hux : (u : Kˣ) = x := artin_injective (p := p) (Ω := Ω)
      (by rw [← unitsInertiaEquiv_apply, hu])
    rw [← hux]
    exact u.2
  · intro h
    have h1 : (multAbEquiv p K Ω x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
        unitsAbEquiv p K Ω ⟨x, h⟩ := by
      apply (galAbEquiv p K Ω).injective
      rw [galAbEquiv_multAbEquiv, galAbEquiv_unitsAbEquiv]
    rw [h1]
    exact (unitsAbEquiv p K Ω ⟨x, h⟩).2

variable {p' : ℕ} [Fact p'.Prime]
variable {K' : Type*} [Field K'] [Algebra ℚ_[p'] K'] [FiniteDimensional ℚ_[p'] K']
variable {Ω' : Type*} [Field Ω'] [Algebra K' Ω'] [Algebra ℚ_[p'] Ω'] [IsScalarTower ℚ_[p'] K' Ω']
  [IsAlgClosed Ω'] [IsGalois K' Ω'] [Algebra.IsAlgebraic ℚ_[p'] Ω']

variable (p p') in
/-- **[AbsTopIII], Proposition 5.8 (i)**, multiplicative part: an isomorphism of topological
groups `Gal(Ω/K) ≃ₜ* Gal(Ω'/K')` induces an isomorphism `Kˣ ≃* K'ˣ` (through `G^ab` and the
reconstructed Weil groups). -/
noncomputable def galEquiv_multEquiv (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) : Kˣ ≃* K'ˣ :=
  (multAbEquiv p K Ω).trans ((((abEquiv φ).subgroupMap (abWeil _)).trans
    (MulEquiv.subgroupCongr (map_abWeil φ))).trans (multAbEquiv p' K' Ω').symm)

theorem multAbEquiv_galEquiv_multEquiv (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (x : Kˣ) :
    (multAbEquiv p' K' Ω' (galEquiv_multEquiv p p' φ x) : TopologicalAbelianization _) =
      abEquiv φ (multAbEquiv p K Ω x) := by
  simp [galEquiv_multEquiv]

/-- **The units are group-theoretic**: the induced `Kˣ ≃* K'ˣ` maps `𝒪_Kˣ` onto `𝒪_{K'}ˣ`. -/
theorem galEquiv_multEquiv_units (φ : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω' ≃ₐ[K'] Ω')) (x : Kˣ) :
    galEquiv_multEquiv p p' φ x ∈ unitGroup p' K' ↔ x ∈ unitGroup p K := by
  rw [← multAbEquiv_mem_abUnits_iff (Ω := Ω'), multAbEquiv_galEquiv_multEquiv,
    ← multAbEquiv_mem_abUnits_iff (Ω := Ω), ← map_abUnits φ]
  exact ⟨fun ⟨y, hy, hxy⟩ => by rwa [(abEquiv φ).injective hxy] at hy,
    fun h => Subgroup.mem_map_of_mem _ h⟩

end Galois

end Iut.Reconstruction
