/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.Abelianization
import Iut.Reconstruction.Local.Cyclotome

/-!
# The torsion of `G_K^ab` and Kummer rigidity of the cyclotome (roadmap P17, M2b)

[AbsTopIII], Corollary 1.10 (i) (a) defines the group-theoretic cyclotome
`μ_{ℚ/ℤ}(G) = lim_{→, H} (H^ab)_tors` (direct limit along the transfer maps). Its building
blocks are the torsion subgroups `(H^ab)_tors` of the abelianisations of the open subgroups
`H = G_L`; here we identify them:

* `Gal(K^ur/K)` is torsion-free (`eq_one_of_pow_eq_one_unr`), so a torsion element of
  `Gal(K^ab/K)` lies in the inertia subgroup `Gal(K^ab/K^ur) = artin(𝒪ˣ)` and is the image of a
  root of unity (`exists_artin_eq_of_pow_eq_one`);
* hence **`(G_K^ab)_tors ≅ μ(K)`** (`torsAbEquiv`), and for every finite `L/K` inside `Ω`,
  `(G_L^ab)_tors ≅ μ(L)` with `G_L ⊆ G_K` the open subgroup (`torsAbEquivFixing`); the
  torsion subgroup of the abelianisation is evidently group-theoretic (`map_torsion_abEquiv`).

The transition maps of the direct limit are the transfer maps `G_K^ab → G_L^ab`, which under
the Artin maps are the inclusions `Kˣ ⊆ Lˣ`; this transfer compatibility of local class field
theory is not part of `local-class-field-theory`, so the direct limit itself is not formed here.

**Kummer rigidity** ([AbsTopIII], Proposition 3.2, monoid form): the automorphisms of the
cyclotome `μ_n` are the power maps `ζ ↦ ζ^a`, inducing `β ↦ β^a` on `H¹(G_K, μ_n)`. If such an
automorphism fixes the Kummer classes `κ(x) ∈ H¹(G_K, μ_n)` of the multiplicative monoid
(already of one uniformiser), then it is the identity (`kummer_rigidity`): `κ(π)^{a-1} = 1`
forces `π^{a-1} ∈ (Kˣ)^n`, i.e. `n ∣ a - 1`.
-/

open PadicField IntermediateField KummerTheory

set_option linter.unusedSectionVars false

namespace Iut.Reconstruction

section Torsion

variable {G G' : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']

/-- **The torsion of the abelianisation is group-theoretic.** -/
theorem map_torsion_abEquiv (ψ : G ≃ₜ* G') :
    (CommGroup.torsion (TopologicalAbelianization G)).map
        (abEquiv ψ : TopologicalAbelianization G →* _) =
      CommGroup.torsion (TopologicalAbelianization G') := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, CommGroup.mem_torsion] at hy
    rw [CommGroup.mem_torsion]
    exact MonoidHom.isOfFinOrder (abEquiv ψ).toMonoidHom hy
  · intro hx
    refine ⟨(abEquiv ψ).symm x, ?_, (abEquiv ψ).apply_symm_apply x⟩
    rw [CommGroup.mem_torsion] at hx
    rw [SetLike.mem_coe, CommGroup.mem_torsion]
    exact MonoidHom.isOfFinOrder (abEquiv ψ).symm.toMonoidHom hx

end Torsion

section Unramified

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [Algebra ℚ_[p] Ω] [IsScalarTower ℚ_[p] K Ω]
  [IsAlgClosed Ω]

/-- **`Gal(K^ur/K) ≅ Ẑ` is torsion-free.** -/
theorem eq_one_of_pow_eq_one_unr (τ : maxUnramified p K Ω ≃ₐ[K] maxUnramified p K Ω) {n : ℕ}
    (hn : 0 < n) (h : τ ^ n = 1) : τ = 1 := by
  ext x
  obtain ⟨m, hm, hx⟩ := (mem_maxUnramified_iff (p := p)).1 x.2
  set M := m * n with hMdef
  have hM : 0 < M := Nat.mul_pos hm hn
  obtain ⟨k, hk⟩ := exists_eq_frobUr_pow τ hM
  have hpow : ∀ j : ℕ, ∀ y : maxUnramified p K Ω, (y : Ω) ∈ unramifiedOfDegree p K Ω M →
      (τ ^ j) y = (frobUr p K Ω ^ (k * j)) y := by
    intro j
    induction j with
    | zero => intro y _; simp
    | succ j ih =>
      intro y hy
      rw [pow_succ', AlgEquiv.mul_apply, ih y hy, hk _ (frobUr_pow_mem hM _ hy),
        ← AlgEquiv.mul_apply, ← pow_add]
      congr 2
      ring
  have hMu := isUnramified_unramifiedOfDegree p K Ω M
  have hfrob : frob hMu ^ (k * n) = 1 := by
    ext ⟨y, hy⟩
    have h1 := hpow n ⟨y, unramifiedOfDegree_le_maxUnramified p K Ω M hy⟩ hy
    rw [h, AlgEquiv.one_apply] at h1
    have h2 := frobUr_pow_apply hM (k * n) ⟨y, unramifiedOfDegree_le_maxUnramified p K Ω M hy⟩ hy
    rw [← h1] at h2
    exact h2.symm
  have hdvd : M ∣ k * n := by
    have := orderOf_dvd_of_pow_eq_one hfrob
    rwa [orderOf_frob, finrank_unramifiedOfDegree p K Ω hM] at this
  have hmk : m ∣ k := Nat.dvd_of_mul_dvd_mul_right hn hdvd
  have hxM : (x : Ω) ∈ unramifiedOfDegree p K Ω M :=
    unramifiedOfDegree_le_of_dvd hM.ne' (Dvd.intro n rfl) hx
  have hmu := isUnramified_unramifiedOfDegree p K Ω m
  have hfm : frob hmu ^ k = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, orderOf_frob, finrank_unramifiedOfDegree p K Ω hm]
    exact hmk
  rw [hk x hxM, frobUr_pow_apply hm k x hx, hfm]
  rfl

variable [IsGalois K Ω] [Algebra.IsAlgebraic ℚ_[p] Ω]

/-- An element of `G_K` whose `n`-th power lies in inertia lies in inertia. -/
theorem mem_absInertia_of_pow_mem {σ : Ω ≃ₐ[K] Ω} {n : ℕ} (hn : 0 < n)
    (h : σ ^ n ∈ absInertia p K Ω) : σ ∈ absInertia p K Ω := by
  rw [← QuotientGroup.eq_one_iff] at h ⊢
  have h1 := eq_one_of_pow_eq_one_unr (unramifiedQuotientEquiv p K Ω (QuotientGroup.mk σ)) hn
    (by rw [← map_pow, ← QuotientGroup.mk_pow, h, map_one])
  exact (unramifiedQuotientEquiv p K Ω).injective (by rw [h1, map_one])

/-- **Torsion in `Gal(K^ab/K)` comes from roots of unity.** -/
theorem exists_artin_eq_of_pow_eq_one (σ : maxAbelian K Ω ≃ₐ[K] maxAbelian K Ω) {n : ℕ}
    (hn : 0 < n) (h : σ ^ n = 1) : ∃ ζ : Kˣ, ζ ^ n = 1 ∧ artin p K Ω ζ = σ := by
  obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) Ω σ
  have h1 : σ' ^ n ∈ absInertia p K Ω := by
    rw [absInertia_eq, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have := congrArg (fun τ => ((τ ⟨y, maxUnramified_le_maxAbelian hy⟩ :
      maxAbelian K Ω) : Ω)) h
    simpa [← map_pow, AlgEquiv.restrictNormalHom_apply] using this
  have h2 := mem_absInertia_of_pow_mem hn h1
  obtain ⟨u, hu⟩ := (unitsInertiaEquiv p K Ω).surjective ⟨_, restrict_mem_abInertia h2⟩
  have hu' : artin p K Ω u = AlgEquiv.restrictNormalHom (maxAbelian K Ω) σ' := by
    rw [← unitsInertiaEquiv_apply, hu]
  refine ⟨u, artin_injective (p := p) (Ω := Ω) ?_, hu'⟩
  rw [map_pow, hu', h, map_one]

theorem multAbEquiv_mem_torsion_iff (x : Kˣ) :
    (multAbEquiv p K Ω x : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) ∈
        CommGroup.torsion (TopologicalAbelianization (Ω ≃ₐ[K] Ω)) ↔
      x ∈ CommGroup.torsion Kˣ := by
  rw [CommGroup.mem_torsion, CommGroup.mem_torsion]
  constructor
  · intro h
    have h1 : IsOfFinOrder (artin p K Ω x) := by
      rw [← galAbEquiv_multAbEquiv]
      exact MonoidHom.isOfFinOrder (galAbEquiv p K Ω).toMulEquiv.toMonoidHom h
    exact (Function.Injective.isOfFinOrder_iff (f := artin p K Ω)
      (artin_injective (p := p) (Ω := Ω))).1 h1
  · intro h
    exact MonoidHom.isOfFinOrder (Subgroup.subtype _)
      (MonoidHom.isOfFinOrder (multAbEquiv p K Ω).toMonoidHom h)

variable (p K Ω) in
/-- **`(G_K^ab)_tors ≅ μ(K)`** (via the Artin map). -/
noncomputable def torsAbEquiv :
    CommGroup.torsion Kˣ ≃* CommGroup.torsion (TopologicalAbelianization (Ω ≃ₐ[K] Ω)) :=
  MulEquiv.ofBijective
    ((((abWeil _).subtype.comp (multAbEquiv p K Ω).toMonoidHom).comp
      (CommGroup.torsion Kˣ).subtype).codRestrict _
      (fun x => (multAbEquiv_mem_torsion_iff x.1).2 x.2))
    ⟨fun x y h => by
        have h' := congrArg Subtype.val h
        exact Subtype.ext ((multAbEquiv p K Ω).injective (Subtype.ext h')),
      fun t => by
        obtain ⟨n, hn, htn⟩ := (isOfFinOrder_iff_pow_eq_one).1
          ((CommGroup.mem_torsion _).1 t.2)
        have h1 : galAbEquiv p K Ω (t : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) ^ n = 1 := by
          rw [← map_pow, htn, map_one]
        obtain ⟨ζ, hζn, hζ⟩ := exists_artin_eq_of_pow_eq_one (p := p) _ hn h1
        refine ⟨⟨ζ, (CommGroup.mem_torsion _).2
          ((isOfFinOrder_iff_pow_eq_one).2 ⟨n, hn, hζn⟩)⟩, Subtype.ext ?_⟩
        apply (galAbEquiv p K Ω).injective
        change galAbEquiv p K Ω (multAbEquiv p K Ω ζ) = _
        rw [galAbEquiv_multAbEquiv, hζ]⟩

theorem galAbEquiv_torsAbEquiv (ζ : CommGroup.torsion Kˣ) :
    galAbEquiv p K Ω (torsAbEquiv p K Ω ζ : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) =
      artin p K Ω ζ :=
  galAbEquiv_multAbEquiv _

variable (p) in
/-- **`(H^ab)_tors ≅ μ(L)`** for the open subgroup `H = Gal(Ω/L) ⊆ G_K`, `L/K` finite. -/
noncomputable def torsAbEquivFixing (L : IntermediateField K Ω) [FiniteDimensional K L] :
    CommGroup.torsion Lˣ ≃*
      CommGroup.torsion (TopologicalAbelianization L.fixingSubgroup) :=
  haveI : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  haveI : FiniteDimensional ℚ_[p] L := Module.Finite.trans K L
  (torsAbEquiv p L Ω).trans
    ((((abEquiv (fixingSubgroupContEquiv L).symm).subgroupMap _)).trans
      (MulEquiv.subgroupCongr (map_torsion_abEquiv (fixingSubgroupContEquiv L).symm)))

end Unramified

/-! ### Kummer rigidity of the cyclotome -/

section Rigidity

variable {K : Type*} [Field K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [IsGalois K Ω]
variable {n : ℕ} [HasKummerRoots n K Ω] [Algebra.IsIntegral K Ω]

/-- **Kummer rigidity** ([AbsTopIII], Proposition 3.2, monoid form): an automorphism
`ζ ↦ ζ^a` of the cyclotome `μ_n` whose induced map `β ↦ β^a` on `H¹(G_K, μ_n)` fixes the Kummer
class of a uniformiser is the identity. -/
theorem kummer_rigidity {p : ℕ} [Fact p.Prime] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (a : ℤ) {π : Kˣ} (hπ : v p (π : K) = 1)
    (h : kummer n K Ω π ^ a = kummer n K Ω π) (ζ : Mu n Ω) : ζ ^ a = ζ := by
  have h1 : π ^ (a - 1) ∈ (kummer n K Ω).ker := by
    rw [MonoidHom.mem_ker, map_zpow, zpow_sub_one, h, mul_inv_cancel]
  rw [ker_kummer] at h1
  obtain ⟨y, hy⟩ := h1
  have hv := congrArg (fun z : Kˣ => v p (z : K)) hy
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val] at hv
  rw [v_pow y.ne_zero, v_zpow π.ne_zero, hπ, mul_one] at hv
  have hζn : ζ ^ n = 1 := by
    apply Mu.ext
    rw [map_pow, Mu.val_pow_n, map_one]
  rw [show a = (a - 1) + 1 by ring, zpow_add_one, ← hv, zpow_mul, zpow_natCast, hζn, one_zpow,
    one_mul]

/-- In particular, if `ζ ↦ ζ^a` fixes all Kummer classes, then it is the identity. -/
theorem kummer_rigidity' (p : ℕ) [Fact p.Prime] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    (a : ℤ) (h : ∀ x : Kˣ, kummer n K Ω x ^ a = kummer n K Ω x)
    (ζ : Mu n Ω) : ζ ^ a = ζ := by
  set π : Kˣ := Units.mk0 (uniformizer p K) (uniformizer_spec (p := p) (K := K)).ne_zero
  exact kummer_rigidity (p := p) a (π := π) uniformizer_spec (h π) ζ

end Rigidity

end Iut.Reconstruction
