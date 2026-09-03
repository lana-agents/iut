/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.Places
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.KrullTopology

/-!
# Places of number fields over places of subfields (taxis #1529, #1494)

For number fields `k ⊆ K`:

* `Iut.FinitePlace.exists_liesOver`: every finite place of `k` has a finite place of `K`
  over it (going up for the integral extension `𝓞_k ⊆ 𝓞_K`);
* `Iut.InfinitePlace.exists_liesOver`: every infinite place of `k` has an infinite place of
  `K` over it (extension of complex embeddings);
* `Iut.galPlace σ w`: the action of `σ ∈ Gal(K/k)` on the finite places of `K`
  (`σ·𝔓 = σ(𝔓)`, through the restriction of `σ` to `𝓞_K`), which preserves the place of
  `k` below (`Iut.galPlace_liesOver`);
* `Iut.decompGroup w`: the **decomposition group** of a finite place `w` of `K` in
  `Gal(F̄/K)` — the stabilizer of a prime of the integral closure of `𝓞_K` in `F̄` lying
  over `𝔓_w` — and its closedness in the Krull topology (`Iut.decompGroup_isClosed`).
-/

namespace Iut

open NumberField IsDedekindDomain

section Places

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

lemma algebraMap_ringOfIntegers_injective :
    Function.Injective (algebraMap (𝓞 k) (𝓞 K)) := by
  intro a b h
  have h' := congrArg (algebraMap (𝓞 K) K) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 k) k K, IsScalarTower.algebraMap_apply (𝓞 k) k K] at h'
  exact RingOfIntegers.coe_injective ((algebraMap k K).injective h')

/-- **Every finite place of `k` has a finite place of `K` over it.** -/
theorem FinitePlace.exists_liesOver (v : FinitePlace k) :
    ∃ w : FinitePlace K, FinitePlace.LiesOver w v := by
  haveI : v.maximalIdeal.asIdeal.IsPrime := v.maximalIdeal.isPrime
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    v.maximalIdeal.asIdeal ⊥ (by
      rw [Ideal.comap_bot_of_injective _ algebraMap_ringOfIntegers_injective]
      exact bot_le)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ algebraMap_ringOfIntegers_injective] at hQv
    exact v.maximalIdeal.ne_bot hQv.symm
  refine ⟨FinitePlace.mk ⟨Q, hQ, hQne⟩, ?_⟩
  unfold FinitePlace.LiesOver
  rw [FinitePlace.maximalIdeal_mk]
  exact ⟨hQv.symm⟩

/-- A number field is algebraic over any subfield (for any algebra structure). -/
instance numberField_isAlgebraic : Algebra.IsAlgebraic k K := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  constructor
  intro x
  obtain ⟨p, hp0, hpx⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
  refine ⟨p.map (algebraMap ℚ k), (Polynomial.map_ne_zero_iff (algebraMap ℚ k).injective).mpr hp0,
    ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    Subsingleton.elim ((algebraMap k K).comp (algebraMap ℚ k)) (algebraMap ℚ K),
    ← Polynomial.aeval_def, hpx]

/-- **Every infinite place of `k` has an infinite place of `K` over it.** -/
theorem InfinitePlace.exists_liesOver (v : InfinitePlace k) :
    ∃ w : InfinitePlace K, w.1.LiesOver v.1 := by
  obtain ⟨w, hw⟩ := NumberField.InfinitePlace.comap_surjective (k := k) (K := K) v
  exact ⟨w, ⟨by rw [← hw]; rfl⟩⟩

/-! ### The Galois action on finite places -/

/-- The restriction of `σ ∈ Gal(K/k)` to the rings of integers. -/
noncomputable def galRestrictInt (σ : K ≃ₐ[k] K) : 𝓞 K ≃ₐ[𝓞 k] 𝓞 K :=
  galRestrict (𝓞 k) k K (𝓞 K) σ

lemma coe_galRestrictInt (σ : K ≃ₐ[k] K) (x : 𝓞 K) :
    (galRestrictInt σ x : K) = σ (x : K) :=
  algebraMap_galRestrict_apply (A := 𝓞 k) (K := k) (L := K) (B := 𝓞 K) σ x

/-- **The action of `Gal(K/k)` on the finite places of `K`**: `σ·w` is the place of the
prime `σ(𝔓_w) = (σ⁻¹)⁻¹(𝔓_w)`. -/
noncomputable def galPlace (σ : K ≃ₐ[k] K) (w : FinitePlace K) : FinitePlace K :=
  FinitePlace.mk (HeightOneSpectrum.comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (galRestrictInt σ⁻¹).surjective w.maximalIdeal)

lemma galPlace_maximalIdeal (σ : K ≃ₐ[k] K) (w : FinitePlace K) :
    (galPlace σ w).maximalIdeal.asIdeal =
      w.maximalIdeal.asIdeal.comap (galRestrictInt σ⁻¹ : 𝓞 K →+* 𝓞 K) := by
  unfold galPlace
  rw [FinitePlace.maximalIdeal_mk]
  rfl

/-- **The action preserves the place below**, for places of any subfield `k₀ ⊆ k` (with
the algebra structure of `K` over `k₀` factoring through `k`). -/
theorem galPlace_liesOver {k₀ : Type*} [Field k₀] [NumberField k₀] [Algebra k₀ k] [Algebra k₀ K]
    (halg : ∀ x : k₀, algebraMap k₀ K x = algebraMap k K (algebraMap k₀ k x))
    (σ : K ≃ₐ[k] K) {w : FinitePlace K} {v : FinitePlace k₀}
    (hw : FinitePlace.LiesOver w v) : FinitePlace.LiesOver (galPlace σ w) v := by
  unfold FinitePlace.LiesOver at hw ⊢
  refine ⟨?_⟩
  rw [hw.over, galPlace_maximalIdeal, Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
  congr 1
  ext x
  rw [RingHom.comp_apply, RingHom.coe_coe, coe_galRestrictInt]
  have h : (algebraMap (𝓞 k₀) (𝓞 K) x : K) = algebraMap k K (algebraMap k₀ k (x : k₀)) := by
    rw [← halg]
    change algebraMap (𝓞 K) K (algebraMap (𝓞 k₀) (𝓞 K) x) = _
    rw [← IsScalarTower.algebraMap_apply (𝓞 k₀) (𝓞 K) K,
      IsScalarTower.algebraMap_apply (𝓞 k₀) k₀ K]
  rw [h, AlgEquiv.commutes]

/-! ### Decomposition groups -/

variable (K) (Fbar : Type*) [Field Fbar] [Algebra K Fbar]

/-- The integral closure of `𝓞_K` in `F̄`. -/
abbrev intClosure : Subalgebra (𝓞 K) Fbar := integralClosure (𝓞 K) Fbar

lemma algebraMap_intClosure_injective :
    Function.Injective (algebraMap (𝓞 K) (intClosure K Fbar)) := by
  intro a b h
  have h' := congrArg (algebraMap (intClosure K Fbar) Fbar) h
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 K) K Fbar, IsScalarTower.algebraMap_apply (𝓞 K) K Fbar] at h'
  exact RingOfIntegers.coe_injective ((algebraMap K Fbar).injective h')

/-- A prime of the integral closure of `𝓞_K` in `F̄` over `𝔓_w` exists. -/
theorem exists_prime_over (w : FinitePlace K) :
    ∃ Q : Ideal (intClosure K Fbar), Q.IsPrime ∧
      Q.comap (algebraMap (𝓞 K) (intClosure K Fbar)) = w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.IsPrime := w.maximalIdeal.isPrime
  obtain ⟨Q, -, hQ, hQw⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (S := intClosure K Fbar) w.maximalIdeal.asIdeal ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (algebraMap_intClosure_injective K Fbar)]
      exact bot_le)
  exact ⟨Q, hQ, hQw⟩

/-- A chosen prime of the integral closure over `𝔓_w`. -/
noncomputable def primeOver (w : FinitePlace K) : Ideal (intClosure K Fbar) :=
  (exists_prime_over K Fbar w).choose

lemma primeOver_isPrime (w : FinitePlace K) : (primeOver K Fbar w).IsPrime :=
  (exists_prime_over K Fbar w).choose_spec.1

lemma primeOver_comap (w : FinitePlace K) :
    (primeOver K Fbar w).comap (algebraMap (𝓞 K) (intClosure K Fbar)) =
      w.maximalIdeal.asIdeal :=
  (exists_prime_over K Fbar w).choose_spec.2

/-- The chosen prime over `𝔓_w`, as a set of elements of `F̄`. -/
def primeOverSet (w : FinitePlace K) : Set Fbar :=
  {x | ∃ hx : x ∈ intClosure K Fbar, (⟨x, hx⟩ : intClosure K Fbar) ∈ primeOver K Fbar w}

/-- **The decomposition group** of `w` in `Gal(F̄/K)`: the stabilizer of the chosen prime
of the integral closure of `𝓞_K` in `F̄` over `𝔓_w`. -/
def decompGroup (w : FinitePlace K) : Subgroup (Fbar ≃ₐ[K] Fbar) where
  carrier := {σ | ∀ x, x ∈ primeOverSet K Fbar w ↔ σ x ∈ primeOverSet K Fbar w}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {σ τ} hσ hτ x => by
    simp only [Set.mem_setOf_eq] at hσ hτ ⊢
    rw [AlgEquiv.mul_apply, ← hσ, ← hτ]
  inv_mem' := fun {σ} hσ x => by
    simp only [Set.mem_setOf_eq] at hσ ⊢
    have h := hσ (σ⁻¹ x)
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h
    exact h.symm

/-- The set of automorphisms sending `x` to `y` is open (Krull topology). -/
lemma isOpen_eval_eq [Algebra.IsIntegral K Fbar] (x y : Fbar) :
    IsOpen {σ : Fbar ≃ₐ[K] Fbar | σ x = y} := by
  by_cases h : ∃ σ₀ : Fbar ≃ₐ[K] Fbar, σ₀ x = y
  · obtain ⟨σ₀, hσ₀⟩ := h
    have hset : {σ : Fbar ≃ₐ[K] Fbar | σ x = y} =
        (fun σ => σ₀⁻¹ * σ) ⁻¹' (MulAction.stabilizer (Fbar ≃ₐ[K] Fbar) x) := by
      ext σ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
        AlgEquiv.smul_def, AlgEquiv.mul_apply]
      constructor
      · intro hσ
        rw [hσ, ← hσ₀, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
      · intro hσ
        have := congrArg σ₀ hσ
        rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hσ₀] at this
    rw [hset]
    exact (stabilizer_isOpen_of_isIntegral (K := K) x).preimage
      (continuous_const.mul continuous_id)
  · push_neg at h
    have : {σ : Fbar ≃ₐ[K] Fbar | σ x = y} = ∅ := by
      ext σ; simp [h σ]
    rw [this]
    exact isOpen_empty

/-- The set of automorphisms sending `x` into (resp. out of) a set is open. -/
lemma isOpen_eval_mem [Algebra.IsIntegral K Fbar] (x : Fbar) (S : Set Fbar) :
    IsOpen {σ : Fbar ≃ₐ[K] Fbar | σ x ∈ S} := by
  have : {σ : Fbar ≃ₐ[K] Fbar | σ x ∈ S} = ⋃ y ∈ S, {σ | σ x = y} := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    exact ⟨fun h => ⟨σ x, h, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact hy⟩
  rw [this]
  exact isOpen_biUnion fun y _ => isOpen_eval_eq K Fbar x y

/-- **Decomposition groups are closed** in the Krull topology. -/
theorem decompGroup_isClosed [Algebra.IsIntegral K Fbar] (w : FinitePlace K) :
    IsClosed ((decompGroup K Fbar w : Subgroup _) : Set (Fbar ≃ₐ[K] Fbar)) := by
  have : ((decompGroup K Fbar w : Subgroup _) : Set (Fbar ≃ₐ[K] Fbar)) =
      ⋂ x, {σ | x ∈ primeOverSet K Fbar w ↔ σ x ∈ primeOverSet K Fbar w} := by
    ext σ; simp [decompGroup]
  rw [this]
  refine isClosed_iInter fun x => ?_
  by_cases hx : x ∈ primeOverSet K Fbar w
  · have : {σ : Fbar ≃ₐ[K] Fbar | x ∈ primeOverSet K Fbar w ↔ σ x ∈ primeOverSet K Fbar w} =
        {σ | σ x ∈ primeOverSet K Fbar w} := by
      ext σ; simp [hx]
    rw [this, ← isOpen_compl_iff]
    have : {σ : Fbar ≃ₐ[K] Fbar | σ x ∈ primeOverSet K Fbar w}ᶜ =
        {σ | σ x ∈ (primeOverSet K Fbar w)ᶜ} := by ext σ; simp
    rw [this]
    exact isOpen_eval_mem K Fbar x _
  · have : {σ : Fbar ≃ₐ[K] Fbar | x ∈ primeOverSet K Fbar w ↔ σ x ∈ primeOverSet K Fbar w} =
        {σ | σ x ∈ (primeOverSet K Fbar w)ᶜ} := by
      ext σ; simp [hx]
    rw [this, ← isOpen_compl_iff]
    have : {σ : Fbar ≃ₐ[K] Fbar | σ x ∈ (primeOverSet K Fbar w)ᶜ}ᶜ =
        {σ | σ x ∈ primeOverSet K Fbar w} := by ext σ; simp
    rw [this]
    exact isOpen_eval_mem K Fbar x _

end Places

end Iut
