/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.MaximalOrder

/-!
# The residue fields of a nonarchimedean tensor packet (taxis #4, #278)

A nonarchimedean packet `⊗_j K_{c j}` is a reduced Artinian ring, hence the product of its
residue fields `L_𝔪 = (⊗_j K_{c j}) ⧸ 𝔪` over the maximal ideals `𝔪` (`IsArtinianRing.equivPi`,
`residueEquiv`), each a finite extension of `ℚ_p`. This file equips every residue field with
the **spectral norm** (`resNorm`, Mathlib's `spectralNorm`: the unique multiplicative norm
extending the `p`-adic norm) and proves the description of the maximal order and of the hull
regions in these terms:

* `isIntegral_iff_resNorm_le_one`: the integral closure of `ℤ_p` in `L_𝔪` is the closed
  unit ball of the spectral norm, by the spectral value criterion
  (`spectralValue_le_one_iff`) applied to the minimal polynomial, whose coefficients lie in
  `ℤ_p` exactly for the integral elements (Gauss's lemma,
  `minpoly.isIntegrallyClosed_eq_field_fractions'`);
* `mem_integral_iff_forall_resNorm_le_one`: `(R_I)^∼ = {x | ∀ 𝔪, ‖x mod 𝔪‖ ≤ 1}`, i.e.
  `(R_I)^∼` is the product of the rings of integers of the residue fields;
* `isUnit_iff_forall_proj_ne_zero`: the units of the packet are the elements with nonzero
  image in every residue field;
* `mem_smul_integral_iff`: the hull region `a·(R_I)^∼` (`a` a unit) is the product of the
  closed balls of radii `‖a mod 𝔪‖`;
* `exists_resNorm_pow_eq_zpow`: **discreteness** of the spectral norm: `‖y‖^{n!} ∈ p^ℤ` for
  `y ≠ 0`, where `n = [L_𝔪 : ℚ_p]`, since `‖y‖^{deg f} = ‖f(0)‖` for the minimal polynomial
  `f` of `y` (`spectralNorm_eq_norm_coeff_zero_rpow`); hence `exists_least_resNorm_ge`:
  among the norms of nonzero elements which are `≥ M > 0` there is a least one.
-/

namespace Iut

namespace LocalConstruct

open NumberField Polynomial
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (p : Nat.Primes) (c : ι → Place K)

/-! ### The residue fields -/

/-- **The residue field** `L_𝔪` of the packet at a maximal ideal `𝔪`. -/
abbrev ResidueField (m : MaximalSpectrum (Tensor K (.finite p) c)) : Type u :=
  Tensor K (.finite p) c ⧸ m.asIdeal

variable (m : MaximalSpectrum (Tensor K (.finite p) c))

noncomputable instance instFieldResidueField : Field (ResidueField p c m) :=
  Ideal.Quotient.field m.asIdeal

instance instFiniteResidueField : Module.Finite ℚ_[p] (ResidueField p c m) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] m.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

instance instFreeResidueField : Module.Free ℚ_[p] (ResidueField p c m) :=
  Module.Free.of_divisionRing _ _

/-- The projection of the packet onto its residue field at `𝔪`. -/
noncomputable def proj : Tensor K (.finite p) c →ₐ[ℚ_[p]] ResidueField p c m :=
  Ideal.Quotient.mkₐ ℚ_[p] m.asIdeal

lemma proj_apply (x : Tensor K (.finite p) c) : proj p c m x = Ideal.Quotient.mk m.asIdeal x :=
  rfl

/-- **The residue-field decomposition** of the packet (a reduced Artinian ring). -/
noncomputable def residueEquiv :
    Tensor K (.finite p) c ≃ₐ[Tensor K (.finite p) c] ∀ m, ResidueField p c m :=
  IsArtinianRing.equivPi _

lemma residueEquiv_apply (x : Tensor K (.finite p) c) : residueEquiv p c x m = proj p c m x :=
  rfl

/-- Every family of residues is the family of residues of an element of the packet. -/
lemma exists_forall_proj_eq (b : ∀ m, ResidueField p c m) :
    ∃ a : Tensor K (.finite p) c, ∀ m, proj p c m a = b m :=
  ⟨(residueEquiv p c).symm b, fun m => congrFun ((residueEquiv p c).apply_symm_apply b) m⟩

/-! ### The spectral norm of a residue field -/

/-- **The spectral norm** of the residue field `L_𝔪`: the unique multiplicative norm
extending the `p`-adic norm of `ℚ_p`. -/
noncomputable def resNorm (y : ResidueField p c m) : ℝ :=
  spectralNorm ℚ_[p] (ResidueField p c m) y

variable {p c m}

lemma resNorm_nonneg (y : ResidueField p c m) : 0 ≤ resNorm p c m y := spectralNorm_nonneg y

lemma resNorm_zero : resNorm p c m 0 = 0 := spectralNorm_zero

lemma resNorm_one : resNorm p c m 1 = 1 := spectralNorm_one

lemma resNorm_mul (x y : ResidueField p c m) :
    resNorm p c m (x * y) = resNorm p c m x * resNorm p c m y :=
  spectralAlgNorm_mul x y

lemma resNorm_eq_zero_iff {y : ResidueField p c m} : resNorm p c m y = 0 ↔ y = 0 :=
  ⟨fun h => eq_zero_of_map_spectralNorm_eq_zero h (Algebra.IsAlgebraic.isAlgebraic y),
    fun h => h ▸ resNorm_zero⟩

lemma resNorm_pos {y : ResidueField p c m} (hy : y ≠ 0) : 0 < resNorm p c m y :=
  lt_of_le_of_ne (resNorm_nonneg y) (Ne.symm (mt resNorm_eq_zero_iff.mp hy))

lemma resNorm_algebraMap (k : ℚ_[p]) :
    resNorm p c m (algebraMap ℚ_[p] (ResidueField p c m) k) = ‖k‖ :=
  spectralNorm_extends k

lemma resNorm_inv (y : ResidueField p c m) : resNorm p c m y⁻¹ = (resNorm p c m y)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [inv_zero, resNorm_zero, inv_zero]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← resNorm_mul, inv_mul_cancel₀ hy, resNorm_one]

/-! ### The integrality criterion -/

/-- **The integral closure of `ℤ_p` in a residue field is the closed unit ball** of the
spectral norm. -/
theorem isIntegral_iff_resNorm_le_one (y : ResidueField p c m) :
    IsIntegral ℤ_[p] y ↔ resNorm p c m y ≤ 1 := by
  have hmonic : (minpoly ℚ_[p] y).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral y)
  constructor
  · intro hy
    unfold resNorm spectralNorm
    rw [spectralValue_le_one_iff hmonic, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hy]
    intro n
    rw [coeff_map, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  · intro hy
    unfold resNorm spectralNorm at hy
    rw [spectralValue_le_one_iff hmonic] at hy
    have hlift : minpoly ℚ_[p] y ∈ lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, hy n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hlift hmonic
    refine ⟨q, hqm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ_[p], hq]
    exact minpoly.aeval ℚ_[p] y

/-- An element of a finite product of algebras all of whose components are integral is
integral. -/
theorem isIntegral_pi {R : Type*} [CommRing R] {α : Type*} [Finite α] {A : α → Type*}
    [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)] (f : ∀ i, A i)
    (hf : ∀ i, IsIntegral R (f i)) : IsIntegral R f := by
  classical
  cases nonempty_fintype α
  rw [← Finset.univ_sum_single f]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨P, hP, hPf⟩ := hf i
  refine ⟨X * P, monic_X.mul hP, ?_⟩
  rw [eval₂_mul, eval₂_X]
  funext j
  by_cases hij : j = i
  · subst hij
    have hcomp : (Pi.evalRingHom A j).comp (algebraMap R (∀ i, A i)) = algebraMap R (A j) :=
      RingHom.ext fun _ => rfl
    change Pi.single j (f j) j * Pi.evalRingHom A j (eval₂ (algebraMap R (∀ i, A i))
      (Pi.single j (f j)) P) = 0
    rw [hom_eval₂, hcomp, Pi.evalRingHom_apply, Pi.single_eq_same, hPf]
    exact mul_zero _
  · change Pi.single i (f i) j * _ = 0
    rw [Pi.single_eq_of_ne hij, zero_mul]

/-- `(R_I)^∼` consists of the elements integral in every residue field. -/
theorem mem_integral_iff_forall_isIntegral {x : Tensor K (.finite p) c} :
    x ∈ integral p c ↔ ∀ m, IsIntegral ℤ_[p] (proj p c m x) := by
  constructor
  · intro hx m
    exact IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) (proj p c m).toRingHom
      (RingHom.ext fun _ => rfl) hx
  · intro hx
    have h1 : IsIntegral ℤ_[p] (residueEquiv p c x) := isIntegral_pi _ hx
    have hcomp : (algebraMap ℤ_[p] (Tensor K (.finite p) c)).comp (RingHom.id ℤ_[p]) =
        (residueEquiv p c).symm.toRingEquiv.toRingHom.comp
          (algebraMap ℤ_[p] (∀ m, ResidueField p c m)) := by
      ext r
      simp only [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, AlgEquiv.coe_ringEquiv]
      rw [eq_comm, (residueEquiv p c).symm_apply_eq]
      funext m
      rfl
    have h2 := IsIntegral.map_of_comp_eq (RingHom.id ℤ_[p]) _ hcomp h1
    rw [mem_integral]
    simpa using h2

/-- **`(R_I)^∼` is the product of the closed unit balls of the residue fields.** -/
theorem mem_integral_iff_forall_resNorm_le_one {x : Tensor K (.finite p) c} :
    x ∈ integral p c ↔ ∀ m, resNorm p c m (proj p c m x) ≤ 1 := by
  rw [mem_integral_iff_forall_isIntegral]
  exact forall_congr' fun m => isIntegral_iff_resNorm_le_one _

/-! ### Units and hull regions -/

/-- **The units of the packet** are the elements with nonzero residues. -/
theorem isUnit_iff_forall_proj_ne_zero {a : Tensor K (.finite p) c} :
    IsUnit a ↔ ∀ m, proj p c m a ≠ 0 := by
  constructor
  · intro ha m
    exact (ha.map (proj p c m)).ne_zero
  · intro h
    have : IsUnit (residueEquiv p c a) :=
      Pi.isUnit_iff.mpr fun m => isUnit_iff_ne_zero.mpr (h m)
    simpa using this.map (residueEquiv p c).symm

/-- **The hull regions `a·(R_I)^∼` are products of closed balls**: for a unit `a`,
`x ∈ a·(R_I)^∼` iff `‖x mod 𝔪‖ ≤ ‖a mod 𝔪‖` for every `𝔪`. -/
theorem mem_smul_integral_iff {a : Tensor K (.finite p) c} (ha : IsUnit a)
    {x : Tensor K (.finite p) c} :
    x ∈ a • integral p c ↔
      ∀ m, resNorm p c m (proj p c m x) ≤ resNorm p c m (proj p c m a) := by
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩ m
    rw [smul_eq_mul, map_mul, resNorm_mul]
    exact mul_le_of_le_one_right (resNorm_nonneg _)
      (mem_integral_iff_forall_resNorm_le_one.mp hy m)
  · intro h
    refine ⟨↑ha.unit⁻¹ * x, ?_, ?_⟩
    · rw [mem_integral_iff_forall_resNorm_le_one]
      intro m
      have hne : proj p c m a ≠ 0 := isUnit_iff_forall_proj_ne_zero.mp ha m
      have hinv : proj p c m ↑ha.unit⁻¹ = (proj p c m a)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul, ha.val_inv_mul, map_one]
      rw [map_mul, resNorm_mul, hinv, resNorm_inv, inv_mul_le_iff₀ (resNorm_pos hne), mul_one]
      exact h m
    · rw [smul_eq_mul, ← mul_assoc, ha.mul_val_inv, one_mul]

/-! ### Discreteness of the spectral norm -/

variable (p c m)

/-- The exponent `[L_𝔪 : ℚ_p]!`, a common multiple of the degrees of the elements of
`L_𝔪`. -/
noncomputable def resExp : ℕ := (Module.finrank ℚ_[p] (ResidueField p c m)).factorial

variable {p c m}

/-- **Discreteness**: `‖y‖^{[L_𝔪 : ℚ_p]!}` is an integral power of `p` for `y ≠ 0`. -/
theorem exists_resNorm_pow_eq_zpow {y : ResidueField p c m} (hy : y ≠ 0) :
    ∃ k : ℤ, resNorm p c m y ^ resExp p c m = (p : ℝ) ^ k := by
  set f := minpoly ℚ_[p] y with hf
  have hint : IsIntegral ℚ_[p] y := Algebra.IsIntegral.isIntegral y
  have hn : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have hpow : resNorm p c m y ^ f.natDegree = ‖f.coeff 0‖ := by
    unfold resNorm
    rw [spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow, one_div,
      Real.rpow_inv_natCast_pow (norm_nonneg _) hn]
  have h0 : f.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  obtain ⟨d, hd⟩ : f.natDegree ∣ resExp p c m :=
    Nat.dvd_factorial (minpoly.natDegree_pos hint) (minpoly.natDegree_le y)
  refine ⟨-(f.coeff 0).valuation * d, ?_⟩
  rw [hd, pow_mul, hpow, Padic.norm_eq_zpow_neg_valuation h0, ← zpow_natCast, ← zpow_mul]

/-- **Least norms**: among the nonzero elements of norm at least `M > 0` there is one of
least norm. -/
theorem exists_least_resNorm_ge {M : ℝ} (hM : 0 < M) :
    ∃ b : ResidueField p c m, b ≠ 0 ∧ M ≤ resNorm p c m b ∧
      ∀ y : ResidueField p c m, y ≠ 0 → M ≤ resNorm p c m y →
        resNorm p c m b ≤ resNorm p c m y := by
  classical
  set D := resExp p c m with hD
  have hD0 : D ≠ 0 := Nat.factorial_ne_zero _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : (p : ℕ).Prime).one_lt
  have hp0 : (0 : ℝ) < p := zero_lt_one.trans hp1
  let Z : ℤ → Prop := fun k => ∃ y : ResidueField p c m, y ≠ 0 ∧ M ≤ resNorm p c m y ∧
    resNorm p c m y ^ D = (p : ℝ) ^ k
  have hZne : ∃ k, Z k := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hp1
    set y : ResidueField p c m := algebraMap ℚ_[p] _ ((p : ℚ_[p]) ^ n)⁻¹ with hy
    have hy0 : y ≠ 0 := by
      rw [hy, _root_.map_ne_zero]
      exact inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : (p : ℕ).Prime).ne_zero))
    have hyn : resNorm p c m y = (p : ℝ) ^ n := by
      rw [hy, resNorm_algebraMap, norm_inv, norm_pow, Padic.norm_p, inv_pow, inv_inv]
    obtain ⟨k, hk⟩ := exists_resNorm_pow_eq_zpow (m := m) hy0
    exact ⟨k, y, hy0, hyn ▸ hn.le, hk⟩
  have hZbdd : ∃ k₀ : ℤ, ∀ k, Z k → k₀ ≤ k := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (pow_pos hM D)
      (inv_lt_one_of_one_lt₀ hp1 : (p : ℝ)⁻¹ < 1)
    refine ⟨-n, ?_⟩
    rintro k ⟨y, -, hMy, hk⟩
    have hlt : (p : ℝ) ^ (-(n : ℤ)) < (p : ℝ) ^ k := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, ← hk]
      exact hn.trans_le (pow_le_pow_left₀ hM.le hMy D)
    exact ((zpow_lt_zpow_iff_right₀ hp1).mp hlt).le
  obtain ⟨lb, ⟨b, hb0, hMb, hb⟩, hlb⟩ := Int.exists_least_of_bdd hZbdd hZne
  refine ⟨b, hb0, hMb, fun y hy0 hMy => ?_⟩
  obtain ⟨k, hk⟩ := exists_resNorm_pow_eq_zpow (m := m) hy0
  have hle : (p : ℝ) ^ lb ≤ (p : ℝ) ^ k := zpow_le_zpow_right₀ hp1.le (hlb k ⟨y, hy0, hMy, hk⟩)
  rw [← hb, ← hk] at hle
  exact (pow_le_pow_iff_left₀ (resNorm_nonneg _) (resNorm_nonneg _) hD0).mp hle

end LocalConstruct

end Iut
