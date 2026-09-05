/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.ResidueField
import Iut.Concrete.LocalConstruct.Admissible

/-!
# Least hull regions at a prime (taxis #4, #278)

**Existence of least hull regions** (IUT III, Remark 3.9.5(i); the field
`LocalTheory.exists_leastHull`): every admissible region `U` of a nonarchimedean packet is
contained in a least region `a·(R_I)^∼` with `a` a unit of the packet
(`exists_leastHull_finite`).

The proof is componentwise in the residue fields `L_𝔪` of the packet (`ResidueField.lean`):
the hull regions are the products of the closed balls of radii `‖a mod 𝔪‖`
(`mem_smul_integral_iff`), so the least one containing `U` is obtained by choosing, in each
`L_𝔪`, an element of least norm among those of norm at least `M_𝔪 = sup_{x ∈ U} ‖x mod 𝔪‖`
(`exists_least_resNorm_ge`, from the discreteness of the spectral norm). The supremum `M_𝔪`
is finite since `U` is bounded, and positive since a region of positive Haar measure is
not contained in the proper subspace `𝔪` of the packet (`haar_submodule_eq_zero`: proper
subspaces of a `ℚ_p`-vector space have Haar measure zero, by the argument of
`MeasureTheory.Measure.addHaar_submodule` with the bounded translates `n·x`, `n ∈ ℕ`).
-/

namespace Iut

namespace LocalConstruct

open NumberField MeasureTheory
open scoped Pointwise Function

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (p : Nat.Primes) (c : ι → Place K)

/-! ### Proper subspaces have Haar measure zero -/

/-- **A proper subspace of a nonarchimedean packet has Haar measure zero.** -/
theorem haar_submodule_eq_zero (S : Submodule ℚ_[p] (Tensor K (.finite p) c)) (hS : S ≠ ⊤) :
    haar (.finite p) c (S : Set (Tensor K (.finite p) c)) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hS
  set u : ℕ → Tensor K (.finite p) c := fun n => ((n : ℕ) : ℚ_[p]) • x with hu_def
  have hu : Bornology.IsBounded (Set.range u) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [hu_def, norm_smul]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact_mod_cast Padic.norm_int_le_one (n : ℤ)
  have hmeas : MeasurableSet (S : Set (Tensor K (.finite p) c)) :=
    (Submodule.closed_of_finiteDimensional S).measurableSet
  have hdisj : Pairwise (Disjoint on fun n => {u n} + (S : Set (Tensor K (.finite p) c))) := by
    intro n k hnk
    simp only [Function.onFun, Set.singleton_add, Set.image_add_left, Set.disjoint_left,
      Set.mem_preimage, SetLike.mem_coe]
    intro y hyn hyk
    have hmem : ((k : ℚ_[p]) - n) • x ∈ S := by
      have := S.sub_mem hyn hyk
      rw [neg_add_eq_sub, neg_add_eq_sub, sub_sub_sub_cancel_left] at this
      change (k : ℚ_[p]) • x - (n : ℚ_[p]) • x ∈ S at this
      rwa [← sub_smul] at this
    have hne : ((k : ℚ_[p]) - n) ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hnk.symm)
    apply hx
    have := S.smul_mem ((k : ℚ_[p]) - n)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have key : ∀ R : ℝ, haar (.finite p) c
      ((S : Set (Tensor K (.finite p) c)) ∩ Metric.closedBall 0 R) = 0 := by
    intro R
    set s := (S : Set (Tensor K (.finite p) c)) ∩ Metric.closedBall 0 R with hs
    have hsb : Bornology.IsBounded s := Metric.isBounded_closedBall.subset Set.inter_subset_right
    have hsm : MeasurableSet s := hmeas.inter Metric.isClosed_closedBall.measurableSet
    have hdisj' : Pairwise (Disjoint on fun n => {u n} + s) :=
      pairwise_disjoint_mono hdisj fun n => Set.add_subset_add subset_rfl Set.inter_subset_left
    by_contra h
    apply lt_irrefl (⊤ : ENNReal)
    calc (⊤ : ENNReal) = ∑' _ : ℕ, haar (.finite p) c s :=
          (ENNReal.tsum_const_eq_top_of_ne_zero h).symm
      _ = ∑' n : ℕ, haar (.finite p) c ({u n} + s) := by
          congr 1
          ext1 n
          simp only [Set.image_add_left, measure_preimage_add, Set.singleton_add]
      _ = haar (.finite p) c (⋃ n, {u n} + s) :=
          Eq.symm <| measure_iUnion hdisj' fun n => by
            have hm : Measurable fun y : Tensor K (.finite p) c => -u n + y :=
              (continuous_const.add continuous_id).measurable
            simpa only [Set.image_add_left, Set.singleton_add] using hm hsm
      _ = haar (.finite p) c (Set.range u + s) := by
          rw [← Set.iUnion_add, Set.iUnion_singleton_eq_range]
      _ < ⊤ := (hu.add hsb).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc haar (.finite p) c (S : Set (Tensor K (.finite p) c))
      ≤ ∑' n : ℕ, haar (.finite p) c
          ((S : Set (Tensor K (.finite p) c)) ∩ Metric.closedBall 0 n) := by
        conv_lhs => rw [← Metric.iUnion_inter_closedBall_nat (S : Set (Tensor K (.finite p) c)) 0]
        exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]

/-- A region of positive Haar measure has a point with nonzero residue at every maximal
ideal. -/
lemma exists_proj_ne_zero_of_haar_pos {U : Set (Tensor K (.finite p) c)}
    (hU : 0 < haar (.finite p) c U) (m : MaximalSpectrum (Tensor K (.finite p) c)) :
    ∃ x ∈ U, proj p c m x ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : U ⊆ (m.asIdeal.restrictScalars ℚ_[p] : Set (Tensor K (.finite p) c)) := by
    intro x hx
    have := h x hx
    rwa [proj_apply, Ideal.Quotient.eq_zero_iff_mem] at this
  have hne : m.asIdeal.restrictScalars ℚ_[p] ≠ ⊤ := by
    intro htop
    have h1 : (1 : Tensor K (.finite p) c) ∈ m.asIdeal := Submodule.eq_top_iff'.mp htop 1
    exact m.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact absurd hU (not_lt.mpr ((measure_mono hsub).trans
    (haar_submodule_eq_zero p c _ hne).le))

/-! ### Bounded regions have bounded residues -/

/-- The residues of a bounded region are uniformly bounded in norm. -/
lemma exists_forall_resNorm_proj_le {U : Set (Tensor K (.finite p) c)}
    (hU : Bornology.IsBounded U) :
    ∃ B : ℝ, ∀ x ∈ U, ∀ m, resNorm p c m (proj p c m x) ≤ B := by
  obtain ⟨R, hR⟩ := hU.subset_closedBall 0
  obtain ⟨r, hr, hsub⟩ := exists_closedBall_subset_integral p c
  have hp1 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : (p : ℕ).Prime).one_lt)
  have hp0 : 0 < ‖((p : ℕ) : ℚ_[p])‖ :=
    norm_pos_iff.mpr (by exact_mod_cast (Fact.out : (p : ℕ).Prime).ne_zero)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < r / (|R| + 1) by positivity) hp1
  set q : ℚ_[p] := ((p : ℕ) : ℚ_[p]) ^ n with hq
  have hq0 : 0 < ‖q‖ := by rw [hq, norm_pow]; exact pow_pos hp0 n
  refine ⟨‖q‖⁻¹, fun x hx m => ?_⟩
  have hxR : ‖x‖ ≤ |R| + 1 := by
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans ((le_abs_self R).trans (by linarith))
  have hmem : q • x ∈ integral p c := by
    refine hsub ?_
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hq, norm_pow]
    calc ‖((p : ℕ) : ℚ_[p])‖ ^ n * ‖x‖ ≤ r / (|R| + 1) * (|R| + 1) :=
          mul_le_mul hn.le hxR (norm_nonneg _) (by positivity)
      _ = r := div_mul_cancel₀ r (by positivity)
  have := mem_integral_iff_forall_resNorm_le_one.mp hmem m
  rw [map_smul, Algebra.smul_def, resNorm_mul, resNorm_algebraMap] at this
  calc resNorm p c m (proj p c m x) = ‖q‖⁻¹ * (‖q‖ * resNorm p c m (proj p c m x)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hq0.ne', one_mul]
    _ ≤ ‖q‖⁻¹ * 1 := mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hq0.le)
    _ = ‖q‖⁻¹ := mul_one _

/-! ### Least hull regions -/

/-- **Existence of least hull regions at a prime** (IUT III, Remark 3.9.5(i);
`LocalTheory.exists_leastHull` for the concrete packets): every admissible region `U` of a
nonarchimedean packet is contained in a least region `a·(R_I)^∼` with `a` a unit. -/
theorem exists_leastHull_finite {U : Set (Tensor K (.finite p) c)}
    (hU : U ∈ admissible (.finite p) c) :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧ U ⊆ a • integral p c ∧
      ∀ b : Tensor K (.finite p) c, IsUnit b → U ⊆ b • integral p c →
        a • integral p c ⊆ b • integral p c := by
  classical
  have hne := admissible_nonempty hU
  have hbdd : Bornology.IsBounded U :=
    (admissible_relCompact hU).isBounded.subset subset_closure
  obtain ⟨B, hB⟩ := exists_forall_resNorm_proj_le p c hbdd
  set M : ∀ m : MaximalSpectrum (Tensor K (.finite p) c), ℝ :=
    fun m => sSup ((fun x => resNorm p c m (proj p c m x)) '' U) with hM
  have hMbdd : ∀ m, BddAbove ((fun x => resNorm p c m (proj p c m x)) '' U) := fun m =>
    ⟨B, by rintro _ ⟨x, hx, rfl⟩; exact hB x hx m⟩
  have hMle : ∀ m, ∀ x ∈ U, resNorm p c m (proj p c m x) ≤ M m := fun m x hx =>
    le_csSup (hMbdd m) ⟨x, hx, rfl⟩
  have hMpos : ∀ m, 0 < M m := fun m => by
    obtain ⟨x, hx, hx0⟩ := exists_proj_ne_zero_of_haar_pos p c (admissible_haar_pos hU) m
    exact (resNorm_pos hx0).trans_le (hMle m x hx)
  have hMsup : ∀ m (t : ℝ), (∀ x ∈ U, resNorm p c m (proj p c m x) ≤ t) → M m ≤ t :=
    fun m t ht => csSup_le (hne.image _) (by rintro _ ⟨x, hx, rfl⟩; exact ht x hx)
  choose b hb0 hbM hbmin using fun m => exists_least_resNorm_ge (p := p) (c := c) (m := m)
    (hMpos m)
  obtain ⟨a, ha⟩ := exists_forall_proj_eq p c b
  have haU : IsUnit a := isUnit_iff_forall_proj_ne_zero.mpr fun m => (ha m).symm ▸ hb0 m
  refine ⟨a, haU, fun x hx => ?_, fun b' hb' hUb' => ?_⟩
  · rw [mem_smul_integral_iff haU]
    intro m
    rw [ha m]
    exact (hMle m x hx).trans (hbM m)
  · intro x hx
    rw [mem_smul_integral_iff haU] at hx
    rw [mem_smul_integral_iff hb']
    intro m
    refine (hx m).trans ?_
    rw [ha m]
    refine hbmin m _ (isUnit_iff_forall_proj_ne_zero.mp hb' m) (hMsup m _ fun y hy => ?_)
    exact (mem_smul_integral_iff hb').mp (hUb' hy) m

end LocalConstruct

end Iut
