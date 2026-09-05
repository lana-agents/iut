/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.TwoAdic

/-!
# The conductor bounds for the Legendre curves

We prove `Iut.Tripod.LogCondGeHyp P` and `Iut.Tripod.LogCondLeHyp P`: the comparison of the
conductor degree `log(f_{F_tpd})` of the tripodal field `F_tpd = ℚ(λ)` away from `2ℓ`
(`Iut.logConductorDegOf`, over the places of `F_tpd` below the places of `F_λ` over
`V_mod^bad(ℓ)`) with the log-conductor `log-cond_{{0,1,∞}}(λ)` of the tripod
(`Iut.Tripod.logCond`, over the places of `ℚ(λ)` where `λ` meets `{0, 1, ∞}`).

Both are sums of `log N(𝔭)` normalized by `1/[ℚ(λ) : ℚ]`, over places of the isomorphic
fields `F_tpd ⊆ F_λ` and `ℚ(λ) ⊆ ℚ̄` (`Iut.Tripod.tpdEquiv`); transporting `log-cond` to
`F_tpd` (`Iut.Tripod.logCond_eq_sum_tpd`) it becomes the sum over the places `𝔭` of `F_tpd`
with `|λ|_𝔭 ≠ 1` or `|λ − 1|_𝔭 ≠ 1` (`Iut.Tripod.badT`). The comparison of the index sets
is the reduction theory of the Legendre curve `E_λ` with `j = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`
at the places `w` of `F_λ` over `𝔭`:

* a bad-tpd place `𝔭` has a multiplicative place `w` above it, so `v_w(j) > 1`, which forces
  `|λ|_𝔭 ≠ 1` or `|λ − 1|_𝔭 ≠ 1` (`Iut.Tripod.mem_badT_of_isBadTpdOf`); hence
  `log(f_{F_tpd}) ≤ log-cond(λ)` (`Iut.Tripod.logCondGe`);
* conversely, at a place `𝔭 ∈ badT` of residue characteristic `≠ 2, ℓ`, every place `w`
  of `F_λ` above has `v_w(j) > 1`, hence multiplicative reduction (stable reduction being
  given), so `w` lies over `V_mod^bad(ℓ)` and `𝔭` is bad-tpd
  (`Iut.Tripod.isBadTpdOf_of_mem_badT`); the remaining places of `badT` have residue
  characteristic `2` or `ℓ` and contribute at most `log 2 + log ℓ = log(2ℓ)`
  (`Iut.sum_log_absNorm_filter_le`); hence `log-cond(λ) ≤ log(f_{F_tpd}) + log(2ℓ)`
  (`Iut.Tripod.logCondLe`).
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section General

variable {T : Type*} [Field T] [NumberField T]

/-- `|y|_𝔭 = 1 ↔ v_𝔭(y) = 1`. -/
lemma FinitePlace.apply_eq_one_iff (𝔭 : FinitePlace T) (y : T) :
    𝔭 y = 1 ↔ 𝔭.maximalIdeal.valuation T y = 1 := by
  rw [← FinitePlace.norm_embedding_eq, norm_emb_eq_one_iff]

/-- `v_w(2) = 1` at a place of residue characteristic `≠ 2`. -/
lemma valuation_two_eq_one_of_ne {w : FinitePlace T} (h2 : residueChar w ≠ 2) :
    w.maximalIdeal.valuation T 2 = 1 := by
  have : (2 : T) = algebraMap (𝓞 T) T 2 := by rw [map_ofNat]
  rw [this, valuation_eq_one_iff_notMem, two_mem_maximalIdeal_iff]
  exact h2

/-- `∑_{𝔭 ∈ S, p_𝔭 = q} log N(𝔭) ≤ [T : ℚ]·log q` for every finite set `S` of places. -/
lemma sum_log_absNorm_filter_le (S : Finset (FinitePlace T)) (q : ℕ) :
    ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal) ≤
      Module.finrank ℚ T * Real.log q := by
  calc ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)
      = ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), (inertDeg T 𝔭 : ℝ) * Real.log q := by
        refine Finset.sum_congr rfl fun 𝔭 h𝔭 => ?_
        rw [Finset.mem_filter] at h𝔭
        rw [absNorm_eq_pow_residueChar, Nat.cast_pow, Real.log_pow, h𝔭.2]
    _ = (∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = q), (inertDeg T 𝔭 : ℝ)) * Real.log q := by
        rw [Finset.sum_mul]
    _ ≤ Module.finrank ℚ T * Real.log q := by
        refine mul_le_mul_of_nonneg_right ?_ (log_natCast_nonneg q)
        exact_mod_cast sum_inertDeg_filter_le S q

end General

end Iut

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve

variable (P : CurveProviders) (x : Pt)

/-! ### The bad places of `F_tpd` -/

/-- The places of `F_tpd` at which `λ` meets `{0, 1, ∞}`: `|λ|_𝔭 ≠ 1` or `|λ − 1|_𝔭 ≠ 1`
(`Iut.Tripod.badPlaces`, transported to `F_tpd ⊆ F_λ`). -/
def badT : Set (FinitePlace (tpd P x)) := {𝔭 | 𝔭 (genT P x) ≠ 1 ∨ 𝔭 (genT P x - 1) ≠ 1}

theorem mem_badT {𝔭 : FinitePlace (tpd P x)} :
    𝔭 ∈ badT P x ↔ 𝔭 (genT P x) ≠ 1 ∨ 𝔭 (genT P x - 1) ≠ 1 := Iff.rfl

/-- Only finitely many places of `F_tpd` are bad. -/
theorem badT_finite : (badT P x).Finite := by
  have h₁ := FinitePlace.hasFiniteMulSupport (genT_ne_zero P x)
  have h₂ := FinitePlace.hasFiniteMulSupport (genT_sub_one_ne_zero P x)
  refine (h₁.union h₂).subset fun 𝔭 h𝔭 => ?_
  rcases h𝔭 with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The bad places of `F_tpd` correspond to the bad places of `ℚ(λ)`. -/
theorem tpdPlace_mem_badPlaces_iff (𝔭 : FinitePlace (tpd P x)) :
    tpdPlace P x 𝔭 ∈ badPlaces x.1 ↔ 𝔭 ∈ badT P x := by
  rw [mem_badPlaces, mem_badT, tpdPlace_gen, tpdPlace_gen_sub_one]

open scoped Classical in
/-- **`log-cond_{{0,1,∞}}(λ)` as a sum over the bad places of `F_tpd`.** -/
theorem logCond_eq_sum_tpd :
    logCond x = (∑ 𝔭 ∈ (badT_finite P x).toFinset,
      Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)) / deg x.1 := by
  rw [logCond_eq_sum]
  congr 1
  symm
  refine Finset.sum_equiv (FinitePlace.mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1))
    (fun 𝔭 => ?_) (fun 𝔭 _ => ?_)
  · rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact (tpdPlace_mem_badPlaces_iff P x 𝔭).symm
  · rw [absNorm_tpdPlace]

/-! ### Bad-tpd places and bad places -/

/-- `v_𝔭(λ) = 1 ↔ v_w(λ) = 1` for `w ∣ 𝔭`. -/
theorem valuation_genC_eq_one_iff {w : FinitePlace (P.curve x).F} {𝔭 : FinitePlace (tpd P x)}
    (hw𝔭 : FinitePlace.LiesOver w 𝔭) :
    w.maximalIdeal.valuation _ (genC' P x) = 1 ↔ 𝔭.maximalIdeal.valuation _ (genT P x) = 1 := by
  rw [← algebraMap_genT, valuation_algebraMap_eq_one_iff hw𝔭]

/-- `v_𝔭(λ − 1) = 1 ↔ v_w(λ − 1) = 1` for `w ∣ 𝔭`. -/
theorem valuation_genC_sub_one_eq_one_iff {w : FinitePlace (P.curve x).F}
    {𝔭 : FinitePlace (tpd P x)} (hw𝔭 : FinitePlace.LiesOver w 𝔭) :
    w.maximalIdeal.valuation _ (genC' P x - 1) = 1 ↔
      𝔭.maximalIdeal.valuation _ (genT P x - 1) = 1 := by
  rw [← algebraMap_genT, ← map_one (algebraMap (tpd P x) (P.curve x).F), ← map_sub,
    valuation_algebraMap_eq_one_iff hw𝔭]

/-- **A bad-tpd place is a bad place**: a multiplicative place `w` of `F_λ` above `𝔭` has
`v_w(j) > 1`, which forces `|λ|_𝔭 ≠ 1` or `|λ − 1|_𝔭 ≠ 1`. -/
theorem mem_badT_of_isBadTpdOf {ℓ : ℕ} {𝔭 : FinitePlace (tpd P x)}
    (h : IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) 𝔭) : 𝔭 ∈ badT P x := by
  obtain ⟨w, hw, hw𝔭⟩ := h
  have hw𝔭' : FinitePlace.LiesOver w 𝔭 := hw𝔭
  have hmult : w ∈ (P.curve x).badAll := (P.curve x).mem_badAll_of_mem_badPlacesOver hw
  have hj : 1 < w.maximalIdeal.valuation _ (legendre (genC' P x)).j :=
    one_lt_valuation_j_of_mult (P.curve x).E w hmult
  have h' := ne_one_or_ne_one_of_one_lt_valuation_legendre_j (w.maximalIdeal.valuation _)
    (l := genC' P x) (valuation_256_le_one w) hj
  rw [mem_badT]
  simp only [ne_eq] at h' ⊢
  rw [FinitePlace.apply_eq_one_iff, FinitePlace.apply_eq_one_iff,
    ← valuation_genC_eq_one_iff P x hw𝔭', ← valuation_genC_sub_one_eq_one_iff P x hw𝔭']
  exact h'

/-- **A bad place of residue characteristic `≠ 2, ℓ` is bad-tpd**: every place `w` of `F_λ`
above `𝔭` has `v_w(j) > 1`, hence multiplicative reduction, hence lies over
`V_mod^bad(ℓ)`. -/
theorem isBadTpdOf_of_mem_badT {ℓ : ℕ} {𝔭 : FinitePlace (tpd P x)} (h : 𝔭 ∈ badT P x)
    (h2 : residueChar 𝔭 ≠ 2) (hℓ : residueChar 𝔭 ≠ ℓ) :
    IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) 𝔭 := by
  obtain ⟨w, hw𝔭⟩ := FinitePlace.exists_liesOver (K := (P.curve x).F) 𝔭
  have hp : residueChar w = residueChar 𝔭 := residueChar_eq_of_liesOver hw𝔭
  have hv2 : w.maximalIdeal.valuation _ (2 : (P.curve x).F) = 1 :=
    valuation_two_eq_one_of_ne (by rw [hp]; exact h2)
  have h' : w.maximalIdeal.valuation _ (genC' P x) ≠ 1 ∨
      w.maximalIdeal.valuation _ (genC' P x - 1) ≠ 1 := by
    rw [mem_badT] at h
    simp only [ne_eq] at h ⊢
    rw [valuation_genC_eq_one_iff P x hw𝔭, valuation_genC_sub_one_eq_one_iff P x hw𝔭,
      ← FinitePlace.apply_eq_one_iff, ← FinitePlace.apply_eq_one_iff]
    exact h
  have hj : 1 < w.maximalIdeal.valuation _ (P.curve x).E.j :=
    one_lt_valuation_legendre_j (w.maximalIdeal.valuation _) (l := genC' P x) hv2 h'
  have hmult : HasMultiplicativeReductionAt (P.curve x).E w :=
    (hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E w
      ((P.arith x).stable_reduction w)).mpr (not_le.mpr hj)
  refine ⟨w, ?_, hw𝔭⟩
  rw [(P.curve x).badPlacesOver_VBadOf (P.arith x)]
  exact ⟨hmult, by rw [hp]; exact h2, by rw [hp]; exact hℓ⟩

open scoped Classical in
/-- **`log(f_{F_tpd})` as a sum over the bad-tpd places** among the bad places of `F_tpd`. -/
theorem logConductorDegOf_eq_sum (ℓ : ℕ) :
    logConductorDegOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) =
      (∑ 𝔭 ∈ (badT_finite P x).toFinset.filter
        (fun 𝔭 => IsBadTpdOf (P.curve x).F (P.curve x).E ((P.curve x).VBadOf ℓ) 𝔭),
        Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)) / deg x.1 := by
  unfold logConductorDegOf
  rw [← finrank_tpd P x, Finset.sum_filter]
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := (badT_finite P x).toFinset)]
  intro 𝔭 h𝔭
  simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h𝔭
  rw [Finset.mem_coe, Set.Finite.mem_toFinset]
  exact mem_badT_of_isBadTpdOf P x h𝔭.1

/-! ### The conductor bounds -/

/-- **The conductor bound from below** (`LogCondGeHyp`): `log(f_{F_tpd}) ≤ log-cond(λ)`. -/
theorem logCondGe : LogCondGeHyp P := by
  intro x ℓ hℓ h7
  classical
  rw [logConductorDegOf_eq_sum P x ℓ, logCond_eq_sum_tpd P x]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun 𝔭 _ _ => Real.log_nonneg (one_le_absNorm_real 𝔭)

/-- **The conductor bound from above** (`LogCondLeHyp`):
`log-cond(λ) ≤ log(f_{F_tpd}) + log(2ℓ)`. -/
theorem logCondLe : LogCondLeHyp P := by
  intro x ℓ hℓ h7
  classical
  rw [logConductorDegOf_eq_sum P x ℓ, logCond_eq_sum_tpd P x]
  have hn : (0 : ℝ) < deg x.1 := deg_pos_real x.1
  rw [div_le_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne']
  set S := (badT_finite P x).toFinset with hS
  set g : FinitePlace (tpd P x) → ℝ := fun 𝔭 => Real.log (Ideal.absNorm 𝔭.maximalIdeal.asIdeal)
    with hg
  have hg0 : ∀ 𝔭, 0 ≤ g 𝔭 := fun 𝔭 => Real.log_nonneg (one_le_absNorm_real 𝔭)
  -- the bad places are bad-tpd, or of residue characteristic `2` or `ℓ`
  have hsub : S ⊆ S.filter (fun 𝔭 => IsBadTpdOf (P.curve x).F (P.curve x).E
      ((P.curve x).VBadOf ℓ) 𝔭) ∪ S.filter (fun 𝔭 => residueChar 𝔭 = 2) ∪
      S.filter (fun 𝔭 => residueChar 𝔭 = ℓ) := by
    intro 𝔭 h𝔭
    have h𝔭' : 𝔭 ∈ badT P x := by rwa [hS, Set.Finite.mem_toFinset] at h𝔭
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h2 : residueChar 𝔭 = 2
    · exact Or.inl (Or.inr ⟨h𝔭, h2⟩)
    by_cases hl : residueChar 𝔭 = ℓ
    · exact Or.inr ⟨h𝔭, hl⟩
    exact Or.inl (Or.inl ⟨h𝔭, isBadTpdOf_of_mem_badT P x h𝔭' h2 hl⟩)
  have h1 : ∑ 𝔭 ∈ S, g 𝔭 ≤
      ∑ 𝔭 ∈ S.filter (fun 𝔭 => IsBadTpdOf (P.curve x).F (P.curve x).E
        ((P.curve x).VBadOf ℓ) 𝔭), g 𝔭 +
      ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = 2), g 𝔭 +
      ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = ℓ), g 𝔭 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun 𝔭 _ _ => hg0 𝔭).trans ?_
    refine (sum_union_le_of_nonneg _ _ g hg0).trans ?_
    exact add_le_add (sum_union_le_of_nonneg _ _ g hg0) le_rfl
  have h2 : ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = 2), g 𝔭 ≤ deg x.1 * Real.log 2 := by
    have := sum_log_absNorm_filter_le S 2
    rwa [finrank_tpd, Nat.cast_ofNat] at this
  have h3 : ∑ 𝔭 ∈ S.filter (fun 𝔭 => residueChar 𝔭 = ℓ), g 𝔭 ≤ deg x.1 * Real.log ℓ := by
    have := sum_log_absNorm_filter_le S ℓ
    rwa [finrank_tpd] at this
  have hlog : Real.log (2 * (ℓ : ℝ)) = Real.log 2 + Real.log ℓ :=
    Real.log_mul two_ne_zero (by exact_mod_cast hℓ.ne_zero)
  rw [hlog]
  linarith

end Iut.Tripod
