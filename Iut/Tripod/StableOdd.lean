/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.CurveFacts
import Iut.Concrete.CurveArithmeticProved
import Iut.Cor312.ThetaData.ValuationTransfer

/-!
# Stable reduction of the Legendre curves at the places of odd residue characteristic

Let `F` be a number field and `w` a finite place of `F` with `w`-adic valuation `v`. A model
`E` over `F` is *good at `w`* if it is `w`-integral with `v(Δ) = 1`, and *multiplicative at `w`*
if it is `w`-integral with `v(Δ) < 1` and `v(c₄) = 1` (`Iut.IsGoodModel`, `Iut.IsMultModel`,
for an arbitrary valuation). Such a model is minimal over the completed integers, since a
change of variables `C` multiplies `Δ` by `u⁻¹²` and `c₄` by `u⁻⁴`
(`WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one`,
`WeierstrassCurve.isMinimal_of_valuation_c₄_eq_one`), so it witnesses Mathlib's
`HasGoodReduction`, resp. `HasMultiplicativeReduction`, and therefore
`Iut.HasStableReductionAt` (`Iut.hasStableReductionAt_of_isStableModel`).

For the Legendre curve `E_λ : y² = x(x − 1)(x − λ)`, with `Δ = 16 λ²(λ − 1)²` and
`c₄ = 16(λ² − λ + 1)`, at a place `w` of residue characteristic `≠ 2`:

* if `λ` is `w`-integral, the Legendre model is integral; it is good if `λ` and `λ − 1` are
  `w`-units, and multiplicative otherwise, since then `λ² − λ + 1` is a `w`-unit
  (`Iut.isStableModel_legendre`);
* if `λ` is not `w`-integral, the change of variables `x = λX`, `y = λ√λ Y` (which needs
  `√λ ∈ F`) transforms `E_λ` into the Legendre curve `E_{1/λ}` (`Iut.legendre_variableChange`),
  whose parameter `1/λ` is `w`-integral and non-unit: multiplicative
  (`Iut.hasStableReductionAt_legendre`).

Since `√λ ∈ F_λ`, the curve `E_λ/F_λ` of a point of the tripod has stable reduction at every
place of odd residue characteristic (`Iut.Tripod.stable_reduction_of_residueChar_ne_two`).
The places of residue characteristic `2` are treated in `Iut.Tripod.StableTwo`.
-/

namespace WeierstrassCurve

/-! ## Minimality of an integral model with a unit discriminant or a unit `c₄` -/

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

/-- The discriminant of an integral model has valuation `≤ 1`. -/
lemma valuation_Δ_le_one_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.Δ ≤ 1 := by
  rw [← integralModel_Δ_eq R W]
  exact valuation_le_one _ _

/-- The invariant `c₄` of an integral model has valuation `≤ 1`. -/
lemma valuation_c₄_le_one_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    valuation K (maximalIdeal R) W.c₄ ≤ 1 := by
  rw [← integralModel_c₄_eq R W]
  exact valuation_le_one _ _

/-- An integral model whose discriminant is a unit is minimal: every integral model has
`v(Δ) ≤ 1`. -/
lemma isMinimal_of_valuation_Δ_eq_one (W : WeierstrassCurve K) [hW : IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simp only [one_smul]; exact hW, fun C hC _ => ?_⟩⟩
  simp only [one_smul] at hC ⊢
  haveI := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, h]
  exact valuation_Δ_le_one_of_isIntegral R (C • W)

/-- An integral model whose invariant `c₄` is a unit is minimal: for an integral model
`C • W`, `v(u⁻¹)⁴ = v(c₄(C • W)) ≤ 1` forces `v(u⁻¹) ≤ 1`, hence
`v(Δ(C • W)) = v(u⁻¹)¹² v(Δ(W)) ≤ v(Δ(W))`. -/
lemma isMinimal_of_valuation_c₄_eq_one (W : WeierstrassCurve K) [hW : IsIntegral R W]
    (h : valuation K (maximalIdeal R) W.c₄ = 1) : IsMinimal R W := by
  refine ⟨⟨by simp only [one_smul]; exact hW, fun C hC _ => ?_⟩⟩
  simp only [one_smul] at hC ⊢
  haveI := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ, map_mul, map_pow]
  have hu : valuation K (maximalIdeal R) (C.u⁻¹ : Kˣ) ≤ 1 := by
    have hc := valuation_c₄_le_one_of_isIntegral R (C • W)
    rw [variableChange_c₄, map_mul, map_pow, h, mul_one] at hc
    exact (pow_le_one_iff_of_nonneg zero_le (by norm_num)).mp hc
  exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hu)

end Minimal

end WeierstrassCurve

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WeierstrassCurve
open scoped WithZero

/-! ## Good and multiplicative models for a valuation -/

section Models

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ) (E : WeierstrassCurve K)

/-- The model `E` is integral for the valuation `v`: `v(aᵢ) ≤ 1`. -/
def IsIntegralModel : Prop :=
  v E.a₁ ≤ 1 ∧ v E.a₂ ≤ 1 ∧ v E.a₃ ≤ 1 ∧ v E.a₄ ≤ 1 ∧ v E.a₆ ≤ 1

/-- The model `E` is good for `v`: integral with a unit discriminant. -/
def IsGoodModel : Prop := IsIntegralModel v E ∧ v E.Δ = 1

/-- The model `E` is multiplicative for `v`: integral with a non-unit discriminant and a
unit `c₄`. -/
def IsMultModel : Prop := IsIntegralModel v E ∧ v E.Δ < 1 ∧ v E.c₄ = 1

/-- The model `E` is good or multiplicative for `v`. -/
def IsStableModel : Prop := IsGoodModel v E ∨ IsMultModel v E

variable {v E}

lemma IsIntegralModel.b₂ (h : IsIntegralModel v E) : v E.b₂ ≤ 1 := by
  obtain ⟨h₁, h₂, -, -, -⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem _ 4) h₂)

lemma IsIntegralModel.b₄ (h : IsIntegralModel v E) : v E.b₄ ≤ 1 := by
  obtain ⟨h₁, -, h₃, h₄, -⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (mul_mem (ofNat_mem _ 2) h₄) (mul_mem h₁ h₃)

lemma IsIntegralModel.b₆ (h : IsIntegralModel v E) : v E.b₆ ≤ 1 := by
  obtain ⟨-, -, h₃, -, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem _ 4) h₆)

lemma IsIntegralModel.b₈ (h : IsIntegralModel v E) : v E.b₈ ≤ 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := h
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem h₁ 2) h₆)
    (mul_mem (mul_mem (ofNat_mem _ 4) h₂) h₆)) (mul_mem (mul_mem h₁ h₃) h₄))
    (mul_mem h₂ (pow_mem h₃ 2))) (pow_mem h₄ 2)

lemma IsIntegralModel.c₄ (h : IsIntegralModel v E) : v E.c₄ ≤ 1 := by
  have h₂ := h.b₂
  have h₄ := h.b₄
  rw [← Valuation.mem_integer_iff] at *
  exact sub_mem (pow_mem h₂ 2) (mul_mem (ofNat_mem _ 24) h₄)

lemma IsIntegralModel.Δ (h : IsIntegralModel v E) : v E.Δ ≤ 1 := by
  have h₂ := h.b₂
  have h₄ := h.b₄
  have h₆ := h.b₆
  have h₈ := h.b₈
  rw [← Valuation.mem_integer_iff] at *
  exact add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem h₂ 2)) h₈)
    (mul_mem (ofNat_mem _ 8) (pow_mem h₄ 3))) (mul_mem (ofNat_mem _ 27) (pow_mem h₆ 2)))
    (mul_mem (mul_mem (mul_mem (ofNat_mem _ 9) h₂) h₄) h₆)

end Models

/-! ## From a stable model to stable reduction at a place -/

section Place

variable {F : Type*} [Field F] [NumberField F] (E : WeierstrassCurve F) (w : FinitePlace F)

/-- An element `y ∈ F` with `v_w(y) ≤ 1` lies in `𝒪_w`. -/
lemma exists_adicCompletionIntegers_eq {y : F} (hy : w.maximalIdeal.valuation F y ≤ 1) :
    ∃ r : w.maximalIdeal.adicCompletionIntegers F,
      algebraMap (w.maximalIdeal.adicCompletionIntegers F) (localCompletion w) r =
        FinitePlace.embedding w.maximalIdeal y :=
  (valued_le_one_iff_range w _).1
    (by rw [FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']; exact hy)

/-- A `w`-integral model is integral over `𝒪_w` after base change to `F_w`. -/
lemma isIntegral_baseChange_of_isIntegralModel
    (h : IsIntegralModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (localCompletion w)).IsIntegral (w.maximalIdeal.adicCompletionIntegers F) := by
  rw [baseChange_adicCompletion_eq]
  exact isIntegral_of_exists_lift _ (exists_adicCompletionIntegers_eq w h.1)
    (exists_adicCompletionIntegers_eq w h.2.1) (exists_adicCompletionIntegers_eq w h.2.2.1)
    (exists_adicCompletionIntegers_eq w h.2.2.2.1) (exists_adicCompletionIntegers_eq w h.2.2.2.2)

/-- A good model at `w` has good reduction over `𝒪_w` in Mathlib's sense. -/
lemma hasGoodReduction_baseChange_of_isGoodModel
    (h : IsGoodModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (localCompletion w)).HasGoodReduction
      (w.maximalIdeal.adicCompletionIntegers F) := by
  haveI := isIntegral_baseChange_of_isIntegralModel E w h.1
  have hΔ : IsDedekindDomain.HeightOneSpectrum.valuation (localCompletion w)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (localCompletion w)).Δ = 1 := by
    rw [baseChange_adicCompletion_eq, map_Δ, valuation_eq_one_iff, norm_emb_eq_one_iff]
    exact h.2
  exact (hasGoodReduction_iff _ _).mpr ⟨isMinimal_of_valuation_Δ_eq_one _ _ hΔ, hΔ⟩

/-- A multiplicative model at `w` has multiplicative reduction over `𝒪_w` in Mathlib's sense. -/
lemma hasMultiplicativeReduction_baseChange_of_isMultModel
    (h : IsMultModel (w.maximalIdeal.valuation F) E) :
    (E.baseChange (localCompletion w)).HasMultiplicativeReduction
      (w.maximalIdeal.adicCompletionIntegers F) := by
  haveI := isIntegral_baseChange_of_isIntegralModel E w h.1
  have hc₄ : IsDedekindDomain.HeightOneSpectrum.valuation (localCompletion w)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (localCompletion w)).c₄ = 1 := by
    rw [baseChange_adicCompletion_eq, map_c₄, valuation_eq_one_iff, norm_emb_eq_one_iff]
    exact h.2.2
  have hΔ : IsDedekindDomain.HeightOneSpectrum.valuation (localCompletion w)
      (IsDiscreteValuationRing.maximalIdeal (w.maximalIdeal.adicCompletionIntegers F))
      (E.baseChange (localCompletion w)).Δ < 1 := by
    rw [baseChange_adicCompletion_eq, map_Δ, valuation_lt_one_iff, norm_emb_lt_one_iff]
    exact h.2.1
  exact (hasMultiplicativeReduction_iff _ _).mpr ⟨isMinimal_of_valuation_c₄_eq_one _ _ hc₄, hΔ, hc₄⟩

/-- **Stable reduction from a stable model**: if some change of variables `C • E` is a good or
multiplicative model at `w`, then `E` has stable reduction at `w`. -/
lemma hasStableReductionAt_of_isStableModel (C : VariableChange F)
    (h : IsStableModel (w.maximalIdeal.valuation F) (C • E)) : HasStableReductionAt E w := by
  rcases h with h | h
  · exact Or.inl ⟨C, hasGoodReduction_baseChange_of_isGoodModel _ w h⟩
  · exact Or.inr ⟨C, hasMultiplicativeReduction_baseChange_of_isMultModel _ w h⟩

/-- `v_w(q) = 1` for a prime `q` iff the residue characteristic of `w` is not `q`. -/
lemma valuation_natCast_eq_one_iff {q : ℕ} (hq : q.Prime) :
    w.maximalIdeal.valuation F (q : F) = 1 ↔ residueChar w ≠ q := by
  have h1 : w.maximalIdeal.valuation F (q : F) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F)]
    exact valuation_le_one (K := F) w.maximalIdeal _
  have h2 : w.maximalIdeal.valuation F (q : F) < 1 ↔ residueChar w = q := by
    rw [← natCast_mem_maximalIdeal_iff w hq, ← valuation_lt_one_iff_mem (K := F)]
    have e : algebraMap (𝓞 F) F (q : 𝓞 F) = (q : F) := map_natCast _ _
    rw [← e]
  constructor
  · intro h hc
    exact (h2.2 hc).ne h
  · intro h
    exact h1.antisymm (not_lt.1 fun hlt => h (h2.1 hlt))

/-- `v_w(2) = 1` at a place of odd residue characteristic. -/
lemma valuation_two_eq_one (hw : residueChar w ≠ 2) : w.maximalIdeal.valuation F 2 = 1 := by
  have := (valuation_natCast_eq_one_iff w Nat.prime_two).2 hw
  rwa [Nat.cast_ofNat] at this

/-- `v_w(3) = 1` at a place of residue characteristic `≠ 3`. -/
lemma valuation_three_eq_one (hw : residueChar w ≠ 3) : w.maximalIdeal.valuation F 3 = 1 := by
  have := (valuation_natCast_eq_one_iff w Nat.prime_three).2 hw
  rwa [Nat.cast_ofNat] at this

end Place

/-! ## The Legendre model at a place of odd residue characteristic -/

section Legendre

open Iut.Tripod

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation K Γ)

/-- The Legendre model of an integral parameter is integral. -/
lemma isIntegralModel_legendre {l : K} (hl : v l ≤ 1) : IsIntegralModel v (legendre l) := by
  refine ⟨by simp, ?_, by simp, hl, by simp⟩
  rw [legendre_a₂, ← Valuation.mem_integer_iff] at *
  exact neg_mem (add_mem (one_mem _) hl)

/-- `v(λ² − λ + 1) = 1` if `v(λ) < 1`. -/
lemma valuation_sq_sub_add_one_eq_one_of_lt {l : K} (hl : v l < 1) : v (l ^ 2 - l + 1) = 1 := by
  have h : v (l ^ 2 - l) < v 1 := by
    rw [map_one]
    refine lt_of_le_of_lt (Valuation.map_sub v _ _) (max_lt ?_ hl)
    rw [map_pow]
    exact pow_lt_one₀ zero_le hl (by norm_num)
  rw [Valuation.map_add_eq_of_lt_right v h, map_one]

/-- `v(λ² − λ + 1) = 1` if `v(λ) ≤ 1` and `v(λ − 1) < 1`. -/
lemma valuation_sq_sub_add_one_eq_one_of_sub_lt {l : K} (hl : v l ≤ 1) (hl1 : v (l - 1) < 1) :
    v (l ^ 2 - l + 1) = 1 := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  have h : v (l * (l - 1)) < v 1 := by
    rw [map_one, map_mul]
    exact (mul_le_of_le_one_left zero_le hl).trans_lt hl1
  rw [e, Valuation.map_add_eq_of_lt_right v h, map_one]

/-- **The Legendre model at a place of odd residue characteristic** (`v(2) = 1`) with
`v(λ) ≤ 1`: it is good if `λ` and `λ − 1` are units, and multiplicative otherwise (for
`λ ∈ {0, 1}` the model is degenerate, with `Δ = 0`, and the predicate is vacuous). -/
lemma isStableModel_legendre (h2 : v 2 = 1) {l : K} (hl : v l ≤ 1) :
    IsStableModel v (legendre l) := by
  have h16 : v 16 = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, map_pow, h2, one_pow]
  have hint := isIntegralModel_legendre v hl
  have hl1 : v (l - 1) ≤ 1 := by
    rw [← Valuation.mem_integer_iff] at *
    exact sub_mem hl (one_mem _)
  have hΔ : v (legendre l).Δ = v l ^ 2 * v (l - 1) ^ 2 := by
    rw [legendre_Δ, map_mul, map_mul, map_pow, map_pow, h16, one_mul]
  by_cases hu : v l = 1 ∧ v (l - 1) = 1
  · left
    refine ⟨hint, ?_⟩
    rw [hΔ, hu.1, hu.2, one_pow, one_mul]
  · right
    refine ⟨hint, ?_, ?_⟩
    · rw [hΔ]
      rcases not_and_or.mp hu with h | h
      · have hlt : v l < 1 := lt_of_le_of_ne hl h
        exact (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hl1)).trans_lt
          (pow_lt_one₀ zero_le hlt (by norm_num))
      · have hlt : v (l - 1) < 1 := lt_of_le_of_ne hl1 h
        exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hl)).trans_lt
          (pow_lt_one₀ zero_le hlt (by norm_num))
    · rw [legendre_c₄, map_mul, h16, one_mul]
      rcases not_and_or.mp hu with h | h
      · exact valuation_sq_sub_add_one_eq_one_of_lt v (lt_of_le_of_ne hl h)
      · exact valuation_sq_sub_add_one_eq_one_of_sub_lt v hl (lt_of_le_of_ne hl1 h)

/-- **The change of variables `x = λX`, `y = λ√λ Y`** (`u = √λ`) transforms the Legendre
curve `E_λ` into `E_{1/λ}`. -/
lemma legendre_variableChange {s l : K} (hs : s ^ 2 = l) (hs0 : s ≠ 0) :
    (⟨Units.mk0 s hs0, 0, 0, 0⟩ : VariableChange K) • legendre l = legendre l⁻¹ := by
  subst hs
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, legendre_a₁, legendre_a₂, legendre_a₃, legendre_a₄, legendre_a₆,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  · ring
  · field_simp
    ring
  · ring
  · field_simp
    ring
  · ring

end Legendre

section LegendrePlace

open Iut.Tripod

variable {F : Type*} [Field F] [NumberField F] (w : FinitePlace F)

/-- **Stable reduction of a Legendre curve at a place of odd residue characteristic**, for a
parameter `λ ≠ 0` with `√λ ∈ F`: the Legendre model itself if `λ` is `w`-integral, the
model `E_{1/λ}` otherwise. -/
theorem hasStableReductionAt_legendre (hw : residueChar w ≠ 2) {l : F} (h0 : l ≠ 0) {s : F}
    (hs : s ^ 2 = l) : HasStableReductionAt (legendre l) w := by
  have h2 := valuation_two_eq_one w hw
  by_cases hl : w.maximalIdeal.valuation F l ≤ 1
  · refine hasStableReductionAt_of_isStableModel _ w 1 ?_
    rw [one_smul]
    exact isStableModel_legendre _ h2 hl
  · have hs0 : s ≠ 0 := by
      rintro rfl
      exact h0 (by rw [← hs]; ring)
    refine hasStableReductionAt_of_isStableModel _ w ⟨Units.mk0 s hs0, 0, 0, 0⟩ ?_
    rw [legendre_variableChange hs hs0]
    refine isStableModel_legendre _ h2 ?_
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hl))

end LegendrePlace

end Iut

namespace Iut.Tripod

open NumberField WeierstrassCurve

/-- **Stable reduction of `E_λ/F_λ` at the places of odd residue characteristic**: `√λ ∈ F_λ`. -/
theorem stable_reduction_of_residueChar_ne_two (x : Pt) (h3 : TorsionFinite x.1 3)
    (h5 : TorsionFinite x.1 5) (w : FinitePlace (curveOf x h3 h5).F) (hw : residueChar w ≠ 2) :
    HasStableReductionAt (curveOf x h3 h5).E w :=
  hasStableReductionAt_legendre w hw (gen'_ne_zero x.2.1) (sqrtLam'_sq x.1)

end Iut.Tripod
