/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.UnitBall

/-!
# The canonical discrete valuation of a `p`-adic field (roadmap MR11)

A field `K` finite over `ℚ_p` (the framework of `local-class-field-theory`) carries a canonical
discrete valuation `PadicField.v p : K → ℤ`. We package it as a `Valued K ℤᵐ⁰` structure with a
rank-one structure and prove that it is complete, **with norm equal to the spectral norm**
`PadicField.nrm p K` (`norm_padicValued`). These are definitions (`padicValued`,
`padicRankOne`), to be used with `letI` for fields that do not carry a valuation yet (e.g. the
finite subextensions of an algebraic closure, `LogShellGalois.lean`), so that the `p`-adic
logarithm of `padic-log-volume` and the log-shell `Iut.logShell` of IUT III, Definition 1.1,
are available for every finite extension of `ℚ_p`.

We also show that every `ℚ_p`-algebra homomorphism between two such fields is continuous for any
choice of `Valued ℤᵐ⁰` structures with rank one (`continuous_algHom_auto`, from `hball_auto`).
-/

namespace Iut.Reconstruction

open PadicField
open scoped Valued NNReal WithZero

set_option linter.unusedSectionVars false

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

open Classical in
variable (p K) in
/-- The normalised valuation `x ↦ exp(−v(x))` with values in `ℤᵐ⁰`. -/
def vZ : Valuation K ℤᵐ⁰ where
  toFun x := if x = 0 then 0 else ((Multiplicative.ofAdd (-(v p x)) : Multiplicative ℤ) : ℤᵐ⁰)
  map_zero' := if_pos rfl
  map_one' := by simp
  map_mul' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    rw [if_neg (mul_ne_zero hx hy), if_neg hx, if_neg hy, v_mul hx hy, ← WithZero.coe_mul,
      ← ofAdd_add, neg_add]
  map_add_le_max' x y := by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    by_cases hxy : x + y = 0
    · simp [hxy]
    rw [if_neg hxy, if_neg hx, if_neg hy, le_max_iff, WithZero.coe_le_coe, WithZero.coe_le_coe,
      Multiplicative.ofAdd_le, Multiplicative.ofAdd_le, neg_le_neg_iff, neg_le_neg_iff]
    rcases le_total (nrm p K y) (nrm p K x) with h | h
    · left
      have h1 : nrm p K (x + y) ≤ nrm p K x := (nrm_add_le_max x y).trans (max_le le_rfl h)
      exact (nrm_le_iff_v_le hxy hx).1 h1
    · right
      have h1 : nrm p K (x + y) ≤ nrm p K y := (nrm_add_le_max x y).trans (max_le h le_rfl)
      exact (nrm_le_iff_v_le hxy hy).1 h1

theorem vZ_apply {x : K} (hx : x ≠ 0) :
    vZ p K x = ((Multiplicative.ofAdd (-(v p x)) : Multiplicative ℤ) : ℤᵐ⁰) := by
  classical
  exact if_neg hx

variable (p K) in
/-- The base `‖π‖⁻¹ > 1` of the norm. -/
def nrmBase : ℝ≥0 := ⟨(nrm p K (uniformizer p K))⁻¹, inv_nonneg.2 (nrm_nonneg _)⟩

theorem nrm_uniformizer_pos : 0 < nrm p K (uniformizer p K) :=
  nrm_pos_iff.2 (uniformizer_spec (p := p) (K := K)).ne_zero

theorem nrm_uniformizer_lt_one : nrm p K (uniformizer p K) < 1 :=
  (nrm_lt_one_iff_v_pos (uniformizer_spec (p := p) (K := K)).ne_zero).2
    (by rw [uniformizer_spec (p := p) (K := K)]; exact one_pos)

theorem one_lt_nrmBase : 1 < nrmBase p K := by
  change (1 : ℝ) < (nrm p K (uniformizer p K))⁻¹
  exact one_lt_inv₀ nrm_uniformizer_pos |>.2 nrm_uniformizer_lt_one

variable (p K) in
/-- **The canonical `Valued K ℤᵐ⁰` structure** of a finite extension of `ℚ_p`. -/
@[implicit_reducible]
def padicValued : Valued K ℤᵐ⁰ := Valued.mk' (vZ p K)

variable (p K) in
/-- Its rank-one structure, normalised so that the norm is the spectral norm. -/
@[implicit_reducible]
def padicRankOne :
    letI := padicValued p K
    Valuation.RankOne (Valued.v : Valuation K ℤᵐ⁰) :=
  letI := padicValued p K
  { hom' := (WithZeroMulInt.toNNReal (one_lt_nrmBase (p := p) (K := K)).ne_zero).comp
      MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := (WithZeroMulInt.toNNReal_strictMono one_lt_nrmBase).comp
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    exists_val_nontrivial := by
      refine ⟨uniformizer p K, ?_, ?_⟩
      · change vZ p K _ ≠ 0
        rw [vZ_apply (uniformizer_spec (p := p) (K := K)).ne_zero]
        exact WithZero.coe_ne_zero
      · change vZ p K _ ≠ 1
        rw [vZ_apply (uniformizer_spec (p := p) (K := K)).ne_zero, uniformizer_spec, ← WithZero.coe_one,
          Ne, WithZero.coe_inj]
        decide }

/-- **The norm of the canonical valuation is the spectral norm.** -/
theorem norm_padicValued (x : K) :
    letI := padicValued p K
    letI := padicRankOne p K
    ‖x‖ = nrm p K x := by
  letI := padicValued p K
  letI := padicRankOne p K
  by_cases hx : x = 0
  · simp [hx]
  rw [Valued.toNormedField.norm_def]
  change ((WithZeroMulInt.toNNReal (one_lt_nrmBase (p := p) (K := K)).ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict x)) : ℝ≥0) : ℝ) = _
  rw [Valuation.restrict_def, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
  change ((WithZeroMulInt.toNNReal _ (vZ p K x) : ℝ≥0) : ℝ) = _
  rw [WithZeroMulInt.toNNReal_neg_apply _ (by rw [vZ_apply hx]; exact WithZero.coe_ne_zero)]
  simp only [vZ_apply hx, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow]
  rw [nrm_eq_nrm_uniformizer_zpow uniformizer_spec hx]
  change ((nrm p K (uniformizer p K))⁻¹ : ℝ) ^ (-v p x) = _
  rw [inv_zpow', neg_neg]

theorem completeSpace_of_dist_eq {X : Type*} (m₁ m₂ : PseudoMetricSpace X)
    (h : ∀ x y, m₁.dist x y = m₂.dist x y) [hc : @CompleteSpace X m₂.toUniformSpace] :
    @CompleteSpace X m₁.toUniformSpace := by
  have : m₁ = m₂ := PseudoMetricSpace.ext (by ext x y; exact h x y)
  subst this
  exact hc

/-- **The canonical valuation is complete.** -/
theorem completeSpace_padicValued :
    letI := padicValued p K
    CompleteSpace K := by
  letI := padicValued p K
  letI := padicRankOne p K
  letI N₁ : NormedField K := Valued.toNormedField K ℤᵐ⁰
  have hd : ∀ x y : K, dist x y = nrm p K (x - y) := fun x y => by
    rw [dist_eq_norm]; exact norm_padicValued (x - y)
  haveI hc := spectralNorm.completeSpace ℚ_[p] K
  exact completeSpace_of_dist_eq N₁.toPseudoMetricSpace
    (spectralNorm.normedField ℚ_[p] K).toPseudoMetricSpace (fun x y => (hd x y).trans rfl)

end

/-! ### `ℚ_p`-algebra homomorphisms are continuous -/

section Continuity

variable {p : ℕ} [hp : Fact p.Prime]
variable {E E' : Type*} [Field E] [Valued E ℤᵐ⁰]
  [Valuation.RankOne (Valued.v : Valuation E ℤᵐ⁰)] [Algebra ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [Field E'] [Valued E' ℤᵐ⁰] [Valuation.RankOne (Valued.v : Valuation E' ℤᵐ⁰)]
  [Algebra ℚ_[p] E'] [FiniteDimensional ℚ_[p] E']

/-- `ℚ_p`-algebra homomorphisms preserve the unit balls. -/
theorem norm_algHom_le_one_iff (f : E →ₐ[ℚ_[p]] E') (x : E) : ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [hball_auto (p := p), hball_auto (p := p), nrm_map]

/-- **Every `ℚ_p`-algebra homomorphism between `p`-adic fields is continuous** (for arbitrary
rank-one `ℤᵐ⁰`-valuations on the two fields). -/
theorem continuous_algHom_auto (f : E →ₐ[ℚ_[p]] E') : Continuous f := by
  have hpE : ‖(p : E)‖ < 1 := norm_p_lt_one_auto
  have hpE' : ‖(p : E')‖ < 1 := norm_p_lt_one_auto
  have hpE0 : 0 < ‖(p : E)‖ := by
    haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] E).injective
    exact norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  refine continuous_of_continuousAt_zero f.toRingHom.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hpE'
  refine ⟨‖(p : E)‖ ^ n, pow_pos hpE0 n, fun x hx => ?_⟩
  rw [dist_zero_right] at hx
  rw [dist_zero_right]
  have hpn : (p : E) ^ n ≠ 0 := by
    have : ‖(p : E) ^ n‖ ≠ 0 := by rw [norm_pow]; exact (pow_pos hpE0 n).ne'
    exact norm_ne_zero_iff.1 this
  have h1 : ‖x / (p : E) ^ n‖ ≤ 1 := by
    rw [norm_div, norm_pow, div_le_one (pow_pos hpE0 n)]; exact hx.le
  have h2 := (norm_algHom_le_one_iff f _).2 h1
  have h3 : f x = f (x / (p : E) ^ n) * (p : E') ^ n := by
    rw [← map_natCast f, ← map_pow, ← map_mul, div_mul_cancel₀ _ hpn]
  change ‖f x‖ < ε
  rw [h3, norm_mul, norm_pow]
  calc ‖f (x / (p : E) ^ n)‖ * ‖(p : E')‖ ^ n ≤ 1 * ‖(p : E')‖ ^ n := by gcongr
    _ < ε := by rw [one_mul]; exact hn

end Continuity

end Iut.Reconstruction
