/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.LogCond

/-!
# The height comparison for the Legendre curves

We prove `Iut.Tripod.LegendreHeightHyp P K` (IUT IV, Corollary 2.2(i); [GenEll],
Proposition 3.4) for the providers `P` of the Legendre curves: on a compactly bounded subset
`K` of the tripod, `(1/6)·log(q_∀(E_λ)) ≈ ht_{𝒪(1)}(λ)`, where `ht_{𝒪(1)}` is the absolute
logarithmic Weil height (`Iut.Tripod.htCan`).

## The proof

Write `g = λ ∈ ℚ(λ)`, `j = j(E_λ) = 256(g² − g + 1)³/(g²(g − 1)²)`, `d = [ℚ(λ) : ℚ]`, and for
`y` in a number field `T` let `h_fin(y) = ∑_{v finite} log⁺|y|_v` and
`h_∞(y) = ∑_{v infinite} [T_v : ℝ] log⁺|y|_v` be the two parts of Mathlib's relative
logarithmic height `logHeight₁ y = h_∞(y) + h_fin(y)` (`Iut.finHeight`, `Iut.infHeight`).

1. `log(q_∀(E_λ)) = h_fin(j)/d` (`Iut.Tripod.h_eq_finHeight_div`): at a multiplicative place
   `w` of `F_λ`, `ord_w(q_w) f_w log p_w = log|j|_w = log⁺|j|_w`
   (`Iut.Tripod.valuation_j_eq_exp_qOrder`), and at a place of good reduction `|j|_w ≤ 1`
   (stable reduction); so `[F_λ : ℚ]·log(q_∀) = h_fin^{F_λ}(j)`. The finite part of the
   height is invariant under finite extensions (`Iut.finHeight_algebraMap`:
   `|y|_w = |y|_v^{e(w/v) f(w/v)}` and `∑_{w ∣ v} e(w/v) f(w/v) = [F_λ : F_tpd]`), and
   `F_tpd ≅ ℚ(λ)` (`Iut.finHeight_mapEquiv`).
2. At every finite place `v` of `ℚ(λ)`, the ultrametric inequality gives
   `log⁺|j|_v ≤ 2(log⁺|g|_v + log⁺|g⁻¹|_v + log⁺|(g − 1)⁻¹|_v)`, with equality when
   `|256|_v = 1`, i.e. at the places of odd residue characteristic
   (`Iut.posLog_legendreJ_le`, `Iut.posLog_legendreJ_ge`). Hence
   `h_fin(j) ≤ 2(h_fin(g) + h_fin(g⁻¹) + h_fin((g − 1)⁻¹))`, and the reverse inequality holds
   up to the contribution of the places over the support `V ∋ 2` of `K`, where the
   compactly bounded subset bounds each term by `c` and there are at most `|V|·d` places
   (`Iut.Tripod.finHeight_legendreJ_le`, `Iut.Tripod.finHeight_legendreJ_ge`).
3. On `K`, the archimedean parts `h_∞(g)`, `h_∞(g⁻¹)`, `h_∞((g − 1)⁻¹)` are at most `c·d`
   (`Iut.Tripod.infHeight_gen_le`, …), so `h_fin` may be replaced by `logHeight₁` at the cost
   of `O(d)`; finally `logHeight₁(g⁻¹) = logHeight₁(g)` and
   `|logHeight₁(g − 1) − logHeight₁(g)| ≤ d·log 2`, so
   `h_fin(j) = 6·logHeight₁(g) + O(d)`, i.e. `(1/6)·log(q_∀) = htCan + O(1)`.
   If `j = 0`, then `g` is a primitive sixth root of unity, and both sides vanish.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped WithZero Real

/-! ### The finite and the archimedean parts of the height -/

section FinHeight

variable {T : Type*} [Field T] [NumberField T]

/-- **The finite part of the logarithmic height**: `h_fin(y) = ∑_{v finite} log⁺|y|_v`. -/
noncomputable def finHeight (y : T) : ℝ := ∑ᶠ v : FinitePlace T, log⁺ (v y)

/-- **The archimedean part of the logarithmic height**:
`h_∞(y) = ∑_{v infinite} [T_v : ℝ] log⁺|y|_v`. -/
noncomputable def infHeight (y : T) : ℝ := ∑ v : InfinitePlace T, (v.mult : ℝ) * log⁺ (v y)

/-- `logHeight₁ y = h_∞(y) + h_fin(y)`. -/
lemma logHeight₁_eq_infHeight_add_finHeight (y : T) :
    Height.logHeight₁ y = infHeight y + finHeight y :=
  logHeight₁_eq y

lemma infHeight_nonneg (y : T) : 0 ≤ infHeight y :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg

lemma finHeight_nonneg (y : T) : 0 ≤ finHeight y :=
  finsum_nonneg fun _ => Real.posLog_nonneg

lemma finHeight_le_logHeight₁ (y : T) : finHeight y ≤ Height.logHeight₁ y := by
  rw [logHeight₁_eq_infHeight_add_finHeight]
  linarith [infHeight_nonneg y]

@[simp] lemma finHeight_zero : finHeight (0 : T) = 0 := by
  simp [finHeight]

/-- The support of `v ↦ log⁺|y|_v` is contained in the multiplicative support of
`v ↦ |y|_v`. -/
lemma support_posLog_subset (y : T) :
    Function.support (fun v : FinitePlace T => log⁺ (v y)) ⊆
      Function.mulSupport (fun v : FinitePlace T => v y) := by
  intro v hv
  simp only [Function.mem_support, Function.mem_mulSupport] at hv ⊢
  intro h
  apply hv
  rw [h, Real.posLog_one]

/-- `v ↦ log⁺|y|_v` has finite support. -/
lemma hasFiniteSupport_posLog (y : T) :
    Function.HasFiniteSupport (fun v : FinitePlace T => log⁺ (v y)) := by
  by_cases hy : y = 0
  · subst hy
    refine Set.Finite.subset Set.finite_empty ?_
    intro v hv
    simp at hv
  · exact Set.Finite.subset (FinitePlace.hasFiniteMulSupport hy) (support_posLog_subset y)

/-- `h_fin(y)` as a sum over any finite set containing the support. -/
lemma finHeight_eq_sum {y : T} {S : Finset (FinitePlace T)}
    (hS : ∀ v : FinitePlace T, log⁺ (v y) ≠ 0 → v ∈ S) :
    finHeight y = ∑ v ∈ S, log⁺ (v y) :=
  finsum_eq_sum_of_support_subset _ fun v hv => hS v hv

/-- The finite part of the height is invariant under isomorphisms of number fields. -/
lemma finHeight_mapEquiv {T' : Type*} [Field T'] [NumberField T'] (e : T ≃+* T') (y : T) :
    finHeight (e y) = finHeight y := by
  unfold finHeight
  rw [← finsum_comp_equiv (FinitePlace.mapEquiv e)]
  refine finsum_congr fun v => ?_
  rw [FinitePlace.mapEquiv_apply, RingEquiv.symm_apply_apply]

/-! ### The absolute value at a finite place in terms of the valuation -/

/-- The weight `f_w · log p_w` of a finite place: `|y|_w = p_w^{f_w · m}` for `v_w(y) = exp m`. -/
noncomputable def finWeight (w : FinitePlace T) : ℝ := inertDeg T w * Real.log (residueChar w)

lemma finWeight_pos (w : FinitePlace T) : 0 < finWeight w :=
  mul_pos (by exact_mod_cast inertDeg_pos' w)
    (Real.log_pos (by exact_mod_cast (residueChar_prime w).one_lt))

/-- `log⁺|y|_w = f_w log p_w · max(0, log v_w(y))`. -/
lemma posLog_apply_eq (w : FinitePlace T) {y : T} (hy : y ≠ 0) :
    log⁺ (w y) = finWeight w * max 0 ((log (w.maximalIdeal.valuation T y) : ℤ) : ℝ) := by
  rw [Real.posLog_apply, Iut.Tripod.log_apply_eq w hy, mul_max_of_nonneg _ _ (finWeight_pos w).le,
    mul_zero, mul_comm]
  rfl

end FinHeight

/-! ### Invariance of the finite part of the height under finite extensions -/

section Extension

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-- The place below is unique. -/
lemma placeUnder_eq_of_liesOver_place {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : placeUnder w = v := by
  symm
  apply (FinitePlace.maximalIdeal_inj _ _).mp
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeUnder_maximalIdeal]
  exact hwv.over

/-- The local degree `e(w/v) f(w/v)` of `w` over `v`. -/
noncomputable abbrev relLocalDeg (w : FinitePlace K) (v : FinitePlace k) : ℕ :=
  relRamIdx w v * relInertDeg w v

lemma relLocalDeg_ne_zero {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) : relLocalDeg w v ≠ 0 := by
  have h := inertDeg_eq_mul hwv
  have hpos := inertDeg_pos' w
  refine mul_ne_zero (relRamIdx_ne_zero hwv) fun h0 => ?_
  rw [h, h0, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-- **`|y|_w = |y|_v^{e(w/v) f(w/v)}`** for `y ∈ k` and `w ∣ v`. -/
lemma apply_algebraMap_eq_pow {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    w (algebraMap k K y) = v y ^ relLocalDeg w v := by
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, map_zero, map_zero, zero_pow (relLocalDeg_ne_zero hwv)]
  have hy' : algebraMap k K y ≠ 0 := (map_ne_zero _).mpr hy
  have hpos : 0 < w (algebraMap k K y) := FinitePlace.pos_iff.mpr hy'
  have hpos' : 0 < v y := FinitePlace.pos_iff.mpr hy
  have hlog : Real.log (w (algebraMap k K y)) = relLocalDeg w v * Real.log (v y) := by
    rw [Iut.Tripod.log_apply_eq w hy', Iut.Tripod.log_apply_eq v hy,
      valuation_algebraMap_eq_pow hwv, log_pow, inertDeg_eq_mul hwv,
      residueChar_eq_of_liesOver hwv]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [← Real.exp_log hpos, hlog, ← Real.log_pow, Real.exp_log (pow_pos hpos' _)]

/-- `log⁺|y|_w = e(w/v) f(w/v) · log⁺|y|_v` for `y ∈ k` and `w ∣ v`. -/
lemma posLog_apply_algebraMap_eq {w : FinitePlace K} {v : FinitePlace k}
    (hwv : FinitePlace.LiesOver w v) (y : k) :
    log⁺ (w (algebraMap k K y)) = relLocalDeg w v * log⁺ (v y) := by
  rw [apply_algebraMap_eq_pow hwv, Real.posLog_pow]

/-- `∑_{w ∣ v} e(w/v) f(w/v) = [K : k]`. -/
lemma sum_relLocalDeg_liesOver (v : FinitePlace k) (s : Finset (FinitePlace K))
    (hs : ∀ w, w ∈ s ↔ FinitePlace.LiesOver w v) :
    ∑ w ∈ s, relLocalDeg w v = Module.finrank k K := by
  have h := sum_localDeg_liesOver v s hs
  have h' : ∑ w ∈ s, localDeg K w = localDeg k v * ∑ w ∈ s, relLocalDeg w v := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w hw => localDeg_eq_mul ((hs w).mp hw)
  have hpos : 0 < localDeg k v := Nat.mul_pos (ramIdx_pos' v) (inertDeg_pos' v)
  rw [h', mul_comm (Module.finrank k K)] at h
  exact Nat.eq_of_mul_eq_mul_left hpos h

/-- **The finite part of the height is invariant under finite extensions**:
`h_fin^K(y) = [K : k] · h_fin^k(y)` for `y ∈ k`. -/
theorem finHeight_algebraMap (y : k) :
    finHeight (algebraMap k K y) = Module.finrank k K * finHeight y := by
  classical
  set Sk := (hasFiniteSupport_posLog y).toFinset with hSk
  set SK := (hasFiniteSupport_posLog (algebraMap k K y)).toFinset with hSK
  have hmemk : ∀ v, v ∈ Sk ↔ log⁺ (v y) ≠ 0 := fun v => by
    rw [hSk, Set.Finite.mem_toFinset, Function.mem_support]
  have hmemK : ∀ w, w ∈ SK ↔ log⁺ (w (algebraMap k K y)) ≠ 0 := fun w => by
    rw [hSK, Set.Finite.mem_toFinset, Function.mem_support]
  have hfib : ∀ w : FinitePlace K,
      log⁺ (w (algebraMap k K y)) = relLocalDeg w (placeUnder w) * log⁺ (placeUnder w y) :=
    fun w => posLog_apply_algebraMap_eq (liesOver_placeUnder w) y
  have hmaps : ∀ w ∈ SK, placeUnder w ∈ Sk := by
    intro w hw
    rw [hmemK, hfib] at hw
    rw [hmemk]
    exact (mul_ne_zero_iff.mp hw).2
  rw [finHeight_eq_sum fun w hw => (hmemK w).mpr hw, finHeight_eq_sum fun v hv => (hmemk v).mpr hv,
    ← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  have hs : ∀ w, w ∈ SK.filter (fun w => placeUnder w = v) ↔ FinitePlace.LiesOver w v := by
    intro w
    rw [Finset.mem_filter, hmemK]
    constructor
    · rintro ⟨-, rfl⟩
      exact liesOver_placeUnder w
    · intro hwv
      have hv' := placeUnder_eq_of_liesOver_place hwv
      refine ⟨?_, hv'⟩
      rw [hfib, hv']
      exact mul_ne_zero (by exact_mod_cast relLocalDeg_ne_zero hwv) ((hmemk v).mp hv)
  calc ∑ w ∈ SK.filter (fun w => placeUnder w = v), log⁺ (w (algebraMap k K y))
      = ∑ w ∈ SK.filter (fun w => placeUnder w = v), (relLocalDeg w v : ℝ) * log⁺ (v y) := by
        refine Finset.sum_congr rfl fun w hw => ?_
        rw [posLog_apply_algebraMap_eq ((hs w).mp hw)]
    _ = (Module.finrank k K : ℝ) * log⁺ (v y) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, sum_relLocalDeg_liesOver v _ hs]

end Extension

/-! ### The `j`-invariant of the Legendre curve at a finite place -/

section LegendreJ

/-- `j(λ) = 256(λ² − λ + 1)³/(λ²(λ − 1)²)`, as an explicit expression. -/
noncomputable def legendreJ {R : Type*} [Field R] (l : R) : R :=
  256 * (l ^ 2 - l + 1) ^ 3 / (l ^ 2 * (l - 1) ^ 2)

lemma map_legendreJ {R S F : Type*} [Field R] [Field S] [FunLike F R S] [RingHomClass F R S]
    (f : F) (l : R) : f (legendreJ l) = legendreJ (f l) := by
  simp only [legendreJ, map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]

open WeierstrassCurve Iut.Tripod in
/-- `j(E_λ) = legendreJ λ`. -/
lemma legendre_j_eq_legendreJ {R : Type*} [Field R] [NeZero (2 : R)] {l : R}
    [(legendre l).IsElliptic] : (legendre l).j = legendreJ l :=
  legendre_j

variable {R : Type*} [Field R] (v : Valuation R ℤᵐ⁰) {l : R}

/-- The right-hand side of the ultrametric comparison at a finite place:
`2(max(0, log v(λ)) + max(0, −log v(λ)) + max(0, −log v(λ − 1)))`. -/
def legendreBound (l : R) : ℤ :=
  2 * (max 0 (log (v l)) + max 0 (-log (v l)) + max 0 (-log (v (l - 1))))

lemma legendreBound_nonneg (l : R) : 0 ≤ legendreBound v l := by
  unfold legendreBound
  have h1 := le_max_left 0 (log (v l))
  have h2 := le_max_left 0 (-log (v l))
  have h3 := le_max_left 0 (-log (v (l - 1)))
  omega

variable (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- `v(legendreJ λ) ≠ 0 ↔ v(λ² − λ + 1) ≠ 0`. -/
lemma valuation_legendreJ_ne_zero_iff [NeZero (2 : R)] :
    v (legendreJ l) ≠ 0 ↔ v (l ^ 2 - l + 1) ≠ 0 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow]
  rw [div_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff, pow_ne_zero_iff (by norm_num),
    pow_ne_zero_iff (by norm_num), pow_ne_zero_iff (by norm_num)]
  simp only [(Valuation.ne_zero_iff v).mpr h256, (Valuation.ne_zero_iff v).mpr hl0,
    (Valuation.ne_zero_iff v).mpr hl1', ne_eq, not_false_eq_true, true_and, and_true]

/-- `log v(j) = log v(256) + 3 log v(λ² − λ + 1) − 2 log v(λ) − 2 log v(λ − 1)`. -/
lemma log_valuation_legendreJ [NeZero (2 : R)] (hc : v (l ^ 2 - l + 1) ≠ 0) :
    log (v (legendreJ l)) = log (v 256) + 3 * log (v (l ^ 2 - l + 1)) -
      (2 * log (v l) + 2 * log (v (l - 1))) := by
  have h256 : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [legendreJ, map_div₀, map_mul, map_pow, map_mul, map_pow, map_pow,
    log_div (mul_ne_zero h256 (pow_ne_zero _ hc))
      (mul_ne_zero (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1)),
    log_mul h256 (pow_ne_zero _ hc), log_pow, log_mul (pow_ne_zero _ hvl) (pow_ne_zero _ hvl1),
    log_pow, log_pow]
  simp only [nsmul_eq_mul]
  push_cast
  ring

omit hl0 hl1 in
/-- **The ultrametric case analysis** for `λ`, `λ − 1`, `λ² − λ + 1` at a finite place. -/
lemma legendre_valuation_cases :
    (v l < 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) < 1 ∧ v (l ^ 2 - l + 1) = 1) ∨
    (v l = 1 ∧ v (l - 1) = 1 ∧ v (l ^ 2 - l + 1) ≤ 1) ∨
    (1 < v l ∧ v (l - 1) = v l ∧ v (l ^ 2 - l + 1) = v l ^ 2) := by
  have e : l ^ 2 - l + 1 = l * (l - 1) + 1 := by ring
  rcases lt_trichotomy (v l) 1 with hlt | heq | hgt
  · left
    have hb : v (l - 1) = 1 := by
      rw [Valuation.map_sub_eq_of_lt_right v (by rw [map_one]; exact hlt), map_one]
    refine ⟨hlt, hb, ?_⟩
    have hlt' : v (l * (l - 1)) < v 1 := by
      rw [map_mul, hb, mul_one, map_one]
      exact hlt
    rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
  · have hb' : v (l - 1) ≤ 1 := by
      have := Valuation.map_sub v l 1
      rwa [heq, map_one, max_self] at this
    rcases hb'.lt_or_eq with hb | hb
    · right; left
      refine ⟨heq, hb, ?_⟩
      have hlt' : v (l * (l - 1)) < v 1 := by
        rw [map_mul, heq, one_mul, map_one]
        exact hb
      rw [e, Valuation.map_add_eq_of_lt_right v hlt', map_one]
    · right; right; left
      refine ⟨heq, hb, ?_⟩
      rw [e]
      refine (Valuation.map_add v _ _).trans (max_le ?_ (map_one v).le)
      rw [map_mul, heq, hb, mul_one]
  · right; right; right
    have hb : v (l - 1) = v l :=
      Valuation.map_sub_eq_of_lt_left v (by rw [map_one]; exact hgt)
    refine ⟨hgt, hb, ?_⟩
    have e' : l ^ 2 - l + 1 = l ^ 2 + (1 - l) := by ring
    have hlt' : v (1 - l) < v (l ^ 2) := by
      rw [Valuation.map_sub_swap, hb, map_pow]
      exact lt_self_pow₀ hgt (by norm_num)
    rw [e', Valuation.map_add_eq_of_lt_left v hlt', map_pow]

/-- **The upper bound** `max(0, log v(j)) ≤ legendreBound` for `v(256) ≤ 1`. -/
lemma max_log_valuation_legendreJ_le [NeZero (2 : R)] (h256 : v 256 ≤ 1) :
    max 0 (log (v (legendreJ l))) ≤ legendreBound v l := by
  refine max_le (legendreBound_nonneg v l) ?_
  by_cases hj : v (legendreJ l) = 0
  · rw [hj, log_zero]
    exact legendreBound_nonneg v l
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  have h256' : v 256 ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this, map_pow]
    exact pow_ne_zero _ ((Valuation.ne_zero_iff v).mpr (NeZero.ne 2))
  have hd : log (v 256) ≤ 0 := by
    have := (log_le_log h256' one_ne_zero).mpr h256
    simpa using this
  rw [log_valuation_legendreJ v hl0 hl1 hc]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    have := le_max_left 0 (log (v l))
    have := le_max_right 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    have := le_max_right 0 (-log (v (l - 1)))
    omega
  · have hS : log (v (l ^ 2 - l + 1)) ≤ 0 := by
      have := (log_le_log hc one_ne_zero).mpr hc'
      simpa using this
    rw [ha, hb, log_one]
    have := le_max_left 0 (-log (v (l - 1)))
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    have := le_max_right 0 (log (v l))
    have := le_max_left 0 (-log (v l))
    have := le_max_left 0 (-log (v (l - 1)))
    push_cast
    omega

/-- **The lower bound** `legendreBound ≤ max(0, log v(j))` for `v(256) = 1` and `j ≠ 0`. -/
lemma legendreBound_le_max_log_valuation_legendreJ [NeZero (2 : R)] (h256 : v 256 = 1)
    (hj : v (legendreJ l) ≠ 0) :
    legendreBound v l ≤ max 0 (log (v (legendreJ l))) := by
  have hc : v (l ^ 2 - l + 1) ≠ 0 := (valuation_legendreJ_ne_zero_iff v hl0 hl1).mp hj
  have hvl : v l ≠ 0 := (Valuation.ne_zero_iff v).mpr hl0
  have hvl1 : v (l - 1) ≠ 0 := (Valuation.ne_zero_iff v).mpr (sub_ne_zero.mpr hl1)
  rw [log_valuation_legendreJ v hl0 hl1 hc, h256, log_one]
  unfold legendreBound
  rcases legendre_valuation_cases v (l := l) with ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ | ⟨ha, hb, hc'⟩ |
    ⟨ha, hb, hc'⟩
  · have hU : log (v l) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl one_ne_zero).mpr ha
    rw [hb, hc', log_one]
    omega
  · have hT : log (v (l - 1)) < 0 := by
      rw [← log_one]
      exact (log_lt_log hvl1 one_ne_zero).mpr hb
    rw [ha, hc', log_one]
    omega
  · rw [ha, hb, log_one]
    omega
  · have hU : 0 < log (v l) := by
      rw [← log_one]
      exact (log_lt_log one_ne_zero hvl).mpr ha
    rw [hb, hc', log_pow]
    simp only [nsmul_eq_mul]
    push_cast
    omega

end LegendreJ

/-! ### The comparison at a finite place of a number field -/

section PlaceComparison

variable {T : Type*} [Field T] [NumberField T] (w : FinitePlace T) {l : T}
  (hl0 : l ≠ 0) (hl1 : l ≠ 1)
include hl0 hl1

/-- The three terms of the comparison at a finite place, in terms of the valuation. -/
lemma posLog_terms_eq :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) =
      finWeight w * (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by
  have hl1' : l - 1 ≠ 0 := sub_ne_zero.mpr hl1
  rw [posLog_apply_eq w hl0, posLog_apply_eq w (inv_ne_zero hl0),
    posLog_apply_eq w (inv_ne_zero hl1'), map_inv₀, map_inv₀, log_inv, log_inv]
  unfold legendreBound
  push_cast
  ring

/-- **`log⁺|j|_w ≤ 2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w)`** at every finite place. -/
theorem posLog_legendreJ_le :
    log⁺ (w (legendreJ l)) ≤ 2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) := by
  rw [posLog_terms_eq w hl0 hl1]
  by_cases hj : legendreJ l = 0
  · rw [hj, map_zero, Real.posLog_zero]
    exact mul_nonneg (finWeight_pos w).le (by exact_mod_cast legendreBound_nonneg _ l)
  rw [posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h := max_log_valuation_legendreJ_le (w.maximalIdeal.valuation T) hl0 hl1
    (Iut.Tripod.valuation_256_le_one w)
  have h' : ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) ≤
      (legendreBound (w.maximalIdeal.valuation T) l : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

/-- **`2(log⁺|λ|_w + log⁺|λ⁻¹|_w + log⁺|(λ − 1)⁻¹|_w) ≤ log⁺|j|_w`** at a finite place of odd
residue characteristic, for `j ≠ 0`. -/
theorem posLog_legendreJ_ge (h2 : residueChar w ≠ 2) (hj : legendreJ l ≠ 0) :
    2 * (log⁺ (w l) + log⁺ (w l⁻¹) + log⁺ (w (l - 1)⁻¹)) ≤ log⁺ (w (legendreJ l)) := by
  rw [posLog_terms_eq w hl0 hl1, posLog_apply_eq w hj]
  refine mul_le_mul_of_nonneg_left ?_ (finWeight_pos w).le
  have h256 : w.maximalIdeal.valuation T 256 = 1 := by
    have : (256 : T) = 2 ^ 8 := by norm_num
    rw [this, map_pow, valuation_two_eq_one_of_ne h2, one_pow]
  have h := legendreBound_le_max_log_valuation_legendreJ (w.maximalIdeal.valuation T) hl0 hl1
    h256 ((Valuation.ne_zero_iff _).mpr hj)
  have h' : (legendreBound (w.maximalIdeal.valuation T) l : ℝ) ≤
      ((max 0 (log (w.maximalIdeal.valuation T (legendreJ l))) : ℤ) : ℝ) := by exact_mod_cast h
  rwa [Int.cast_max, Int.cast_zero] at h'

end PlaceComparison

/-! ### `j = 0` -/

/-- If `j(λ) = 0` then `λ` is a sixth root of unity. -/
lemma pow_six_eq_one_of_legendreJ_eq_zero {R : Type*} [Field R] [NeZero (2 : R)] {l : R}
    (hl0 : l ≠ 0) (hl1 : l ≠ 1) (hj : legendreJ l = 0) : l ^ 6 = 1 := by
  have h256 : (256 : R) ≠ 0 := by
    have : (256 : R) = 2 ^ 8 := by norm_num
    rw [this]
    exact pow_ne_zero _ (NeZero.ne 2)
  have hden : l ^ 2 * (l - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ (sub_ne_zero.mpr hl1))
  rw [legendreJ, div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by norm_num)] at hj
  rcases hj with (h | h) | h
  · exact absurd h h256
  · have h3 : l ^ 3 = -1 := by linear_combination (l + 1) * h
    calc l ^ 6 = (l ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3]; ring
  · exact absurd h hden

/-! ### The archimedean part on a set of bounded absolute values -/

/-- `h_∞(y) ≤ c·[T : ℚ]` if `log⁺|y|_w ≤ c` at every infinite place. -/
lemma infHeight_le_of_forall {T : Type*} [Field T] [NumberField T] {y : T} {c : ℝ}
    (h : ∀ w : InfinitePlace T, log⁺ (w y) ≤ c) :
    infHeight y ≤ c * Module.finrank ℚ T := by
  unfold infHeight
  calc ∑ w : InfinitePlace T, (w.mult : ℝ) * log⁺ (w y)
      ≤ ∑ w : InfinitePlace T, (w.mult : ℝ) * c :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (h w) (Nat.cast_nonneg _)
    _ = c * Module.finrank ℚ T := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq, mul_comm]

/-- `log⁺ t ≤ |log t|`. -/
lemma posLog_le_abs_log (t : ℝ) : log⁺ t ≤ |Real.log t| := by
  rw [Real.posLog_apply]
  exact max_le (abs_nonneg _) (le_abs_self _)

/-- `log⁺ t⁻¹ ≤ |log t|`. -/
lemma posLog_inv_le_abs_log (t : ℝ) : log⁺ t⁻¹ ≤ |Real.log t| := by
  rw [Real.posLog_apply, Real.log_inv]
  exact max_le (abs_nonneg _) (neg_le_abs _)

end Iut

namespace Iut.Tripod

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero WeierstrassCurve
open scoped WithZero Real

variable (P : CurveProviders) (x : Pt)

/-! ### `log(q_∀(E_λ))` as the finite part of the height of `j` -/

/-- `j(E_λ)` as an element of `F_tpd`. -/
noncomputable abbrev jT : tpd P x := legendreJ (genT P x)

/-- `j(E_λ) = legendreJ λ` in `F_λ`. -/
theorem curve_j_eq_legendreJ : (P.curve x).E.j = legendreJ (genC' P x) := by
  change (legendre (genC' P x)).j = _
  exact legendre_j_eq_legendreJ

/-- `j(E_λ)` comes from `F_tpd`. -/
theorem curve_j_eq_algebraMap :
    (P.curve x).E.j = algebraMap (tpd P x) (P.curve x).F (jT P x) := by
  rw [curve_j_eq_legendreJ, jT, map_legendreJ, algebraMap_genT]

/-- `F_tpd ≅ ℚ(λ)` maps `j` to `legendreJ λ`. -/
theorem tpdEquiv_jT : tpdEquiv P x (jT P x) = legendreJ (gen x.1) := by
  rw [jT, map_legendreJ, tpdEquiv_genT]

/-- **At a multiplicative place, `log⁺|j|_w = ord_w(q_w) f_w log p_w`.** -/
theorem posLog_j_eq_of_mem_badAll {w : FinitePlace (P.curve x).F} (hw : w ∈ (P.curve x).badAll) :
    log⁺ (w (P.curve x).E.j) =
      ((P.tate x).qOrder w hw : ℝ) * inertDeg (P.curve x).F w * Real.log (residueChar w) := by
  have hvj : w.maximalIdeal.valuation _ (P.curve x).E.j = exp (((P.tate x).qOrder w hw : ℕ) : ℤ) :=
    (P.curve x).valuation_j_eq_exp_qOrder hw
  have hj0 : (P.curve x).E.j ≠ 0 := by
    intro h
    rw [h, map_zero] at hvj
    exact exp_ne_zero hvj.symm
  rw [posLog_apply_eq w hj0, hvj, log_exp, finWeight, max_eq_right (by positivity)]
  push_cast
  ring

/-- **At a place of good reduction, `log⁺|j|_w = 0`** (stable reduction). -/
theorem posLog_j_eq_zero_of_not_mem_badAll {w : FinitePlace (P.curve x).F}
    (hw : w ∉ (P.curve x).badAll) : log⁺ (w (P.curve x).E.j) = 0 := by
  have hst := (P.arith x).stable_reduction w
  have hle : w.maximalIdeal.valuation _ (P.curve x).E.j ≤ 1 := by
    by_contra h
    exact hw ((hasMultiplicativeReductionAt_iff_of_stable (P.curve x).E w hst).mpr h)
  rw [Real.posLog_eq_zero_iff, abs_of_nonneg (apply_nonneg _ _), ← FinitePlace.norm_embedding_eq]
  exact (norm_emb_le_one_iff _).mpr hle

/-- **`[F_λ : ℚ]·log(q_∀(E_λ)) = h_fin^{F_λ}(j)`.** -/
theorem finrank_mul_h_eq_finHeight :
    (Module.finrank ℚ (P.curve x).F : ℝ) * P.h x = finHeight (P.curve x).E.j := by
  classical
  have h := (P.localData x).deg_mul_height
  change ((P.localData x).deg : ℝ) * (P.localData x).height = _
  rw [h]
  have hmem : ∀ w, w ∈ (P.localData x).bad ↔ w ∈ (P.curve x).badAll := fun w =>
    (P.arith x).badAll_finite.mem_toFinset
  have hhv : ∀ w, (P.localData x).hv w =
      if h : w ∈ (P.curve x).badAll then (P.tate x).qOrder w h else 0 := fun w => rfl
  have hf : ∀ w, (P.localData x).f w = inertDeg (P.curve x).F w := fun w => rfl
  have hp : ∀ w, (P.localData x).p w = residueChar w := fun w => rfl
  rw [finHeight_eq_sum (S := (P.localData x).bad) (fun w hw => ?_)]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [hmem] at hw
    rw [hhv, hf, hp, dif_pos hw, posLog_j_eq_of_mem_badAll P x hw]
  · refine (hmem w).mpr ?_
    by_contra h'
    exact hw (posLog_j_eq_zero_of_not_mem_badAll P x h')

/-- **`log(q_∀(E_λ)) = h_fin(j)/[ℚ(λ) : ℚ]`**, with `h_fin` computed in `ℚ(λ)`. -/
theorem h_eq_finHeight_div : P.h x = finHeight (legendreJ (gen x.1)) / deg x.1 := by
  have h1 := finrank_mul_h_eq_finHeight P x
  haveI : Module.Finite (tpd P x) (P.curve x).F := Module.Finite.right ℚ (tpd P x) (P.curve x).F
  have hT : finHeight (jT P x) = finHeight (legendreJ (gen x.1)) := by
    rw [← tpdEquiv_jT]
    exact (finHeight_mapEquiv (tpdEquiv P x : tpd P x ≃+* fieldOf x.1) (jT P x)).symm
  rw [curve_j_eq_algebraMap, finHeight_algebraMap, hT] at h1
  have h2 : (Module.finrank ℚ (P.curve x).F : ℝ) =
      deg x.1 * Module.finrank (tpd P x) (P.curve x).F := by
    rw [← finrank_tpd P x]
    exact_mod_cast (Module.finrank_mul_finrank ℚ (tpd P x) (P.curve x).F).symm
  have h3 : (Module.finrank (tpd P x) (P.curve x).F : ℝ) ≠ 0 := by
    intro h0
    have hpos : (0 : ℝ) < Module.finrank ℚ (P.curve x).F := by
      exact_mod_cast Module.finrank_pos
    rw [h2, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  rw [h2] at h1
  rw [eq_div_iff (deg_pos_real x.1).ne']
  apply mul_left_cancel₀ h3
  calc (Module.finrank (tpd P x) (P.curve x).F : ℝ) * (P.h x * deg x.1)
      = deg x.1 * Module.finrank (tpd P x) (P.curve x).F * P.h x := by ring
    _ = _ := h1

/-! ### The bounds on a compactly bounded subset -/

variable {K : CompactlyBounded} {x : Pt}

/-- On `K`, the three archimedean terms are bounded by `c` at every infinite place. -/
lemma posLog_infinite_le (hx : x ∈ K.set) (w : InfinitePlace (fieldOf x.1)) :
    log⁺ (w (gen x.1)) ≤ K.c ∧ log⁺ (w (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (w (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.2 w
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

/-- On `K`, the three nonarchimedean terms are bounded by `c` at every finite place over the
support `V`. -/
lemma posLog_finite_le (hx : x ∈ K.set) (v : FinitePlace (fieldOf x.1))
    (hv : residueChar v ∈ K.V) :
    log⁺ (v (gen x.1)) ≤ K.c ∧ log⁺ (v (gen x.1)⁻¹) ≤ K.c ∧
      log⁺ (v (gen x.1 - 1)⁻¹) ≤ K.c := by
  obtain ⟨h1, h2⟩ := hx.1 v hv
  refine ⟨(posLog_le_abs_log _).trans h1, ?_, ?_⟩
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h1
  · rw [map_inv₀]
    exact (posLog_inv_le_abs_log _).trans h2

/-- **The archimedean parts are `O(d)` on `K`**: `logHeight₁ y ≤ h_fin(y) + c·d` for
`y ∈ {λ, λ⁻¹, (λ − 1)⁻¹}`. -/
lemma logHeight₁_le_finHeight_add (hx : x ∈ K.set) :
    Height.logHeight₁ (gen x.1) ≤ finHeight (gen x.1) + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1)⁻¹ ≤ finHeight (gen x.1)⁻¹ + K.c * deg x.1 ∧
    Height.logHeight₁ (gen x.1 - 1)⁻¹ ≤ finHeight (gen x.1 - 1)⁻¹ + K.c * deg x.1 := by
  have key : ∀ y : fieldOf x.1, (∀ w : InfinitePlace (fieldOf x.1), log⁺ (w y) ≤ K.c) →
      Height.logHeight₁ y ≤ finHeight y + K.c * deg x.1 := by
    intro y hy
    rw [logHeight₁_eq_infHeight_add_finHeight, deg_eq_finrank]
    linarith [infHeight_le_of_forall hy]
  exact ⟨key _ fun w => (posLog_infinite_le hx w).1, key _ fun w => (posLog_infinite_le hx w).2.1,
    key _ fun w => (posLog_infinite_le hx w).2.2⟩

/-! ### The comparison of the finite parts -/

/-- A finite set of places of `ℚ(λ)` containing the supports of `log⁺|λ|_v`, `log⁺|λ⁻¹|_v`,
`log⁺|(λ − 1)⁻¹|_v` and `log⁺|j|_v`. -/
noncomputable def suppFinset (x : Pt) : Finset (FinitePlace (fieldOf x.1)) :=
  (Set.Finite.union
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1)) (hasFiniteSupport_posLog (gen x.1)⁻¹))
    (Set.Finite.union (hasFiniteSupport_posLog (gen x.1 - 1)⁻¹)
      (hasFiniteSupport_posLog (legendreJ (gen x.1))))).toFinset

lemma mem_suppFinset_of_ne {v : FinitePlace (fieldOf x.1)}
    (h : log⁺ (v (gen x.1)) ≠ 0 ∨ log⁺ (v (gen x.1)⁻¹) ≠ 0 ∨
      log⁺ (v (gen x.1 - 1)⁻¹) ≠ 0 ∨ log⁺ (v (legendreJ (gen x.1))) ≠ 0) :
    v ∈ suppFinset x := by
  rw [suppFinset, Set.Finite.mem_toFinset]
  simp only [Set.mem_union, Function.mem_support]
  tauto

lemma finHeight_gen_eq_sum (x : Pt) :
    finHeight (gen x.1) = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inl hv)

lemma finHeight_gen_inv_eq_sum (x : Pt) :
    finHeight (gen x.1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inl hv))

lemma finHeight_gen_sub_one_inv_eq_sum (x : Pt) :
    finHeight (gen x.1 - 1)⁻¹ = ∑ v ∈ suppFinset x, log⁺ (v (gen x.1 - 1)⁻¹) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inl hv)))

lemma finHeight_legendreJ_eq_sum (x : Pt) :
    finHeight (legendreJ (gen x.1)) = ∑ v ∈ suppFinset x, log⁺ (v (legendreJ (gen x.1))) :=
  finHeight_eq_sum fun _ hv => mem_suppFinset_of_ne (Or.inr (Or.inr (Or.inr hv)))

/-- The sum of the three finite parts as a sum over `suppFinset`. -/
lemma two_mul_finHeight_sum_eq (x : Pt) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) =
      ∑ v ∈ suppFinset x,
        2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) := by
  rw [finHeight_gen_eq_sum, finHeight_gen_inv_eq_sum, finHeight_gen_sub_one_inv_eq_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]

lemma gen_ne_one (x : Pt) : gen x.1 ≠ 1 := sub_ne_zero.mp (gen_sub_one_ne_zero x.2.2)

/-- **`h_fin(j) ≤ 2(h_fin(λ) + h_fin(λ⁻¹) + h_fin((λ − 1)⁻¹))`.** -/
theorem finHeight_legendreJ_le (x : Pt) :
    finHeight (legendreJ (gen x.1)) ≤
      2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) := by
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  exact Finset.sum_le_sum fun v _ => posLog_legendreJ_le v (gen_ne_zero x.2.1) (gen_ne_one x)

/-- The number of places of `ℚ(λ)` in a finite set `S` with residue characteristic in `V` is at
most `|V|·[ℚ(λ) : ℚ]`. -/
lemma card_filter_residueChar_mem_le (x : Pt) (S : Finset (FinitePlace (fieldOf x.1)))
    (V : Finset ℕ) :
    (S.filter (fun v => residueChar v ∈ V)).card ≤ V.card * deg x.1 := by
  classical
  have hsub : S.filter (fun v => residueChar v ∈ V) ⊆
      V.biUnion (fun q => S.filter (fun v => residueChar v = q)) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    rw [Finset.mem_biUnion]
    exact ⟨_, hv.2, Finset.mem_filter.mpr ⟨hv.1, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun q _ => ?_
  calc (S.filter (fun v => residueChar v = q)).card
      = ∑ v ∈ S.filter (fun v => residueChar v = q), 1 := by rw [Finset.card_eq_sum_ones]
    _ ≤ ∑ v ∈ S.filter (fun v => residueChar v = q), inertDeg (fieldOf x.1) v :=
        Finset.sum_le_sum fun v _ => inertDeg_pos' v
    _ ≤ Module.finrank ℚ (fieldOf x.1) := sum_inertDeg_filter_le S q
    _ = deg x.1 := (deg_eq_finrank x.1).symm

/-- **`2(h_fin(λ) + h_fin(λ⁻¹) + h_fin((λ − 1)⁻¹)) ≤ h_fin(j) + 6c|V|d`** on `K`, for `j ≠ 0`. -/
theorem finHeight_legendreJ_ge (hx : x ∈ K.set) (hj : legendreJ (gen x.1) ≠ 0) :
    2 * (finHeight (gen x.1) + finHeight (gen x.1)⁻¹ + finHeight (gen x.1 - 1)⁻¹) ≤
      finHeight (legendreJ (gen x.1)) + 6 * K.c * K.V.card * deg x.1 := by
  classical
  have hc := CompactlyBounded.c_nonneg hx
  have hg0 := gen_ne_zero x.2.1
  have hg1 := gen_ne_one x
  rw [two_mul_finHeight_sum_eq, finHeight_legendreJ_eq_sum]
  set S := suppFinset x with hS
  set A : FinitePlace (fieldOf x.1) → ℝ := fun v =>
    2 * (log⁺ (v (gen x.1)) + log⁺ (v (gen x.1)⁻¹) + log⁺ (v (gen x.1 - 1)⁻¹)) with hA
  rw [← Finset.sum_filter_add_sum_filter_not S (fun v => residueChar v ∈ K.V)]
  have hA_le : ∀ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v ≤ 6 * K.c := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨h1, h2, h3⟩ := posLog_finite_le hx v hv.2
    rw [hA]
    dsimp only
    linarith
  have hA_le' : ∀ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V),
      A v ≤ log⁺ (v (legendreJ (gen x.1))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have h2 : residueChar v ≠ 2 := fun h => hv.2 (h ▸ K.two_mem)
    exact posLog_legendreJ_ge v hg0 hg1 h2 hj
  have hcard := card_filter_residueChar_mem_le x S K.V
  have hcard' : ((S.filter (fun v => residueChar v ∈ K.V)).card : ℝ) ≤ K.V.card * deg x.1 := by
    exact_mod_cast hcard
  calc ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), A v +
        ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), A v
      ≤ ∑ v ∈ S.filter (fun v => residueChar v ∈ K.V), 6 * K.c +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) :=
        add_le_add (Finset.sum_le_sum hA_le) (Finset.sum_le_sum hA_le')
    _ = 6 * K.c * (S.filter (fun v => residueChar v ∈ K.V)).card +
          ∑ v ∈ S.filter (fun v => ¬ residueChar v ∈ K.V), log⁺ (v (legendreJ (gen x.1))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 6 * K.c * (K.V.card * deg x.1) + ∑ v ∈ S, log⁺ (v (legendreJ (gen x.1))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hcard' (by positivity)) ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.posLog_nonneg
    _ = _ := by ring

/-! ### The height comparison -/

/-- **IUT IV, Corollary 2.2(i) for the Legendre curves** (`LegendreHeightHyp P K`):
`(1/6)·log(q_∀(E_λ)) ≈ ht_{𝒪(1)}(λ)` on every compactly bounded subset `K`, with the explicit
constants `log 2 / 3` and `c|V| + c + log 2 / 3`. -/
theorem legendreHeight (P : CurveProviders) (K : CompactlyBounded) : LegendreHeightHyp P K := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  constructor
  · refine ⟨Real.log 2 / 3, fun x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h_eq_finHeight_div, htCan]
    have hd := deg_pos_real x.1
    have h1 := finHeight_legendreJ_le x
    have h2 := finHeight_le_logHeight₁ (gen x.1)
    have h3 := finHeight_le_logHeight₁ (gen x.1)⁻¹
    have h4 := finHeight_le_logHeight₁ (gen x.1 - 1)⁻¹
    rw [Height.logHeight₁_inv] at h3 h4
    have h5 : Height.logHeight₁ (gen x.1 - 1) ≤
        deg x.1 * Real.log 2 + Height.logHeight₁ (gen x.1) := by
      have := Height.logHeight₁_sub_le (gen x.1) 1
      rwa [Height.logHeight₁_one, add_zero, totalWeight_eq_finrank, ← deg_eq_finrank] at this
    have key : 1 / 6 * finHeight (legendreJ (gen x.1)) ≤
        Height.logHeight₁ (gen x.1) + Real.log 2 / 3 * deg x.1 := by linarith
    rw [div_add' _ _ _ hd.ne', ← mul_div_assoc]
    exact div_le_div_of_nonneg_right key hd.le
  · refine ⟨K.c * K.V.card + K.c + Real.log 2 / 3, fun x hx => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h_eq_finHeight_div, htCan]
    have hd := deg_pos_real x.1
    have hc := CompactlyBounded.c_nonneg hx
    have hcV : 0 ≤ K.c * K.V.card := mul_nonneg hc (Nat.cast_nonneg _)
    by_cases hj : legendreJ (gen x.1) = 0
    · have hg6 : gen x.1 ^ 6 = 1 :=
        pow_six_eq_one_of_legendreJ_eq_zero (gen_ne_zero x.2.1) (gen_ne_one x) hj
      have h0 : Height.logHeight₁ (gen x.1) = 0 := by
        have := Height.logHeight₁_pow (gen x.1) 6
        rw [hg6, Height.logHeight₁_one] at this
        push_cast at this
        linarith
      rw [h0, hj, finHeight_zero, zero_div, mul_zero, zero_add]
      linarith
    have h1 := finHeight_legendreJ_ge hx hj
    obtain ⟨h2, h3, h4⟩ := logHeight₁_le_finHeight_add hx
    rw [Height.logHeight₁_inv] at h3 h4
    have h5 : Height.logHeight₁ (gen x.1) ≤
        deg x.1 * Real.log 2 + Height.logHeight₁ (gen x.1 - 1) := by
      have := Height.logHeight₁_add_le (gen x.1 - 1) 1
      rwa [sub_add_cancel, Height.logHeight₁_one, add_zero, totalWeight_eq_finrank,
        ← deg_eq_finrank] at this
    have key : Height.logHeight₁ (gen x.1) ≤
        1 / 6 * finHeight (legendreJ (gen x.1)) +
          (K.c * K.V.card + K.c + Real.log 2 / 3) * deg x.1 := by linarith
    rw [div_le_iff₀ hd, add_mul, mul_assoc, div_mul_cancel₀ _ hd.ne']
    exact key

end Iut.Tripod
