/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.TateStructure

/-!
# The Tate coordinates of the points entering the isogeny estimate

Let `E` be an elliptic curve with a Tate structure over a complete discretely valued field `k` of
residue characteristic `≠ 2` (`Iut.TateStructure`): `k^×/q^ℤ ≃ E(k)`, with the point of a unit
`u ∉ q^ℤ` having `x`-coordinate `u²X(u) + r` in the model of `E` (`X` the Tate coordinate). For
the isogeny estimate of the cyclic-subgroup bound we need the norms of the ratios

`(x(T) − x(R + Q)) / (x(T) − x(Q))`

for a point `T` of order `2`, a point `R` with `2R = T`, and a nonzero point `Q` of the graph line
`μ_ℓ` (ℓ odd). In Tate coordinates `T ↔ τ` with `τ² ∈ q^ℤ`, `R ↔ ρ` with `ρ² ∈ τ q^ℤ`,
`Q ↔ ζ` with `ζ^ℓ = 1`, `ζ ≠ 1`, and after normalizing to the annulus `‖q‖ < ‖·‖ ≤ 1`:

* if `‖τ‖² = ‖q‖` (`T` reduces to the node), then `‖ρ‖⁴ ∈ {‖q‖, ‖q‖³}` and the ratio has
  `‖·‖⁴ ≤ ‖q‖` (`Iut.CyclicGain.norm_ratio_pow_four_le`): `‖X(τ)‖ ≤ ‖q‖^{1/2}`,
  `‖X(ρζ)‖ ≤ ‖q‖^{1/4}`, `‖X(ζ)‖ ≥ 1`;
* if `τ = −1`, the ratio has norm `≤ 1` (`Iut.CyclicGain.norm_ratio_le_one`), using `‖2‖ = 1`.

The norm estimates of the Tate coordinate `X` are those of `lana-agents/tate-curves-theta`
(`TateParameter.norm_X_sub_node_le`, `TateParameter.norm_X_sub_annulus_le`).
-/

namespace Iut.CyclicGain

open TateCurvesTheta

/-! ### Norm estimates of the Tate coordinate -/

section Norms

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (t : TateParameter K)

/-- Every unit has a representative modulo `q^ℤ` in the annulus `‖q‖ < ‖u‖ ≤ 1`. -/
theorem exists_zpow_mul_mem_annulus (u : Kˣ) :
    ∃ n : ℤ, ‖(t.q : K)‖ < ‖((t.q ^ n * u : Kˣ) : K)‖ ∧ ‖((t.q ^ n * u : Kˣ) : K)‖ ≤ 1 := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hu0 : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  set α : ℝ := -Real.log ‖(t.q : K)‖ with hα
  have hαpos : 0 < α := by
    rw [hα, neg_pos]; exact Real.log_neg hq0 hq1
  set β : ℝ := Real.log ‖(u : K)‖
  have hlogq : Real.log ‖(t.q : K)‖ = -α := by rw [hα, neg_neg]
  refine ⟨⌈β / α⌉, ?_, ?_⟩
  all_goals
    rw [Units.val_mul, norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow]
  · have hn : (⌈β / α⌉ : ℝ) < β / α + 1 := Int.ceil_lt_add_one _
    rw [← Real.log_lt_log_iff hq0 (by positivity), Real.log_mul (by positivity) hu0.ne',
      Real.log_zpow, hlogq]
    have := (lt_div_iff₀ hαpos).mp (by linarith : (⌈β / α⌉ : ℝ) - 1 < β / α)
    nlinarith
  · have hn : β / α ≤ (⌈β / α⌉ : ℝ) := Int.le_ceil _
    rw [← Real.log_le_log_iff (by positivity) one_pos, Real.log_mul (by positivity) hu0.ne',
      Real.log_zpow, hlogq, Real.log_one]
    have := (div_le_iff₀ hαpos).mp hn
    nlinarith

/-- On the middle annulus `‖q‖ < ‖u‖ < 1`, `‖X(u)‖ ≤ max(‖u‖, ‖q‖/‖u‖)`. -/
theorem norm_X_le_of_annulus {u : Kˣ} (hlo : ‖(t.q : K)‖ < ‖(u : K)‖) (hhi : ‖(u : K)‖ < 1) :
    ‖t.X u‖ ≤ max ‖(u : K)‖ (‖(t.q : K)‖ / ‖(u : K)‖) := by
  have hu0 : 0 < ‖(u : K)‖ := lt_trans t.norm_q_pos hlo
  have herr := t.norm_X_sub_annulus_le hlo hhi
  have h0 := t.norm_Xterm_zero hhi
  have h1 := t.norm_Xterm_neg_one hlo
  have hq : ‖(t.q : K)‖ ≤ ‖(t.q : K)‖ / ‖(u : K)‖ := by
    rw [le_div_iff₀ hu0]
    exact mul_le_of_le_one_right (norm_nonneg _) hhi.le
  have heq : t.X u = (t.X u - t.Xterm u 0 - t.Xterm u (-1)) + t.Xterm u 0 + t.Xterm u (-1) := by
    ring
  rw [heq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h1 ▸ le_max_right _ _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (h0 ▸ le_max_left _ _))
  exact herr.trans (hq.trans (le_max_right _ _))

omit [CompleteSpace K] in
/-- `‖1 − a^m‖ ≤ ‖1 − a‖` for `‖a‖ ≤ 1`. -/
theorem norm_one_sub_pow_le {a : K} (ha : ‖a‖ ≤ 1) (m : ℕ) : ‖1 - a ^ m‖ ≤ ‖1 - a‖ := by
  rw [← mul_neg_geom_sum, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) ha

/-- On the unit sphere, away from `1`: `‖X(u)‖ = ‖u/(1 − u)²‖ ≥ 1`. -/
theorem one_le_norm_X {u : Kˣ} (hu : ‖(u : K)‖ = 1) (hu1 : (u : K) ≠ 1) : 1 ≤ ‖t.X u‖ := by
  have herr := t.norm_X_sub_node_le hu
  have h1u : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm)
  have h1u' : ‖1 - (u : K)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_one, norm_neg, hu, max_self]
  have hmain : 1 ≤ ‖(u : K) / (1 - (u : K)) ^ 2‖ := by
    rw [norm_div, norm_pow, hu, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_one₀ (norm_nonneg _) h1u'
  have hlt : ‖t.X u - (u : K) / (1 - (u : K)) ^ 2‖ < ‖(u : K) / (1 - (u : K)) ^ 2‖ :=
    lt_of_le_of_lt herr (lt_of_lt_of_le t.norm_lt_one hmain)
  have heq : t.X u = (t.X u - (u : K) / (1 - (u : K)) ^ 2) + (u : K) / (1 - (u : K)) ^ 2 := by
    ring
  rw [heq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le]
  exact hmain

/-- On the unit sphere, with `‖1 − u‖ = 1`: `‖X(u)‖ ≤ 1`. -/
theorem norm_X_le_one {u : Kˣ} (hu : ‖(u : K)‖ = 1) (hu1 : ‖1 - (u : K)‖ = 1) :
    ‖t.X u‖ ≤ 1 := by
  have herr := t.norm_X_sub_node_le hu
  have hmain : ‖(u : K) / (1 - (u : K)) ^ 2‖ = 1 := by
    rw [norm_div, norm_pow, hu, hu1]; norm_num
  have heq : t.X u = (t.X u - (u : K) / (1 - (u : K)) ^ 2) + (u : K) / (1 - (u : K)) ^ 2 := by
    ring
  rw [heq]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hmain.le)
  exact herr.trans t.norm_lt_one.le

/-- On the unit sphere, away from `1`: `‖X(u)‖ = 1/‖1 − u‖²`. -/
theorem norm_X_eq {u : Kˣ} (hu : ‖(u : K)‖ = 1) (hu1 : (u : K) ≠ 1) :
    ‖t.X u‖ = 1 / ‖1 - (u : K)‖ ^ 2 := by
  have herr := t.norm_X_sub_node_le hu
  have h1u : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu1.symm)
  have h1u' : ‖1 - (u : K)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_one, norm_neg, hu, max_self]
  have hmain' : ‖(u : K) / (1 - (u : K)) ^ 2‖ = 1 / ‖1 - (u : K)‖ ^ 2 := by
    rw [norm_div, norm_pow, hu]
  have hmain : 1 ≤ ‖(u : K) / (1 - (u : K)) ^ 2‖ := by
    rw [hmain', le_div_iff₀ (by positivity), one_mul]
    exact pow_le_one₀ (norm_nonneg _) h1u'
  have hlt : ‖t.X u - (u : K) / (1 - (u : K)) ^ 2‖ < ‖(u : K) / (1 - (u : K)) ^ 2‖ :=
    lt_of_le_of_lt herr (lt_of_lt_of_le t.norm_lt_one hmain)
  have heq : t.X u = (t.X u - (u : K) / (1 - (u : K)) ^ 2) + (u : K) / (1 - (u : K)) ^ 2 := by
    ring
  rw [heq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne, max_eq_right hlt.le,
    hmain']

omit [CompleteSpace K] in
/-- `‖a − b‖ = ‖b‖` if `‖a‖ < ‖b‖`. -/
lemma norm_sub_eq_right {a b : K} (h : ‖a‖ < ‖b‖) : ‖a - b‖ = ‖b‖ := by
  have h' : ‖a‖ ≠ ‖-b‖ := by rw [norm_neg]; exact h.ne
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h', norm_neg,
    max_eq_right h.le]

/-- **The gain at a point of order `2` reducing to the node.** If `‖τ‖² = ‖q‖`,
`‖ρ‖⁴ ∈ {‖q‖, ‖q‖³}`, `‖ζ‖ = 1` and `ζ ≠ 1`, then `‖X(τ) − X(ρζ)‖⁴ ≤ ‖q‖` and
`‖X(τ) − X(ζ)‖ ≥ 1`. -/
theorem node_bounds {τ ρ ζ : Kˣ} (hτ : ‖(τ : K)‖ ^ 2 = ‖(t.q : K)‖)
    (hρ : ‖(ρ : K)‖ ^ 4 = ‖(t.q : K)‖ ∨ ‖(ρ : K)‖ ^ 4 = ‖(t.q : K)‖ ^ 3)
    (hζ : ‖(ζ : K)‖ = 1) (hζ1 : (ζ : K) ≠ 1) :
    ‖t.X τ - t.X (ρ * ζ)‖ ^ 4 ≤ ‖(t.q : K)‖ ∧ 1 ≤ ‖t.X τ - t.X ζ‖ := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hτ0 : 0 < ‖(τ : K)‖ := norm_pos_iff.mpr τ.ne_zero
  have hρ0 : 0 < ‖(ρ : K)‖ := norm_pos_iff.mpr ρ.ne_zero
  have hτ1 : ‖(τ : K)‖ < 1 := by
    by_contra h; nlinarith [one_le_pow₀ (n := 2) (not_lt.mp h)]
  have hτq : ‖(t.q : K)‖ < ‖(τ : K)‖ := by nlinarith
  have hXτ : ‖t.X τ‖ ≤ ‖(τ : K)‖ := by
    refine (norm_X_le_of_annulus t hτq hτ1).trans (max_le le_rfl ?_)
    rw [div_le_iff₀ hτ0]; nlinarith
  have hq3 : ‖(t.q : K)‖ ^ 3 ≤ ‖(t.q : K)‖ := by
    have : ‖(t.q : K)‖ ^ 2 ≤ 1 := pow_le_one₀ hq0.le hq1.le
    nlinarith
  have hq4 : ‖(t.q : K)‖ ^ 4 < ‖(t.q : K)‖ ^ 3 := pow_lt_pow_right_of_lt_one₀ hq0 hq1 (by norm_num)
  have hρ4 : ‖(t.q : K)‖ ^ 4 < ‖(ρ : K)‖ ^ 4 ∧ ‖(ρ : K)‖ ^ 4 < 1 := by
    rcases hρ with h | h <;> rw [h]
    · exact ⟨lt_of_lt_of_le hq4 hq3, hq1⟩
    · exact ⟨hq4, lt_of_le_of_lt hq3 hq1⟩
  have hρq : ‖(t.q : K)‖ < ‖(ρ : K)‖ :=
    lt_of_pow_lt_pow_left₀ 4 hρ0.le hρ4.1
  have hρ1 : ‖(ρ : K)‖ < 1 := by
    by_contra h; nlinarith [one_le_pow₀ (n := 4) (not_lt.mp h)]
  have hρζ : ‖((ρ * ζ : Kˣ) : K)‖ = ‖(ρ : K)‖ := by rw [Units.val_mul, norm_mul, hζ, mul_one]
  have hXρζ : ‖t.X (ρ * ζ)‖ ^ 4 ≤ ‖(t.q : K)‖ := by
    have h := norm_X_le_of_annulus t (u := ρ * ζ) (hρζ ▸ hρq) (hρζ ▸ hρ1)
    rw [hρζ] at h
    refine (pow_le_pow_left₀ (norm_nonneg _) h 4).trans ?_
    rcases le_total ‖(ρ : K)‖ (‖(t.q : K)‖ / ‖(ρ : K)‖) with hm | hm
    · rw [max_eq_right hm, div_pow]
      rw [div_le_iff₀ (by positivity)]
      rcases hρ with h' | h' <;> rw [h'] <;> nlinarith [pow_pos hq0 3]
    · rw [max_eq_left hm]
      rcases hρ with h' | h' <;> rw [h']
      · exact hq3
  refine ⟨?_, ?_⟩
  · have hXτ4 : ‖t.X τ‖ ^ 4 ≤ ‖(t.q : K)‖ := by
      calc ‖t.X τ‖ ^ 4 ≤ ‖(τ : K)‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hXτ 4
        _ = ‖(t.q : K)‖ ^ 2 := by rw [← hτ]; ring
        _ ≤ ‖(t.q : K)‖ := by nlinarith
    rw [sub_eq_add_neg]
    refine (pow_le_pow_left₀ (norm_nonneg _) (IsUltrametricDist.norm_add_le_max _ _) 4).trans ?_
    rw [norm_neg]
    rcases le_total ‖t.X τ‖ ‖t.X (ρ * ζ)‖ with hm | hm
    · rw [max_eq_right hm]; exact hXρζ
    · rw [max_eq_left hm]; exact hXτ4
  · have hXζ := one_le_norm_X t hζ hζ1
    rw [norm_sub_eq_right (lt_of_le_of_lt hXτ (lt_of_lt_of_le hτ1 hXζ))]
    exact hXζ

/-- **The bound at the point of order `2` not reducing to the node** (`τ = −1`), for residue
characteristic `≠ 2`: if `ρ² = −1` or `‖ρ‖² = ‖q‖`, and `ζ ≠ 1` is an `ℓ`-th root of unity with
`ℓ` odd, then `‖X(−1) − X(ρζ)‖ ≤ 1` and `‖X(−1) − X(ζ)‖ ≥ 1`. -/
theorem minus_one_bounds (h2 : ‖(2 : K)‖ = 1) {ρ ζ : Kˣ}
    (hρ : (ρ : K) ^ 2 = -1 ∨ ‖(ρ : K)‖ ^ 2 = ‖(t.q : K)‖) {ℓ : ℕ} (hℓ : Odd ℓ)
    (hζℓ : ζ ^ ℓ = 1) (hζ1 : (ζ : K) ≠ 1) :
    ‖t.X (-1) - t.X (ρ * ζ)‖ ≤ 1 ∧ 1 ≤ ‖t.X (-1) - t.X ζ‖ := by
  have hq0 := t.norm_q_pos
  have hq1 := t.norm_lt_one
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hℓ)
  have hζ : ‖(ζ : K)‖ = 1 := by
    have h := congrArg (fun u : Kˣ => ‖(u : K)‖) hζℓ
    simp only [Units.val_pow_eq_pow_val, norm_pow, Units.val_one, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ0).mp h
  have hm1 : ‖((-1 : Kˣ) : K)‖ = 1 := by simp
  have h1m1 : ‖1 - ((-1 : Kˣ) : K)‖ = 1 := by
    rw [Units.val_neg, Units.val_one, sub_neg_eq_add, one_add_one_eq_two, h2]
  have hXm1 : ‖t.X (-1)‖ ≤ 1 := norm_X_le_one t hm1 h1m1
  obtain ⟨k, hk⟩ := hℓ
  refine ⟨?_, ?_⟩
  · -- the numerator
    have hXρζ : ‖t.X (ρ * ζ)‖ ≤ 1 := by
      rcases hρ with hρ | hρ
      · have hρn : ‖(ρ : K)‖ = 1 := by
          have h := congrArg norm hρ
          rw [norm_pow, norm_neg, norm_one] at h
          exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h
        have hρζ : ‖((ρ * ζ : Kˣ) : K)‖ = 1 := by
          rw [Units.val_mul, norm_mul, hρn, hζ, mul_one]
        refine norm_X_le_one t hρζ ?_
        -- `‖1 − ρζ‖ = 1`: otherwise `‖1 − ρ^ℓ‖ < 1`, `ρ^ℓ = ±ρ`, and `‖2‖ = ‖1 − ρ²‖ < 1`
        have hle : ‖1 - ((ρ * ζ : Kˣ) : K)‖ ≤ 1 := by
          rw [sub_eq_add_neg]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
          rw [norm_one, norm_neg, hρζ, max_self]
        refine le_antisymm hle (not_lt.mp fun hlt => ?_)
        have hpow := norm_one_sub_pow_le (a := ((ρ * ζ : Kˣ) : K)) hρζ.le ℓ
        have hρℓ : ((ρ * ζ : Kˣ) : K) ^ ℓ = (-1) ^ k * (ρ : K) := by
          rw [Units.val_mul, mul_pow, ← Units.val_pow_eq_pow_val ζ, hζℓ, Units.val_one, mul_one,
            hk, pow_succ, pow_mul, hρ, mul_comm]
        rw [hρℓ] at hpow
        have hsmall : ‖1 - (-1) ^ k * (ρ : K)‖ < 1 := lt_of_le_of_lt hpow hlt
        have hbig : ‖1 + (-1) ^ k * (ρ : K)‖ ≤ 1 := by
          refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
          rw [norm_one, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hρn, max_self]
        have hprod : (1 - (-1) ^ k * (ρ : K)) * (1 + (-1) ^ k * (ρ : K)) = 2 := by
          have : ((-1 : K) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          linear_combination (-(((-1 : K) ^ k) ^ 2)) * hρ + this
        have := congrArg norm hprod
        rw [norm_mul, h2] at this
        nlinarith [norm_nonneg (1 - (-1) ^ k * (ρ : K)), norm_nonneg (1 + (-1) ^ k * (ρ : K))]
      · have hρ0 : 0 < ‖(ρ : K)‖ := norm_pos_iff.mpr ρ.ne_zero
        have hρ1 : ‖(ρ : K)‖ < 1 := by
          by_contra h; nlinarith [one_le_pow₀ (n := 2) (not_lt.mp h)]
        have hρq : ‖(t.q : K)‖ < ‖(ρ : K)‖ := by nlinarith
        have hρζ : ‖((ρ * ζ : Kˣ) : K)‖ = ‖(ρ : K)‖ := by
          rw [Units.val_mul, norm_mul, hζ, mul_one]
        refine (norm_X_le_of_annulus t (hρζ ▸ hρq) (hρζ ▸ hρ1)).trans (max_le ?_ ?_)
        · rw [hρζ]; exact hρ1.le
        · rw [hρζ, div_le_iff₀ hρ0]; nlinarith
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hXm1 ?_)
    rw [norm_neg]; exact hXρζ
  · -- the denominator
    by_cases hlt : ‖1 - (ζ : K)‖ < 1
    · have hXζ := norm_X_eq t hζ hζ1
      have h1ζ : 0 < ‖1 - (ζ : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ1.symm)
      have hgt : 1 < ‖t.X ζ‖ := by
        rw [hXζ, lt_div_iff₀ (by positivity), one_mul]
        exact pow_lt_one₀ (norm_nonneg _) hlt two_ne_zero
      rw [norm_sub_eq_right (lt_of_le_of_lt hXm1 hgt)]
      exact hgt.le
    · have h1ζ : ‖1 - (ζ : K)‖ = 1 := by
        refine le_antisymm ?_ (not_lt.mp hlt)
        rw [sub_eq_add_neg]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
        rw [norm_one, norm_neg, hζ, max_self]
      -- `‖1 + ζ‖ = 1`: otherwise `‖1 − ζ²‖ < 1` and `ζ = (ζ²)^(k+1)`
      have h1ζ' : ‖1 + (ζ : K)‖ = 1 := by
        have hle : ‖1 + (ζ : K)‖ ≤ 1 := by
          refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
          rw [norm_one, hζ, max_self]
        refine le_antisymm hle (not_lt.mp fun hlt' => ?_)
        have hsq : ‖1 - (ζ : K) ^ 2‖ < 1 := by
          rw [show 1 - (ζ : K) ^ 2 = (1 - ζ) * (1 + ζ) by ring, norm_mul, h1ζ, one_mul]
          exact hlt'
        have hζsq : ‖(ζ : K) ^ 2‖ ≤ 1 := by rw [norm_pow, hζ, one_pow]
        have hpow := norm_one_sub_pow_le hζsq (k + 1)
        have hζeq : ((ζ : K) ^ 2) ^ (k + 1) = ζ := by
          rw [← pow_mul, show 2 * (k + 1) = ℓ + 1 by omega, pow_succ,
            ← Units.val_pow_eq_pow_val ζ, hζℓ, Units.val_one, one_mul]
        rw [hζeq, h1ζ] at hpow
        linarith
      have h4 : ‖(4 : K)‖ = 1 := by
        rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2, one_mul]
      have hm1v : ((-1 : Kˣ) : K) = -1 := by simp
      have e1 := t.norm_X_sub_node_le hm1
      have e2 := t.norm_X_sub_node_le hζ
      rw [hm1v] at e1
      have hmain : ‖(-1 : K) / (1 - (-1 : K)) ^ 2 - (ζ : K) / (1 - (ζ : K)) ^ 2‖ = 1 := by
        have h1ζ0 : (1 - (ζ : K)) ≠ 0 := sub_ne_zero.mpr hζ1.symm
        have hfour : (4 : K) ≠ 0 := by intro h; rw [h, norm_zero] at h4; exact zero_ne_one h4
        have key : (-1 : K) / (1 - (-1 : K)) ^ 2 - (ζ : K) / (1 - (ζ : K)) ^ 2 =
            -((1 + ζ) ^ 2 / (4 * (1 - ζ) ^ 2)) := by
          have h4' : (1 - (-1 : K)) ^ 2 = 4 := by norm_num
          rw [h4']
          field_simp
          ring
        rw [key]
        rw [norm_neg, norm_div, norm_mul, norm_pow, norm_pow, h1ζ, h1ζ', h4]
        norm_num
      have heq : t.X (-1) - t.X ζ = ((-1 : K) / (1 - (-1 : K)) ^ 2 - (ζ : K) / (1 - (ζ : K)) ^ 2) +
          ((t.X (-1) - (-1 : K) / (1 - (-1 : K)) ^ 2) -
            (t.X ζ - (ζ : K) / (1 - (ζ : K)) ^ 2)) := by ring
      have herr : ‖(t.X (-1) - (-1 : K) / (1 - (-1 : K)) ^ 2) -
          (t.X ζ - (ζ : K) / (1 - (ζ : K)) ^ 2)‖ < 1 := by
        rw [sub_eq_add_neg]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
        rw [norm_neg]
        exact max_lt (lt_of_le_of_lt e1 hq1) (lt_of_le_of_lt e2 hq1)
      have hne : ‖(t.X (-1) - (-1 : K) / (1 - (-1 : K)) ^ 2) -
          (t.X ζ - (ζ : K) / (1 - (ζ : K)) ^ 2)‖ ≠
          ‖(-1 : K) / (1 - (-1 : K)) ^ 2 - (ζ : K) / (1 - (ζ : K)) ^ 2‖ := by
        rw [hmain]; exact herr.ne
      rw [heq, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hmain,
        max_eq_right herr.le]

end Norms

end Iut.CyclicGain

/-! ### Tate classes of points -/

namespace Iut.CyclicGain

open WeierstrassCurve TateCurvesTheta
open scoped Classical Valued

universe u

variable {k : Type u} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))] [CompleteSpace k]
  {E : WeierstrassCurve k} (S : TateStructure E)

/-- **Tate coordinates of a nonzero point**: every nonzero point `P = (x, y)` of `E(k)` is the
point of a unit `u` in the annulus `‖q‖ < ‖u‖ ≤ 1`, and `x = u_C² X(u) + r_C` for the change of
variables `C` of the Tate structure. -/
theorem exists_unit_of_some {x y : k} (h : E.toAffine.Nonsingular x y) :
    ∃ u : kˣ, S.ofUnit u = Affine.Point.some x y h ∧ ‖(S.t.q : k)‖ < ‖(u : k)‖ ∧
      ‖(u : k)‖ ≤ 1 ∧ x = (S.C.u : k) ^ 2 * S.t.X u + S.C.r := by
  obtain ⟨u₀, hu₀⟩ := S.ofUnit_surjective (Affine.Point.some x y h)
  obtain ⟨n, hlo, hhi⟩ := exists_zpow_mul_mem_annulus S.t u₀
  set u := S.t.q ^ n * u₀ with hu
  have hPu : S.ofUnit u = Affine.Point.some x y h := by
    rw [← hu₀, S.ofUnit_eq_iff]
    exact ⟨-n, by rw [hu, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]⟩
  refine ⟨u, hPu, hlo, hhi, ?_⟩
  have hoff : ∀ m : ℤ, (S.t.q : k) ^ m * (u : k) ≠ 1 := by
    intro m hm
    have hu1 : S.t.q ^ m * u = 1 := Units.ext (by simpa using hm)
    have : S.ofUnit u = 0 := by
      rw [← S.ofUnit_one, S.ofUnit_eq_iff]
      exact ⟨m, by rw [hu1]⟩
    rw [hPu] at this
    exact Affine.Point.some_ne_zero h this
  have hx := S.iso_x u hoff
  change xCoord S.C (S.ofUnit u) = S.t.X u at hx
  rw [hPu] at hx
  change (x - S.C.r) / (S.C.u : k) ^ 2 = S.t.X u at hx
  rw [← hx]
  field_simp [Units.ne_zero]
  ring

/-- The norms `‖q‖^m` are strictly decreasing in `m`: from `‖q‖^k < ‖q‖^m ≤ 1` follows
`0 ≤ m < k`. -/
lemma zpow_bounds {a : ℝ} (ha₀ : 0 < a) (ha₁ : a < 1) {m : ℤ} {k : ℕ} (hlo : a ^ k < a ^ m)
    (hhi : a ^ m ≤ 1) : 0 ≤ m ∧ m < k := by
  refine ⟨?_, ?_⟩
  · by_contra hm
    rw [not_le] at hm
    have := zpow_lt_zpow_right_of_lt_one₀ ha₀ ha₁ hm
    rw [zpow_zero] at this
    linarith
  · rw [← zpow_natCast] at hlo
    exact (zpow_lt_zpow_iff_right_of_lt_one₀ ha₀ ha₁).mp hlo

/-- **The Tate class of a point of order `2`**: its annulus representative is `−1` or has
`‖τ‖² = ‖q‖`. -/
theorem two_torsion_class {T : E.toAffine.Point} (hT0 : T ≠ 0) (hT2 : T + T = 0) {τ : kˣ}
    (hτ : S.ofUnit τ = T) (hlo : ‖(S.t.q : k)‖ < ‖(τ : k)‖) (hhi : ‖(τ : k)‖ ≤ 1) :
    (τ : k) = -1 ∨ ‖(τ : k)‖ ^ 2 = ‖(S.t.q : k)‖ := by
  have hq0 := S.t.norm_q_pos
  have hq1 := S.t.norm_lt_one
  have h2 : S.ofUnit (τ * τ) = S.ofUnit 1 := by rw [S.ofUnit_mul, hτ, hT2, S.ofUnit_one]
  obtain ⟨n, hn⟩ := (S.ofUnit_eq_iff _ _).mp h2
  have hsq : (τ : k) ^ 2 = (S.t.q : k) ^ (-n) := by
    have := congrArg (fun v : kˣ => (v : k)) hn
    simp only [Units.val_one, Units.val_mul, Units.val_zpow_eq_zpow_val] at this
    rw [zpow_neg]
    have hq' : (S.t.q : k) ^ n ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
    field_simp
    linear_combination -this
  have hnorm : ‖(τ : k)‖ ^ 2 = ‖(S.t.q : k)‖ ^ (-n) := by rw [← norm_pow, hsq, norm_zpow]
  have hτ0 : 0 < ‖(τ : k)‖ := lt_trans hq0 hlo
  obtain ⟨h0, h2'⟩ := zpow_bounds hq0 hq1 (m := -n) (k := 2)
    (by rw [← hnorm]; exact pow_lt_pow_left₀ hlo hq0.le two_ne_zero)
    (by rw [← hnorm]; exact pow_le_one₀ hτ0.le hhi)
  rcases (show -n = 0 ∨ -n = 1 by omega) with h | h
  · left
    rw [h, zpow_zero] at hsq
    rcases sq_eq_one_iff.mp hsq with h1 | h1
    · exfalso; apply hT0
      rw [← hτ, show τ = 1 from Units.ext h1, S.ofUnit_one]
    · exact h1
  · right
    rw [hnorm, h, zpow_one]

/-- **The Tate class of a half of a point of order `2`** reducing to the node:
`‖ρ‖⁴ ∈ {‖q‖, ‖q‖³}`. -/
theorem half_class_node {T R : E.toAffine.Point} (hRT : R + R = T) {τ ρ : kˣ}
    (hτ : S.ofUnit τ = T) (hρ : S.ofUnit ρ = R) (hτn : ‖(τ : k)‖ ^ 2 = ‖(S.t.q : k)‖)
    (hlo : ‖(S.t.q : k)‖ < ‖(ρ : k)‖) (hhi : ‖(ρ : k)‖ ≤ 1) :
    ‖(ρ : k)‖ ^ 4 = ‖(S.t.q : k)‖ ∨ ‖(ρ : k)‖ ^ 4 = ‖(S.t.q : k)‖ ^ 3 := by
  have hq0 := S.t.norm_q_pos
  have hq1 := S.t.norm_lt_one
  have h2 : S.ofUnit (ρ * ρ) = S.ofUnit τ := by rw [S.ofUnit_mul, hρ, hRT, hτ]
  obtain ⟨n, hn⟩ := (S.ofUnit_eq_iff _ _).mp h2
  have hnorm : ‖(ρ : k)‖ ^ 4 = ‖(S.t.q : k)‖ ^ (-2 * n + 1) := by
    have := congrArg (fun v : kˣ => ‖(v : k)‖) hn
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow] at this
    have hq' : ‖(S.t.q : k)‖ ^ n ≠ 0 := zpow_ne_zero _ hq0.ne'
    have hρ2 : ‖(ρ : k)‖ ^ 2 = ‖(τ : k)‖ * (‖(S.t.q : k)‖ ^ n)⁻¹ := by
      rw [this]; field_simp
    calc ‖(ρ : k)‖ ^ 4 = (‖(ρ : k)‖ ^ 2) ^ 2 := by ring
      _ = ‖(τ : k)‖ ^ 2 * ((‖(S.t.q : k)‖ ^ n) ^ 2)⁻¹ := by rw [hρ2]; ring
      _ = ‖(S.t.q : k)‖ * ‖(S.t.q : k)‖ ^ (-2 * n) := by
        rw [hτn, ← zpow_natCast, ← zpow_mul, ← zpow_neg]
        congr 2
        push_cast
        ring
      _ = ‖(S.t.q : k)‖ ^ (-2 * n + 1) := by rw [zpow_add₀ hq0.ne', zpow_one, mul_comm]
  have hρ0 : 0 < ‖(ρ : k)‖ := lt_trans hq0 hlo
  obtain ⟨h0, h4⟩ := zpow_bounds hq0 hq1 (m := -2 * n + 1) (k := 4)
    (by rw [← hnorm]; exact pow_lt_pow_left₀ hlo hq0.le (by norm_num))
    (by rw [← hnorm]; exact pow_le_one₀ hρ0.le hhi)
  rcases (show -2 * n + 1 = 1 ∨ -2 * n + 1 = 3 by omega) with h | h
  · left; rw [hnorm, h, zpow_one]
  · right; rw [hnorm, h]; norm_cast

/-- **The Tate class of a half of the point of order `2` of class `−1`**: `ρ² = −1` or
`‖ρ‖² = ‖q‖`. -/
theorem half_class_minus_one {T R : E.toAffine.Point} (hRT : R + R = T) {ρ : kˣ}
    (hτ : S.ofUnit (-1) = T) (hρ : S.ofUnit ρ = R)
    (hlo : ‖(S.t.q : k)‖ < ‖(ρ : k)‖) (hhi : ‖(ρ : k)‖ ≤ 1) :
    (ρ : k) ^ 2 = -1 ∨ ‖(ρ : k)‖ ^ 2 = ‖(S.t.q : k)‖ := by
  have hq0 := S.t.norm_q_pos
  have hq1 := S.t.norm_lt_one
  have h2 : S.ofUnit (ρ * ρ) = S.ofUnit (-1) := by rw [S.ofUnit_mul, hρ, hRT, hτ]
  obtain ⟨n, hn⟩ := (S.ofUnit_eq_iff _ _).mp h2
  have hsq : (ρ : k) ^ 2 = -(S.t.q : k) ^ (-n) := by
    have := congrArg (fun v : kˣ => (v : k)) hn
    simp only [Units.val_neg, Units.val_one, Units.val_mul, Units.val_zpow_eq_zpow_val] at this
    rw [zpow_neg, sq]
    have hq' : (S.t.q : k) ^ n ≠ 0 := zpow_ne_zero _ (Units.ne_zero _)
    field_simp
    linear_combination -this
  have hnorm : ‖(ρ : k)‖ ^ 2 = ‖(S.t.q : k)‖ ^ (-n) := by
    rw [← norm_pow, hsq, norm_neg, norm_zpow]
  have hρ0 : 0 < ‖(ρ : k)‖ := lt_trans hq0 hlo
  obtain ⟨h0, h2'⟩ := zpow_bounds hq0 hq1 (m := -n) (k := 2)
    (by rw [← hnorm]; exact pow_lt_pow_left₀ hlo hq0.le two_ne_zero)
    (by rw [← hnorm]; exact pow_le_one₀ hρ0.le hhi)
  rcases (show -n = 0 ∨ -n = 1 by omega) with h | h
  · left; rw [hsq, h, zpow_zero]
  · right; rw [hnorm, h, zpow_one]

end Iut.CyclicGain
