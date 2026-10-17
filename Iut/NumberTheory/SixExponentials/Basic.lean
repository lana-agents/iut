/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.NumberTheory.SixExponentials.ExpPolyZeros
import Iut.NumberTheory.SixExponentials.InterpolationDeterminant

/-!
# The six exponentials theorem, rational case

We prove the following special case of the six exponentials theorem (Siegel, Lang,
Ramachandra): if `p q r` are multiplicatively independent positive rational numbers and `u` is a
real number such that `p ^ u`, `q ^ u`, `r ^ u` are rational, then `u` is rational.

The proof follows M. Waldschmidt, *Six exponentials Theorem – irrationality*, Resonance (June 2021)
(English translation of RMS 131 (2021) no. 3, 26–33), via an interpolation determinant
(M. Laurent's method). For a large integer `N` put `S = N ^ 2`, `T = N ^ 3`, `L = N ^ 6`,
`λ_s = s₁ log p + s₂ log q + s₃ log r` for `s ∈ [0, S) ^ 3` and `ξ_t = t₀ + t₁ u` for
`t ∈ [0, T) ^ 2`, and `Δ = det (exp (λ_s ξ_t))`.

* If `D` is a common denominator of `p, q, r, p ^ u, q ^ u, r ^ u`, then `D ^ (6 S T L) Δ` is an
  integer.
* By `Real.abs_det_exp_mul_le` (vanishing of the first `L (L - 1) / 2` Taylor coefficients),
  `|Δ| ≤ L! exp (e L b - L (L - 1) / 2)` with `b = S T (1 + |u|) (|log p| + |log q| + |log r|)`.
  The explicit parameter inequality `Real.sixExp_param_lt_one` shows that this forces `Δ = 0`
  as soon as `N ≥ 13 + 2 e A + 12 log D`, `A = (|log p| + |log q| + |log r|) (1 + |u|)`.
* If `Δ = 0`, a nontrivial combination `∑ a_s exp (λ_s x)` vanishes at all `ξ_t`; the `λ_s` are
  distinct by multiplicative independence, so by `Real.card_zeros_sum_mul_exp_lt` the `ξ_t`
  are not distinct, i.e. `t₀ + t₁ u = t₀' + t₁' u` for some `t ≠ t'`, whence `u ∈ ℚ`.

Unlike Waldschmidt we do not reduce to `p, q, r > 1`, `u > 0`: we work with absolute values.

## Main results

* `Real.sixExp_param_lt_one`: the explicit parameter inequality (Waldschmidt's (3)).
* `Real.exists_rat_eq_of_rpow_rat`: the rational six exponentials theorem.
-/

namespace Real

/-- **Waldschmidt's parameter inequality (3)**, made explicit. Let `A ≥ 0`, `D ≥ 1` and let `N`
be a natural number with `13 + 2 e A + 12 log D ≤ N`. Put `L = N ^ 6`, `M = L (L - 1) / 2`.
Then `D ^ (6 N² N³ L) · L! · exp (e · L · N⁵ A - M) < 1`.

Computation (with `x = N`, so `x ≥ 13 ≥ 1`): use `L! ≤ L ^ L = exp (6 x⁶ log x)`,
`D ^ k = exp (k log D)` and `2 M = x⁶ (x⁶ - 1)`. The logarithm of the left-hand side is at most
`x⁶ · (6 log x + x⁵ (e A + 6 log D) - (x⁶ - 1) / 2)`. Since `log x ≤ x - 1 < x ≤ x⁵`, the bracket
is `< x⁵ c - (x⁶ - 1) / 2` with `c = 6 + e A + 6 log D`; the hypothesis says `x ≥ 1 + 2 c`, so
`x⁶ - 1 = x · x⁵ - 1 ≥ (1 + 2 c) x⁵ - 1 ≥ 2 c x⁵` and the bracket is negative. -/
theorem sixExp_param_lt_one {N : ℕ} {A D : ℝ} (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hN : 13 + 2 * exp 1 * A + 12 * log D ≤ N) :
    D ^ (6 * (N ^ 2 * N ^ 3) * N ^ 6) * (((N ^ 6).factorial : ℝ) *
      exp (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
        ((N ^ 6 * (N ^ 6 - 1) / 2 : ℕ) : ℝ))) < 1 := by
  have hlogD : 0 ≤ log D := log_nonneg hD
  have heA : 0 ≤ exp 1 * A := mul_nonneg (exp_pos 1).le hA
  have hx13 : (13 : ℝ) ≤ N := by linarith
  have hx0 : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hL1 : 1 ≤ N ^ 6 := Nat.one_le_pow _ _ hN1
  have hcast : ((N ^ 6 : ℕ) : ℝ) = (N : ℝ) ^ 6 := by push_cast; ring
  -- the factorial and the power of `D` as exponentials
  have hfact : ((N ^ 6).factorial : ℝ) ≤ exp ((N : ℝ) ^ 6 * (6 * log N)) := by
    have h1 : ((N ^ 6).factorial : ℝ) ≤ ((N ^ 6 : ℕ) : ℝ) ^ (N ^ 6) := by
      exact_mod_cast Nat.factorial_le_pow _
    have h2 : ((N ^ 6 : ℕ) : ℝ) ^ (N ^ 6) = exp ((N : ℝ) ^ 6 * (6 * log N)) := by
      rw [← exp_log (by positivity : (0 : ℝ) < ((N ^ 6 : ℕ) : ℝ) ^ (N ^ 6))]
      congr 1
      rw [log_pow, hcast, log_pow]
      push_cast
      ring
    exact h1.trans h2.le
  have hDpow : D ^ (6 * (N ^ 2 * N ^ 3) * N ^ 6) =
      exp (6 * (N : ℝ) ^ 5 * (N : ℝ) ^ 6 * log D) := by
    rw [← exp_log (pow_pos (by linarith : (0 : ℝ) < D) _)]
    congr 1
    rw [log_pow]
    push_cast
    ring
  have hM : (((N ^ 6 * (N ^ 6 - 1) / 2 : ℕ) : ℝ)) = (N : ℝ) ^ 6 * ((N : ℝ) ^ 6 - 1) / 2 := by
    have hev : 2 ∣ N ^ 6 * (N ^ 6 - 1) := (Nat.even_mul_pred_self _).two_dvd
    rw [Nat.cast_div hev (by norm_num), Nat.cast_mul, Nat.cast_sub hL1, hcast]
    push_cast
    ring
  -- the exponent is negative
  set c : ℝ := 6 + exp 1 * A + 6 * log D with hc
  have hx5 : (N : ℝ) ≤ (N : ℝ) ^ 5 := le_self_pow₀ (by linarith) (by norm_num)
  have hlogx : log N < (N : ℝ) ^ 5 := by
    have := log_le_sub_one_of_pos hx0
    linarith
  have hx5pos : (0 : ℝ) < (N : ℝ) ^ 5 := by positivity
  have hkey : 6 * log N + (N : ℝ) ^ 5 * (exp 1 * A + 6 * log D) < ((N : ℝ) ^ 6 - 1) / 2 := by
    have h1 : 6 * log N + (N : ℝ) ^ 5 * (exp 1 * A + 6 * log D) < (N : ℝ) ^ 5 * c := by
      rw [hc]
      linarith
    have h2 : (1 + 2 * c) * (N : ℝ) ^ 5 ≤ N * (N : ℝ) ^ 5 := by
      refine mul_le_mul_of_nonneg_right ?_ hx5pos.le
      rw [hc]
      linarith
    have h3 : (N : ℝ) ^ 6 = N * (N : ℝ) ^ 5 := by ring
    linarith
  have hexp : 6 * (N : ℝ) ^ 5 * (N : ℝ) ^ 6 * log D + ((N : ℝ) ^ 6 * (6 * log N) +
      (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
        (N : ℝ) ^ 6 * ((N : ℝ) ^ 6 - 1) / 2)) < 0 := by
    have heq : 6 * (N : ℝ) ^ 5 * (N : ℝ) ^ 6 * log D + ((N : ℝ) ^ 6 * (6 * log N) +
        (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
          (N : ℝ) ^ 6 * ((N : ℝ) ^ 6 - 1) / 2)) = (N : ℝ) ^ 6 *
        (6 * log N + (N : ℝ) ^ 5 * (exp 1 * A + 6 * log D) - ((N : ℝ) ^ 6 - 1) / 2) := by
      rw [hcast]
      ring
    rw [heq]
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith)
  calc D ^ (6 * (N ^ 2 * N ^ 3) * N ^ 6) * (((N ^ 6).factorial : ℝ) *
        exp (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
          ((N ^ 6 * (N ^ 6 - 1) / 2 : ℕ) : ℝ)))
      ≤ exp (6 * (N : ℝ) ^ 5 * (N : ℝ) ^ 6 * log D) * (exp ((N : ℝ) ^ 6 * (6 * log N)) *
          exp (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
            (N : ℝ) ^ 6 * ((N : ℝ) ^ 6 - 1) / 2)) := by
        rw [hDpow, hM]
        gcongr
    _ = exp (6 * (N : ℝ) ^ 5 * (N : ℝ) ^ 6 * log D + ((N : ℝ) ^ 6 * (6 * log N) +
          (exp 1 * (((N ^ 6 : ℕ) : ℝ) * ((N : ℝ) ^ 5 * A)) -
            (N : ℝ) ^ 6 * ((N : ℝ) ^ 6 - 1) / 2))) := by
        rw [exp_add, exp_add]
    _ < 1 := exp_lt_one_iff.mpr hexp

/-- If `x.den ∣ D` and `k ≤ n`, then `D ^ n * x ^ k` is an integer. -/
private lemma exists_int_eq_pow_mul_pow {x : ℚ} {D : ℕ} (hD : x.den ∣ D) {k n : ℕ}
    (hk : k ≤ n) : ∃ z : ℤ, (D : ℝ) ^ n * (x : ℝ) ^ k = z := by
  obtain ⟨m, rfl⟩ := hD
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨((x.den * m : ℕ) : ℤ) ^ j * (m * x.num) ^ k, ?_⟩
  have hx : (x : ℝ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
  push_cast
  rw [← hx]
  ring

/-- Multiplicative independence of `p, q, r` gives `ℤ`-linear independence of their logarithms. -/
private lemma eq_zero_of_log_comb {p q r : ℚ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hind : ∀ a b c : ℤ, p ^ a * q ^ b * r ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0) {a b c : ℤ}
    (h : a * log p + b * log q + c * log r = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  apply hind
  have hpos : (0 : ℝ) < (p : ℝ) ^ a * (q : ℝ) ^ b * (r : ℝ) ^ c :=
    mul_pos (mul_pos (zpow_pos hp' a) (zpow_pos hq' b)) (zpow_pos hr' c)
  have hlog : log ((p : ℝ) ^ a * (q : ℝ) ^ b * (r : ℝ) ^ c) = 0 := by
    rw [log_mul (mul_pos (zpow_pos hp' a) (zpow_pos hq' b)).ne' (zpow_pos hr' c).ne',
      log_mul (zpow_pos hp' a).ne' (zpow_pos hq' b).ne', log_zpow, log_zpow, log_zpow, h]
  have := eq_one_of_pos_of_log_eq_zero hpos hlog
  exact_mod_cast this

/-- The entries of the interpolation matrix: for `a, b, c > 0`,
`exp ((s₁ log a + s₂ log b + s₃ log c) (t₀ + t₁ u))` is a product of natural powers of
`a, b, c, a ^ u, b ^ u, c ^ u`. -/
private lemma exp_comb_mul_comb {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (u : ℝ)
    (s₁ s₂ s₃ t₀ t₁ : ℕ) :
    exp ((s₁ * log a + s₂ * log b + s₃ * log c) * (t₀ + t₁ * u)) =
      a ^ (s₁ * t₀) * b ^ (s₂ * t₀) * c ^ (s₃ * t₀) *
        (a ^ u) ^ (s₁ * t₁) * (b ^ u) ^ (s₂ * t₁) * (c ^ u) ^ (s₃ * t₁) := by
  have e₁ : ∀ {x : ℝ}, 0 < x → ∀ n : ℕ, x ^ n = exp (n * log x) := fun hx n => by
    rw [exp_nat_mul, exp_log hx]
  have e₂ : ∀ {x : ℝ}, 0 < x → ∀ n : ℕ, (x ^ u) ^ n = exp (n * (log x * u)) := fun hx n => by
    rw [exp_nat_mul, ← rpow_def_of_pos hx]
  rw [e₁ ha, e₁ hb, e₁ hc, e₂ ha, e₂ hb, e₂ hc, ← exp_add, ← exp_add, ← exp_add, ← exp_add,
    ← exp_add]
  congr 1
  push_cast
  ring

/-- **Six exponentials theorem, rational case** (Siegel, Lang, Ramachandra; proof of
Waldschmidt 2021). Let `p, q, r` be multiplicatively independent positive rational numbers and
`u` a real number such that `p ^ u`, `q ^ u` and `r ^ u` are rational. Then `u` is rational. -/
theorem exists_rat_eq_of_rpow_rat {p q r : ℚ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hind : ∀ a b c : ℤ, p ^ a * q ^ b * r ^ c = 1 → a = 0 ∧ b = 0 ∧ c = 0) {u : ℝ}
    (hpu : ∃ x : ℚ, (p : ℝ) ^ u = x) (hqu : ∃ x : ℚ, (q : ℝ) ^ u = x)
    (hru : ∃ x : ℚ, (r : ℝ) ^ u = x) : ∃ x : ℚ, u = x := by
  obtain ⟨α, hα⟩ := hpu
  obtain ⟨β, hβ⟩ := hqu
  obtain ⟨γ, hγ⟩ := hru
  have ha : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < r := by exact_mod_cast hr
  -- common denominator and the parameter `N`
  set D : ℕ := p.den * q.den * r.den * α.den * β.den * γ.den with hD
  have hDne : D ≠ 0 := by simp [hD]
  have hD1 : (1 : ℝ) ≤ D := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hDne)
  have hdvd : p.den ∣ D ∧ q.den ∣ D ∧ r.den ∣ D ∧ α.den ∣ D ∧ β.den ∣ D ∧ γ.den ∣ D := by
    rw [hD]
    exact ⟨Dvd.intro (q.den * r.den * α.den * β.den * γ.den) (by ring),
      Dvd.intro (p.den * r.den * α.den * β.den * γ.den) (by ring),
      Dvd.intro (p.den * q.den * α.den * β.den * γ.den) (by ring),
      Dvd.intro (p.den * q.den * r.den * β.den * γ.den) (by ring),
      Dvd.intro (p.den * q.den * r.den * α.den * γ.den) (by ring),
      Dvd.intro (p.den * q.den * r.den * α.den * β.den) (by ring)⟩
  set A₀ : ℝ := |log p| + |log q| + |log r| with hA₀
  set U : ℝ := 1 + |u| with hU
  have hA₀0 : 0 ≤ A₀ := by positivity
  have hU0 : 0 ≤ U := by positivity
  set N : ℕ := ⌈13 + 2 * exp 1 * (A₀ * U) + 12 * log D⌉₊ with hN
  have hNle : 13 + 2 * exp 1 * (A₀ * U) + 12 * log D ≤ N := Nat.le_ceil _
  set S : ℕ := N ^ 2
  set T : ℕ := N ^ 3
  set L : ℕ := N ^ 6
  have hcardS : Fintype.card (Fin S × Fin S × Fin S) = L := by
    simp only [Fintype.card_prod, Fintype.card_fin, S, L]; ring
  have hcardT : Fintype.card (Fin T × Fin T) = L := by
    simp only [Fintype.card_prod, Fintype.card_fin, T, L]; ring
  set eS : Fin L ≃ Fin S × Fin S × Fin S := (Fintype.equivFinOfCardEq hcardS).symm
  set eT : Fin L ≃ Fin T × Fin T := (Fintype.equivFinOfCardEq hcardT).symm
  set l : Fin L → ℝ := fun i =>
    ((eS i).1 : ℕ) * log p + ((eS i).2.1 : ℕ) * log q + ((eS i).2.2 : ℕ) * log r with hl
  set ξ : Fin L → ℝ := fun j => ((eT j).1 : ℕ) + ((eT j).2 : ℕ) * u with hξ
  set Δ : ℝ := (Matrix.of fun i j => exp (l i * ξ j)).det with hΔ
  -- the upper bound
  have hlb : ∀ i, |l i| ≤ (N : ℝ) ^ 2 * A₀ := by
    intro i
    have h1 : (((eS i).1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast ((eS i).1.isLt.le)
    have h2 : (((eS i).2.1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast ((eS i).2.1.isLt.le)
    have h3 : (((eS i).2.2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast ((eS i).2.2.isLt.le)
    calc |l i| ≤ |(((eS i).1 : ℕ) : ℝ) * log p| + |(((eS i).2.1 : ℕ) : ℝ) * log q| +
          |(((eS i).2.2 : ℕ) : ℝ) * log r| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
      _ = (((eS i).1 : ℕ) : ℝ) * |log p| + (((eS i).2.1 : ℕ) : ℝ) * |log q| +
          (((eS i).2.2 : ℕ) : ℝ) * |log r| := by
        simp only [abs_mul, Nat.abs_cast]
      _ ≤ (N : ℝ) ^ 2 * |log p| + (N : ℝ) ^ 2 * |log q| + (N : ℝ) ^ 2 * |log r| := by
        gcongr
      _ = (N : ℝ) ^ 2 * A₀ := by rw [hA₀]; ring
  have hξb : ∀ j, |ξ j| ≤ (N : ℝ) ^ 3 * U := by
    intro j
    have h1 : (((eT j).1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast ((eT j).1.isLt.le)
    have h2 : (((eT j).2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 3 := by exact_mod_cast ((eT j).2.isLt.le)
    calc |ξ j| ≤ |(((eT j).1 : ℕ) : ℝ)| + |(((eT j).2 : ℕ) : ℝ) * u| := abs_add_le _ _
      _ = (((eT j).1 : ℕ) : ℝ) + (((eT j).2 : ℕ) : ℝ) * |u| := by
        simp only [abs_mul, Nat.abs_cast]
      _ ≤ (N : ℝ) ^ 3 + (N : ℝ) ^ 3 * |u| := by gcongr
      _ = (N : ℝ) ^ 3 * U := by rw [hU]; ring
  have hbound : ∀ i j, |l i * ξ j| ≤ (N : ℝ) ^ 5 * (A₀ * U) := by
    intro i j
    rw [abs_mul]
    calc |l i| * |ξ j| ≤ ((N : ℝ) ^ 2 * A₀) * ((N : ℝ) ^ 3 * U) :=
          mul_le_mul (hlb i) (hξb j) (abs_nonneg _) (by positivity)
      _ = (N : ℝ) ^ 5 * (A₀ * U) := by ring
  have hΔle := abs_det_exp_mul_le l ξ hbound
  -- integrality
  have hent : ∀ i j, ∃ z : ℤ, (D : ℝ) ^ (6 * (S * T)) * exp (l i * ξ j) = z := by
    intro i j
    have hle : ∀ {m n : ℕ}, m < S → n < T → m * n ≤ S * T :=
      fun hm hn => Nat.mul_le_mul hm.le hn.le
    have hs₁ := (eS i).1.isLt
    have hs₂ := (eS i).2.1.isLt
    have hs₃ := (eS i).2.2.isLt
    have ht₀ := (eT j).1.isLt
    have ht₁ := (eT j).2.isLt
    obtain ⟨z₁, hz₁⟩ := exists_int_eq_pow_mul_pow hdvd.1 (hle hs₁ ht₀)
    obtain ⟨z₂, hz₂⟩ := exists_int_eq_pow_mul_pow hdvd.2.1 (hle hs₂ ht₀)
    obtain ⟨z₃, hz₃⟩ := exists_int_eq_pow_mul_pow hdvd.2.2.1 (hle hs₃ ht₀)
    obtain ⟨z₄, hz₄⟩ := exists_int_eq_pow_mul_pow hdvd.2.2.2.1 (hle hs₁ ht₁)
    obtain ⟨z₅, hz₅⟩ := exists_int_eq_pow_mul_pow hdvd.2.2.2.2.1 (hle hs₂ ht₁)
    obtain ⟨z₆, hz₆⟩ := exists_int_eq_pow_mul_pow hdvd.2.2.2.2.2 (hle hs₃ ht₁)
    refine ⟨z₁ * z₂ * z₃ * z₄ * z₅ * z₆, ?_⟩
    simp only [hl, hξ]
    rw [exp_comb_mul_comb ha hb hc, hα, hβ, hγ]
    push_cast
    rw [← hz₁, ← hz₂, ← hz₃, ← hz₄, ← hz₅, ← hz₆,
      show (D : ℝ) ^ (6 * (S * T)) = ((D : ℝ) ^ (S * T)) ^ 6 from pow_mul' _ _ _]
    ring
  choose B hB using hent
  have hdetB : (D : ℝ) ^ (6 * (S * T) * L) * Δ = ((Matrix.of B).det : ℝ) := by
    have hsmul := Matrix.det_smul (Matrix.of fun i j => exp (l i * ξ j)) ((D : ℝ) ^ (6 * (S * T)))
    rw [Fintype.card_fin] at hsmul
    calc (D : ℝ) ^ (6 * (S * T) * L) * Δ
        = ((D : ℝ) ^ (6 * (S * T)) • Matrix.of fun i j => exp (l i * ξ j)).det := by
          rw [hsmul, pow_mul]
      _ = ((Int.castRingHom ℝ).mapMatrix (Matrix.of B)).det := by
          congr 1
          ext i j
          simp [hB]
      _ = ((Matrix.of B).det : ℝ) := ((Int.castRingHom ℝ).map_det (Matrix.of B)).symm
  -- hence `Δ = 0`
  have hΔ0 : Δ = 0 := by
    have hlt : |((Matrix.of B).det : ℝ)| < 1 := by
      rw [← hdetB, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg D) _)]
      calc (D : ℝ) ^ (6 * (S * T) * L) * |Δ|
          ≤ (D : ℝ) ^ (6 * (S * T) * L) * ((L.factorial : ℝ) *
              exp (exp 1 * ((L : ℝ) * ((N : ℝ) ^ 5 * (A₀ * U))) -
                ((L * (L - 1) / 2 : ℕ) : ℝ))) := by gcongr
        _ < 1 := sixExp_param_lt_one (by positivity) hD1 hNle
    have hz : (Matrix.of B).det = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast hlt)
    rw [hz, Int.cast_zero] at hdetB
    exact (mul_eq_zero.mp hdetB).resolve_left (pow_ne_zero _ (Nat.cast_ne_zero.mpr hDne))
  -- a nontrivial vanishing combination of exponentials
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hΔ0
  have hlinj : Set.InjOn l (Finset.univ : Finset (Fin L)) := by
    intro i _ i' _ hii'
    have h : (((eS i).1 : ℕ) - ((eS i').1 : ℕ) : ℤ) * log p +
        (((eS i).2.1 : ℕ) - ((eS i').2.1 : ℕ) : ℤ) * log q +
        (((eS i).2.2 : ℕ) - ((eS i').2.2 : ℕ) : ℤ) * log r = 0 := by
      simp only [hl] at hii'
      push_cast
      linear_combination hii'
    obtain ⟨h₁, h₂, h₃⟩ := eq_zero_of_log_comb hp hq hr hind h
    apply eS.injective
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> omega
  have hcard := card_zeros_sum_mul_exp_lt Finset.univ l v hlinj
    (by simpa [Function.ne_iff] using hv0) (Finset.univ.image ξ) (by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      have := congrFun hv j
      simpa [Matrix.vecMul, dotProduct] using this)
  have hninj : ¬ Function.Injective ξ := fun hinj => by
    rw [Finset.card_image_of_injective _ hinj] at hcard
    exact lt_irrefl _ hcard
  obtain ⟨j, j', hjj', hne⟩ := Function.not_injective_iff.mp hninj
  have hne' : eT j ≠ eT j' := fun h => hne (eT.injective h)
  simp only [hξ] at hjj'
  by_cases ht : ((eT j).2 : ℕ) = ((eT j').2 : ℕ)
  · exfalso
    apply hne'
    rw [ht] at hjj'
    have h0 : ((eT j).1 : ℕ) = ((eT j').1 : ℕ) := by exact_mod_cast add_right_cancel hjj'
    exact Prod.ext (Fin.ext h0) (Fin.ext ht)
  · refine ⟨((((eT j').1 : ℕ) : ℚ) - ((eT j).1 : ℕ)) / ((((eT j).2 : ℕ) : ℚ) - ((eT j').2 : ℕ)),
      ?_⟩
    have hden : ((((eT j).2 : ℕ) : ℝ) - ((eT j').2 : ℕ)) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast ht)
    push_cast
    rw [eq_div_iff hden]
    linear_combination hjj'

end Real
