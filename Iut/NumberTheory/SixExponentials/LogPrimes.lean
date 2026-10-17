/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.NumberTheory.SixExponentials.Basic

/-!
# Logarithms of prime numbers

This file proves [FrdI], Lemma 6.5 (S. Mochizuki, *The Geometry of Frobenioids I*, p. 116):

* (i) the real numbers `log p`, `p` prime, are linearly independent over `ℚ`
  (`Real.linearIndependent_log_primes`);
* (ii) if `p₀, …, p₅` are distinct primes, there are no `λ₁, λ₂ ∈ ℚ_{>0}` with
  `log p₀ / log p₁ = λ₁ · log p₂ / log p₃ = λ₂ · log p₄ / log p₅`
  (`Real.not_exists_pos_rat_log_div_eq`; the positivity assumption is not needed,
  see `Real.not_exists_rat_log_div_eq`).

Part (i) follows from unique factorisation (via `padicValRat`). Part (ii) follows from the
rational six exponentials theorem `Real.exists_rat_eq_of_rpow_rat`: with `t = log p₀ / log p₁`,
`λ₁ = a₁ / b₁`, `λ₂ = a₂ / b₂` and `P = p₁`, `Q = p₃ ^ b₁`, `R = p₅ ^ b₂`, the numbers
`P ^ t = p₀`, `Q ^ t = p₂ ^ a₁`, `R ^ t = p₄ ^ a₂` are rational, `P, Q, R` are multiplicatively
independent by (i), and `t` is irrational by (i), a contradiction.
(Mochizuki deduces (ii) from Lang's six exponentials theorem; the indices here start at `0`.)
-/

namespace Real

/-- The `q`-adic valuation of `∏_{p ∈ s} p ^ z p`, for primes `p, q`. -/
private lemma padicValRat_prod_zpow (s : Finset Nat.Primes) (z : Nat.Primes → ℤ)
    (q : Nat.Primes) :
    padicValRat q (∏ p ∈ s, ((p : ℕ) : ℚ) ^ z p) = if q ∈ s then z q else 0 := by
  classical
  haveI : Fact (q : ℕ).Prime := ⟨q.prop⟩
  have hne : ∀ p : Nat.Primes, ((p : ℕ) : ℚ) ^ z p ≠ 0 :=
    fun p => zpow_ne_zero _ (Nat.cast_ne_zero.mpr p.prop.ne_zero)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, padicValRat.mul (hne a)
      (Finset.prod_ne_zero_iff.mpr fun p _ => hne p), padicValRat.zpow, ih,
      padicValRat.of_nat]
    by_cases hqa : q = a
    · subst hqa
      rw [padicValNat.self q.prop.one_lt, if_neg ha, if_pos (Finset.mem_insert_self _ _)]
      simp
    · haveI : Fact (a : ℕ).Prime := ⟨a.prop⟩
      rw [padicValNat_primes (fun h => hqa (Subtype.ext h))]
      simp [Finset.mem_insert, hqa]

/-- **[FrdI], Lemma 6.5(i)**: the logarithms of the prime numbers are linearly independent
over `ℚ`. -/
theorem linearIndependent_log_primes :
    LinearIndependent ℚ (fun p : Nat.Primes => log (p : ℕ)) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ, linearIndependent_iff']
  intro s g hg q hq
  have hpos : ∀ p : Nat.Primes, (0 : ℝ) < ((p : ℕ) : ℝ) :=
    fun p => Nat.cast_pos.mpr p.prop.pos
  have h1 : log (∏ p ∈ s, ((p : ℕ) : ℝ) ^ g p) = 0 := by
    rw [log_prod fun p _ => (zpow_pos (hpos p) _).ne']
    simpa [log_zpow, zsmul_eq_mul] using hg
  have h2 := eq_one_of_pos_of_log_eq_zero
    (Finset.prod_pos fun p _ => zpow_pos (hpos p) _) h1
  have h3 : (∏ p ∈ s, ((p : ℕ) : ℚ) ^ g p) = 1 := by
    have : ((∏ p ∈ s, ((p : ℕ) : ℚ) ^ g p : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
      push_cast
      exact h2
    exact_mod_cast this
  have := padicValRat_prod_zpow s g q
  rw [h3, padicValRat.one, if_pos hq] at this
  exact this.symm

/-- Linear independence of the logarithms of finitely many distinct primes, in coordinates. -/
theorem eq_zero_of_sum_rat_mul_log_prime_eq_zero {n : ℕ} {p : Fin n → ℕ}
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (g : Fin n → ℚ)
    (h : ∑ i, (g i : ℝ) * log (p i) = 0) (i : Fin n) : g i = 0 := by
  have hli := linearIndependent_log_primes.comp (fun i => (⟨p i, hp i⟩ : Nat.Primes))
    fun i j hij => hinj (congrArg Subtype.val hij)
  exact Fintype.linearIndependent_iff.mp hli g (by simpa [Rat.smul_def] using h) i

/-- **[FrdI], Lemma 6.5(ii)**, for arbitrary rational `λ₁, λ₂`: if `p₀, …, p₅` are distinct
primes, there are no `λ₁ λ₂ : ℚ` with
`log p₀ / log p₁ = λ₁ · log p₂ / log p₃ = λ₂ · log p₄ / log p₅`. -/
theorem not_exists_rat_log_div_eq {p : Fin 6 → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    ¬ ∃ l₁ l₂ : ℚ, log (p 0) / log (p 1) = l₁ * (log (p 2) / log (p 3)) ∧
      log (p 0) / log (p 1) = l₂ * (log (p 4) / log (p 5)) := by
  rintro ⟨l₁, l₂, h₁, h₂⟩
  have hind := eq_zero_of_sum_rat_mul_log_prime_eq_zero hp hinj
  have hpos : ∀ i, (0 : ℝ) < p i := fun i => Nat.cast_pos.mpr (hp i).pos
  have hlog : ∀ i, 0 < log (p i) := fun i => log_pos (by exact_mod_cast (hp i).one_lt)
  set t := log (p 0) / log (p 1) with ht
  -- `Q ^ t` and `R ^ t` are rational
  have hpow : ∀ (l : ℚ) (i j : Fin 6), t = l * (log (p i) / log (p j)) →
      ((((p j : ℚ) ^ l.den : ℚ)) : ℝ) ^ t = (((p i : ℚ) ^ l.num : ℚ) : ℝ) := by
    intro l i j hl
    have hden : (l : ℝ) * l.den = l.num := by exact_mod_cast Rat.mul_den_eq_num l
    push_cast
    rw [rpow_def_of_pos (pow_pos (hpos j) _), ← exp_log (zpow_pos (hpos i) _), log_pow,
      log_zpow, hl]
    congr 1
    rw [← hden]
    field_simp [(hlog j).ne']
  obtain ⟨x, hx⟩ := exists_rat_eq_of_rpow_rat (p := (p 1 : ℚ)) (q := (p 3 : ℚ) ^ l₁.den)
    (r := (p 5 : ℚ) ^ l₂.den) (u := t) (by exact_mod_cast (hp 1).pos)
    (pow_pos (by exact_mod_cast (hp 3).pos) _) (pow_pos (by exact_mod_cast (hp 5).pos) _)
    (by
      intro a b c habc
      have hreal := congrArg (Rat.cast : ℚ → ℝ) habc
      push_cast at hreal
      have hl := congrArg log hreal
      rw [log_one, log_mul (mul_pos (zpow_pos (hpos 1) _) (zpow_pos (pow_pos (hpos 3) _) _)).ne'
          (zpow_pos (pow_pos (hpos 5) _) _).ne',
        log_mul (zpow_pos (hpos 1) _).ne' (zpow_pos (pow_pos (hpos 3) _) _).ne',
        log_zpow, log_zpow, log_zpow, log_pow, log_pow] at hl
      have hsum : ∑ i, ((![0, (a : ℚ), 0, b * l₁.den, 0, c * l₂.den] i : ℚ) : ℝ) *
          log (p i) = 0 := by
        simp only [Fin.sum_univ_six]
        simp
        linear_combination hl
      have ha := hind _ hsum 1
      have hb := hind _ hsum 3
      have hc := hind _ hsum 5
      simp only [Matrix.cons_val] at ha hb hc
      refine ⟨by exact_mod_cast ha, ?_, ?_⟩
      · exact_mod_cast (mul_eq_zero.mp hb).resolve_right (by positivity)
      · exact_mod_cast (mul_eq_zero.mp hc).resolve_right (by positivity))
    ⟨p 0, by
      push_cast
      rw [rpow_def_of_pos (hpos 1), ht, mul_div_cancel₀ _ (hlog 1).ne', exp_log (hpos 0)]⟩
    ⟨_, hpow l₁ 2 3 h₁⟩ ⟨_, hpow l₂ 4 5 h₂⟩
  -- but `t` is irrational
  have hden : (x : ℝ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
  have hsum : ∑ i, ((![(x.den : ℚ), -x.num, 0, 0, 0, 0] i : ℚ) : ℝ) * log (p i) = 0 := by
    simp only [Fin.sum_univ_six]
    simp only [Fin.isValue, Matrix.cons_val_zero, Rat.cast_natCast, Matrix.cons_val_one,
      Rat.cast_neg, Rat.cast_intCast, neg_mul, Matrix.cons_val, Rat.cast_zero, zero_mul, add_zero]
    rw [ht] at hx
    rw [← hden, ← hx]
    field_simp [(hlog 1).ne']
    ring
  have := hind _ hsum 0
  simp at this

/-- **[FrdI], Lemma 6.5(ii)**: if `p₀, …, p₅` are distinct primes, there are no
`λ₁ λ₂ ∈ ℚ_{>0}` with `log p₀ / log p₁ = λ₁ · log p₂ / log p₃ = λ₂ · log p₄ / log p₅`. -/
theorem not_exists_pos_rat_log_div_eq {p : Fin 6 → ℕ} (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) :
    ¬ ∃ l₁ l₂ : ℚ, 0 < l₁ ∧ 0 < l₂ ∧ log (p 0) / log (p 1) = l₁ * (log (p 2) / log (p 3)) ∧
      log (p 0) / log (p 1) = l₂ * (log (p 4) / log (p 5)) := by
  rintro ⟨l₁, l₂, -, -, h₁, h₂⟩
  exact not_exists_rat_log_div_eq hp hinj ⟨l₁, l₂, h₁, h₂⟩

end Real
