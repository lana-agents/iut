/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Prime selection for Corollary 2.2 (IUT IV, Proposition 2.1(ii) and (P1)–(P3))

The proof of IUT IV, Corollary 2.2 chooses, for an elliptic curve `E_F` of height
`h = log(q_∀)`, a prime `ℓ` such that

* (P1) `√h ≤ ℓ ≤ 10δ·√h·log(2δh)`;
* (P2) `ℓ` divides no nonzero local height `h_v`;
* (P3) if `ℓ = p_v` for some bad place `v` then `h_v < √h`.

The tool is IUT IV, Proposition 2.1(ii): from Chebyshev-type bounds `(2/3)x ≤ θ(x) ≤ (4/3)x`
for `x ≥ ξ_prm`, for every finite set `A` of primes there is a prime `p ∉ A` with
`p ≤ 2(θ_A + ξ_prm)`, where `θ_A = ∑_{p ∈ A} log p`. The Chebyshev bounds themselves are
prime-number-theorem strength and are the explicit certificate `ChebyshevBound`
(taxis #6, `lana-agents/prime-counting`); everything else in this file is proved.

The local heights enter through `LocalHeightData`: a finite family of bad places with
residue characteristics `p_v`, local heights `h_v ≥ 1`, and residue degrees `f_v ≥ 1`,
with `[F : ℚ]·h = ∑_v h_v·f_v·log p_v` and `[F : ℚ] ≤ δ` — the data of the `q`-divisor
of `E_F` in the notation of IUT IV, Theorem 1.10 and [GenEll], Definition 3.3.
-/

universe w

namespace Iut

open Finset Real

/-- **IUT IV, Proposition 2.1(ii)** as an explicit certificate: a threshold `ξ_prm ≥ 5`
beyond which Chebyshev's function `θ(x) = ∑_{p ≤ x} log p` satisfies
`(2/3)·x ≤ θ(x) ≤ (4/3)·x`. Prime-number-theorem strength; not proved here (taxis #6). -/
structure ChebyshevBound where
  /-- The threshold `ξ_prm`. -/
  ξ : ℝ
  /-- `ξ_prm ≥ 5`. -/
  five_le : 5 ≤ ξ
  /-- The lower Chebyshev bound. -/
  lower : ∀ x : ℝ, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x
  /-- The upper Chebyshev bound. -/
  upper : ∀ x : ℝ, ξ ≤ x → Chebyshev.theta x ≤ 4 / 3 * x

/-- `θ_A = ∑_{p ∈ A} log p` for a finite set of natural numbers. -/
noncomputable def thetaSet (A : Finset ℕ) : ℝ := ∑ p ∈ A, Real.log p

lemma thetaSet_nonneg (A : Finset ℕ) : 0 ≤ thetaSet A :=
  Finset.sum_nonneg fun p _ => by
    rcases Nat.eq_zero_or_pos p with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)

lemma log_natCast_nonneg (p : ℕ) : 0 ≤ Real.log p := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- The sum of a nonnegative function over a union is at most the sum of the sums. -/
lemma sum_union_le_of_nonneg {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : ∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have h0 : 0 ≤ ∑ i ∈ s ∩ t, f i := Finset.sum_nonneg fun i _ => hf i
  linarith

/-- The sum of a nonnegative function over a finite union is at most the sum of the
sums. -/
lemma sum_biUnion_le_of_nonneg {ι κ : Type*} [DecidableEq κ] (s : Finset ι)
    (t : ι → Finset κ) (f : κ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    ∑ k ∈ s.biUnion t, f k ≤ ∑ i ∈ s, ∑ k ∈ t i, f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact (sum_union_le_of_nonneg _ _ f hf).trans (by linarith)

/-- `∑_{p ∣ n} log p ≤ log n` for `n ≠ 0`. -/
lemma sum_log_primeFactors_le (n : ℕ) (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hne : ∀ p ∈ n.primeFactors, (p : ℝ) ≠ 0 := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  rw [← Real.log_prod hne]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have := Nat.prod_primeFactors_dvd n
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) this

namespace ChebyshevBound

variable (cheb : ChebyshevBound)

/-- **Proposition 2.1(ii)**: for every finite set `A` of natural numbers there is a
prime `p ∉ A` with `p ≤ 2(θ_A + ξ_prm)`. -/
theorem exists_prime_notMem (A : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ A ∧ (p : ℝ) ≤ 2 * (thetaSet A + cheb.ξ) := by
  set x : ℝ := 2 * (thetaSet A + cheb.ξ) with hx
  have hξ : 0 < cheb.ξ := by linarith [cheb.five_le]
  have hxξ : cheb.ξ ≤ x := by rw [hx]; linarith [thetaSet_nonneg A]
  have hlow := cheb.lower x hxξ
  by_contra hcon
  push Not at hcon
  -- every prime `≤ x` lies in `A`, so `θ(x) ≤ θ_A`
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ A := by
    intro p hp
    have hp' : p ∈ Nat.primesBelow (⌊x⌋₊ + 1) := hp
    rw [Nat.mem_primesBelow] at hp'
    have hple : (p : ℝ) ≤ x := by
      have h1 : p ≤ ⌊x⌋₊ := by omega
      calc (p : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
        _ ≤ x := Nat.floor_le (by linarith)
    by_contra hpA
    exact absurd hple (not_le.mpr (hcon p hp'.2 hpA))
  have hθ : Chebyshev.theta x ≤ thetaSet A := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => log_natCast_nonneg p
  -- but `θ(x) ≥ (2/3)x = (4/3)(θ_A + ξ) > θ_A`
  have : 2 / 3 * x = 4 / 3 * (thetaSet A + cheb.ξ) := by rw [hx]; ring
  linarith [thetaSet_nonneg A]

end ChebyshevBound

/-- **Local height data** of an elliptic curve `E_F` over a number field `F` in the
sense of IUT IV, Theorem 1.10 / [GenEll], Definition 3.3: a finite family of bad places
with residue characteristics `p_v`, local heights `h_v ≥ 1`, and residue degrees
`f_v ≥ 1`, such that `[F : ℚ]·h = ∑_v h_v·f_v·log p_v`, where `h = log(q_∀)` is the
normalized degree of the `q`-divisor. -/
structure LocalHeightData : Type (w + 1) where
  /-- The index type of the bad places. -/
  ι : Type w
  /-- The bad places. -/
  bad : Finset ι
  /-- The residue characteristic of a bad place. -/
  p : ι → ℕ
  /-- The local height `h_v = ord_v(q_v)` at a bad place. -/
  hv : ι → ℕ
  /-- The residue degree `f_v`. -/
  f : ι → ℕ
  /-- The degree `[F : ℚ]`. -/
  deg : ℕ
  /-- `[F : ℚ] ≥ 1`. -/
  one_le_deg : 1 ≤ deg
  /-- Residue characteristics are prime. -/
  p_prime : ∀ v ∈ bad, (p v).Prime
  /-- Local heights at bad places are positive. -/
  one_le_hv : ∀ v ∈ bad, 1 ≤ hv v
  /-- Residue degrees are positive. -/
  one_le_f : ∀ v ∈ bad, 1 ≤ f v
  /-- Over a rational prime, the residue degrees sum to at most `[F : ℚ]`
  (`∑_{v ∣ p} e_v f_v = [F : ℚ]`). -/
  sum_f_le : ∀ q : ℕ, ∑ v ∈ bad.filter (fun v => p v = q), f v ≤ deg

namespace LocalHeightData

variable (L : LocalHeightData)

/-- The height `h = log(q_∀) = (1/[F:ℚ])·∑_v h_v f_v log p_v`. -/
noncomputable def height : ℝ :=
  (∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

/-- The part of `log(q_∀)` supported at the places of residue characteristic `q`. -/
noncomputable def heightEq (q : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v = q), (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

/-- The part of `log(q_∀)` supported away from the residue characteristics `a` and `b`
(for `a = 2`, `b = ℓ`: the `log(q)` of the initial Θ-data, whose bad places are those
not dividing `2ℓ`). -/
noncomputable def heightOther (a b : ℕ) : ℝ :=
  (∑ v ∈ L.bad.filter (fun v => L.p v ≠ a ∧ L.p v ≠ b),
    (L.hv v : ℝ) * L.f v * Real.log (L.p v)) / L.deg

lemma term_nonneg (v : L.ι) : 0 ≤ (L.hv v : ℝ) * L.f v * Real.log (L.p v) :=
  mul_nonneg (by positivity) (log_natCast_nonneg _)

lemma height_nonneg : 0 ≤ L.height :=
  div_nonneg (Finset.sum_nonneg fun v _ => L.term_nonneg v) (by positivity)

lemma deg_mul_height : (L.deg : ℝ) * L.height =
    ∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v) := by
  unfold height
  have h1 := L.one_le_deg
  have : (L.deg : ℝ) ≠ 0 := by exact_mod_cast (by omega : L.deg ≠ 0)
  field_simp

/-- The decomposition `h = h_{(a)} + h_{(b)} + h_{(≠a,≠b)}` of the height by residue
characteristic, for `a ≠ b`. -/
lemma height_eq_add (a b : ℕ) (hab : a ≠ b) :
    L.height = L.heightEq a + L.heightEq b + L.heightOther a b := by
  classical
  unfold height heightEq heightOther
  rw [← add_div, ← add_div]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not L.bad (fun v => L.p v = a),
    ← Finset.sum_filter_add_sum_filter_not (L.bad.filter fun v => ¬ L.p v = a)
      (fun v => L.p v = b), Finset.filter_filter, Finset.filter_filter, add_assoc]
  congr 2
  exact Finset.sum_congr (Finset.filter_congr fun v _ =>
    ⟨fun h => h.2, fun h => ⟨fun h' => hab (h'.symm.trans h), h⟩⟩) fun _ _ => rfl

/-- **The choice of `ℓ` in the proof of Corollary 2.2**, conditions (P1)–(P3): given
Chebyshev bounds, local height data with `[F : ℚ] ≤ δ`, `δ ≥ 2`, and `√h ≥ ξ_prm`, there
is a prime `ℓ` with `√h ≤ ℓ ≤ 10δ·√h·log(2δh)`, dividing no nonzero `h_v`, and with
`h_v < √h` whenever `p_v = ℓ`. -/
theorem exists_prime_selection (cheb : ChebyshevBound) (δ : ℝ) (hδ : 2 ≤ δ)
    (hdeg : (L.deg : ℝ) ≤ δ) (hξ : cheb.ξ ≤ Real.sqrt L.height) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ Real.sqrt L.height ≤ ℓ ∧
      (ℓ : ℝ) ≤ 10 * δ * Real.sqrt L.height * Real.log (2 * δ * L.height) ∧
      (∀ v ∈ L.bad, ¬ ℓ ∣ L.hv v) ∧
      (∀ v ∈ L.bad, L.p v = ℓ → (L.hv v : ℝ) < Real.sqrt L.height) := by
  classical
  obtain ⟨h, hh⟩ : ∃ h, h = L.height := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt h := ⟨_, rfl⟩
  rw [← hh, ← hr] at hξ ⊢
  have hξ5 := cheb.five_le
  have hr5 : 5 ≤ r := hξ5.trans hξ
  have hr0 : 0 < r := by linarith
  have hh0 : 0 ≤ h := hh ▸ L.height_nonneg
  have hrr : r * r = h := hr ▸ Real.mul_self_sqrt hh0
  have hh25 : 25 ≤ h := by nlinarith
  have hlog2δh : 1 ≤ Real.log (2 * δ * h) := by
    have : Real.exp 1 ≤ 2 * δ * h := by
      have := Real.exp_one_lt_d9
      nlinarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * δ * h) := Real.log_le_log (Real.exp_pos 1) this
  have hdegpos : (0 : ℝ) < L.deg := by exact_mod_cast L.one_le_deg
  have hsum : (L.deg : ℝ) * h = ∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v) :=
    hh ▸ L.deg_mul_height
  -- the places with large local height
  obtain ⟨big, hbig⟩ : ∃ big : Finset L.ι, ∀ v, v ∈ big ↔ v ∈ L.bad ∧ r ≤ (L.hv v : ℝ) :=
    ⟨L.bad.filter fun v => r ≤ (L.hv v : ℝ), fun v => Finset.mem_filter⟩
  have hbig_sub : big ⊆ L.bad := fun v hv => ((hbig v).1 hv).1
  -- the excluded set `A`: primes `≤ √h`, prime factors of large `h_v`, and their `p_v`
  obtain ⟨A, hA⟩ : ∃ A : Finset ℕ, A = Nat.primesLE ⌊r⌋₊ ∪
      big.biUnion (fun v => (L.hv v).primeFactors ∪ {L.p v}) := ⟨_, rfl⟩
  -- bound `θ_A`
  have hθ1 : thetaSet (Nat.primesLE ⌊r⌋₊) ≤ 4 / 3 * r := by
    have := cheb.upper r hξ
    rw [Chebyshev.theta_eq_sum_primesLE] at this
    exact this
  have hterm : ∀ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v) ≤ L.deg * h := by
    intro v hv
    rw [hsum]
    exact Finset.single_le_sum (fun w _ => L.term_nonneg w) hv
  have hlogp2 : ∀ v ∈ L.bad, 1 / 2 ≤ Real.log (L.p v) := by
    intro v hv
    have h2 : (2 : ℝ) ≤ L.p v := by exact_mod_cast (L.p_prime v hv).two_le
    have := Real.log_two_gt_d9
    linarith [Real.log_le_log (by norm_num) h2]
  have hbig_term : ∀ v ∈ big, r ≤ 2 * ((L.hv v : ℝ) * L.f v * Real.log (L.p v)) := by
    intro v hv
    have hvb := ((hbig v).1 hv).1
    have hv' := ((hbig v).1 hv).2
    have hf : (1 : ℝ) ≤ L.f v := by exact_mod_cast L.one_le_f v hvb
    have hl := hlogp2 v hvb
    have hhv : (0 : ℝ) ≤ L.hv v := by positivity
    calc r ≤ L.hv v := hv'
      _ ≤ (L.hv v : ℝ) * (2 * (L.f v * Real.log (L.p v))) := by
          apply le_mul_of_one_le_right hhv; nlinarith
      _ = 2 * ((L.hv v : ℝ) * L.f v * Real.log (L.p v)) := by ring
  -- `∑_{v ∈ big} log p_v ≤ δ r`
  have hθ2 : ∑ v ∈ big, Real.log (L.p v) ≤ δ * r := by
    have : r * ∑ v ∈ big, Real.log (L.p v) ≤ L.deg * h := by
      rw [Finset.mul_sum, hsum]
      calc ∑ v ∈ big, r * Real.log (L.p v)
          ≤ ∑ v ∈ big, (L.hv v : ℝ) * L.f v * Real.log (L.p v) := by
            apply Finset.sum_le_sum
            intro v hv
            have hvb := ((hbig v).1 hv).1
            have hv' := ((hbig v).1 hv).2
            have hf : (1 : ℝ) ≤ L.f v := by exact_mod_cast L.one_le_f v hvb
            have hl := log_natCast_nonneg (L.p v)
            calc r * Real.log (L.p v) ≤ (L.hv v : ℝ) * Real.log (L.p v) :=
                  mul_le_mul_of_nonneg_right hv' hl
              _ ≤ (L.hv v : ℝ) * L.f v * Real.log (L.p v) := by
                  rw [mul_assoc]
                  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hl hf) (by positivity)
        _ ≤ ∑ v ∈ L.bad, (L.hv v : ℝ) * L.f v * Real.log (L.p v) :=
            Finset.sum_le_sum_of_subset_of_nonneg hbig_sub fun v _ _ => L.term_nonneg v
    have h2 : (L.deg : ℝ) * h ≤ δ * (r * r) := by rw [hrr]; nlinarith
    nlinarith
  -- `∑_{v ∈ big} log h_v ≤ 2 δ r log(2δh)`
  have hθ3 : ∑ v ∈ big, Real.log (L.hv v) ≤ 2 * δ * r * Real.log (2 * δ * h) := by
    have hcard : (big.card : ℝ) * r ≤ 2 * δ * h := by
      have h1 : ∑ v ∈ big, r ≤ ∑ v ∈ big, 2 * ((L.hv v : ℝ) * L.f v * Real.log (L.p v)) :=
        Finset.sum_le_sum hbig_term
      rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
      have h2 := Finset.sum_le_sum_of_subset_of_nonneg hbig_sub
        (fun v _ _ => L.term_nonneg v) (f := fun v => (L.hv v : ℝ) * L.f v * Real.log (L.p v))
      rw [← hsum] at h2
      nlinarith
    have hlog : ∀ v ∈ big, Real.log (L.hv v) ≤ Real.log (2 * δ * h) := by
      intro v hv
      have hvb := ((hbig v).1 hv).1
      have hhv : (1 : ℝ) ≤ L.hv v := by exact_mod_cast L.one_le_hv v hvb
      apply Real.log_le_log (by linarith)
      have h1 := hterm v hvb
      have hf : (1 : ℝ) ≤ L.f v := by exact_mod_cast L.one_le_f v hvb
      have hl := hlogp2 v hvb
      have hhv0 : (0 : ℝ) ≤ L.hv v := by positivity
      have h2 : (L.hv v : ℝ) ≤ 2 * ((L.hv v : ℝ) * L.f v * Real.log (L.p v)) := by
        calc (L.hv v : ℝ) ≤ (L.hv v : ℝ) * (2 * (L.f v * Real.log (L.p v))) := by
              apply le_mul_of_one_le_right hhv0; nlinarith
          _ = 2 * ((L.hv v : ℝ) * L.f v * Real.log (L.p v)) := by ring
      have h3 : (L.deg : ℝ) * h ≤ δ * h := mul_le_mul_of_nonneg_right hdeg hh0
      linarith
    calc ∑ v ∈ big, Real.log (L.hv v) ≤ ∑ v ∈ big, Real.log (2 * δ * h) :=
          Finset.sum_le_sum hlog
      _ = big.card * Real.log (2 * δ * h) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * δ * r * Real.log (2 * δ * h) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          have : (big.card : ℝ) * r ≤ 2 * δ * r * r := by rw [mul_assoc, hrr]; exact hcard
          nlinarith
  have hθA : thetaSet A ≤ 4 * δ * r * Real.log (2 * δ * h) := by
    have hB : ∑ k ∈ big.biUnion (fun v => (L.hv v).primeFactors ∪ {L.p v}), Real.log k ≤
        ∑ v ∈ big, (Real.log (L.hv v) + Real.log (L.p v)) := by
      refine (sum_biUnion_le_of_nonneg _ _ _ log_natCast_nonneg).trans ?_
      refine Finset.sum_le_sum fun v hv => ?_
      refine (sum_union_le_of_nonneg _ _ _ log_natCast_nonneg).trans ?_
      have h1 := sum_log_primeFactors_le (L.hv v)
        (by have := L.one_le_hv v (hbig_sub hv); omega)
      have h2 : ∑ k ∈ ({L.p v} : Finset ℕ), Real.log k = Real.log (L.p v) := by simp
      linarith
    rw [Finset.sum_add_distrib] at hB
    unfold thetaSet at hθ1 ⊢
    rw [hA]
    have hU := sum_union_le_of_nonneg (Nat.primesLE ⌊r⌋₊)
      (big.biUnion fun v => (L.hv v).primeFactors ∪ {L.p v}) (fun k : ℕ => Real.log k)
      log_natCast_nonneg
    have h1 : 2 * δ * r * 1 ≤ 2 * δ * r * Real.log (2 * δ * h) :=
      mul_le_mul_of_nonneg_left hlog2δh (by positivity)
    have h2 : 0 ≤ (δ - 2) * r := mul_nonneg (by linarith) hr0.le
    have : 4 / 3 * r + δ * r ≤ 2 * δ * r * Real.log (2 * δ * h) := by nlinarith
    linarith
  -- choose `ℓ`
  obtain ⟨ℓ, hℓp, hℓA, hℓle⟩ := cheb.exists_prime_notMem A
  have hℓr : r ≤ ℓ := by
    have : ℓ ∉ Nat.primesLE ⌊r⌋₊ := fun h => hℓA (hA ▸ Finset.mem_union_left _ h)
    have h' : ¬ (ℓ < ⌊r⌋₊ + 1) := fun hlt => this (by
      change ℓ ∈ Nat.primesBelow (⌊r⌋₊ + 1)
      rw [Nat.mem_primesBelow]; exact ⟨hlt, hℓp⟩)
    have : (⌊r⌋₊ : ℝ) + 1 ≤ ℓ := by exact_mod_cast not_lt.mp h'
    linarith [Nat.lt_floor_add_one r]
  refine ⟨ℓ, hℓp, hℓr, ?_, ?_, ?_⟩
  · -- (P1) upper bound
    have h1 : r ≤ r * (δ * Real.log (2 * δ * h)) :=
      le_mul_of_one_le_right hr0.le (by nlinarith)
    linarith
  · -- (P2)
    intro v hv hdvd
    have hhv := L.one_le_hv v hv
    by_cases hvb : v ∈ big
    · apply hℓA
      rw [hA]
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr ⟨v, hvb, ?_⟩
      apply Finset.mem_union_left
      exact Nat.mem_primeFactors.mpr ⟨hℓp, hdvd, by omega⟩
    · have hlt : (L.hv v : ℝ) < r := by
        by_contra hle
        exact hvb ((hbig v).2 ⟨hv, not_lt.mp hle⟩)
      have : L.hv v < ℓ := by exact_mod_cast hlt.trans_le hℓr
      exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.mpr this)
  · -- (P3)
    intro v hv hpv
    by_contra hle
    apply hℓA
    rw [hA]
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr ⟨v, (hbig v).2 ⟨hv, not_lt.mp hle⟩, ?_⟩
    apply Finset.mem_union_right
    exact Finset.mem_singleton.mpr hpv.symm

end LocalHeightData

end Iut
