/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Abc.Counting.Exponents
import Iut.Abc.Counting.Split
import Mathlib.Data.Set.Card

/-!
# An abstract framework for counting elliptic curves by discriminant

The counting theorems V6 and E1 of the LANA notes (`V6.md`, `V5V7.md`) are short reductions
from deep cited theorems. This file sets up an abstract framework in which these reductions can
be checked: a type `ι` of "curves" (in the application: `ℚ`-isomorphism classes of elliptic
curves over `ℚ`) carrying the invariants that the reductions use. The cited theorems enter as
explicit hypotheses (`Prop`s), never as global assumptions.

## Main definitions

* `Iut.Abc.Counting.CurveData ι`: the invariants `|Δ_min(E)|`, the conductor `N_E` and the
  predicate "semistable at every prime `p ∤ 6`".
* `CurveData.S k X`: the set `𝒮_k(X)` of `V6.md` §1, curves semistable off `6` with
  `|Δ_min| ≤ X` and `v_p(Δ_min) ≥ k` for every prime `p ∤ 6` dividing `Δ_min`.
* `CurveData.twistFamily n T`: the family `𝒞_n(T)` of Prop S3.2, curves semistable off `6`
  with `n ∣ v_p(Δ_min)` for every prime `p ∤ 6 T`.
* `CurveData.T k E`: the product of the primes `p ∤ 6` with `k ∤ v_p(Δ_min(E))`.

## Hypotheses (statements of cited theorems)

* `CurveData.ConductorFormula`: for `E` semistable off `6`, `N_E = 2 ^ f₂ 3 ^ f₃ rad(Δ′)` with
  `f₂ ≤ 8`, `f₃ ≤ 5` (Ogg's formula at multiplicative primes; Brumer–Kramer, Lockhart–Rosen–
  Silverman at `2, 3`).
* `CurveData.DukeKowalski`: Duke–Kowalski, Invent. Math. 139 (2000), Prop. 1: the number of
  curves of conductor `≤ Q` is `≪_ε Q ^ (1 + ε)`.
* `CurveData.UniformTwistBound n C₀ C`: Prop S3.2(n): `#𝒞_n(T) ≤ C₀ T ^ C` for every squarefree
  `T` prime to `6`.

Counts are phrased through finite sets: "`#A ≤ B`" means that every `s : Finset ι` contained
in `A` has `s.card ≤ B`. Then `ncard_le_of_forall_finset` gives finiteness and `A.ncard ≤ B`.

## Main results

* `CurveData.mem_twistFamily_of_mem_S`: `E ∈ 𝒮_k(X)` lies in `𝒞_ℓ(T_k(E))` for every `ℓ ∣ k`.
* `CurveData.cond_le`: the conductor bound `N_E ≤ 2⁸ 3⁵ rad(Δ′)`.
* `CurveData.regionI`: Region I of V6/E1: for `0 ≤ β ≤ 1`, the curves of `𝒮_k(X)` with
  `T > X ^ β` number `≪_ε X ^ ((1 - β) / k + ε)`, given the two hypotheses above.
* `card_le_of_fibres`: a set whose elements take values `1, …, N` under `f`, with fibres of size
  `≤ B`, has size `≤ N B`.
-/

namespace Iut.Abc.Counting

open Finset

/-- If every finite subset of `S` has at most `B` elements, then `S` is finite and
`S.ncard ≤ B`. -/
theorem ncard_le_of_forall_finset {ι : Type*} {S : Set ι} {B : ℝ}
    (h : ∀ s : Finset ι, (∀ E ∈ s, E ∈ S) → (s.card : ℝ) ≤ B) :
    S.Finite ∧ (S.ncard : ℝ) ≤ B := by
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊B⌋₊ + 1)
    have := h t (fun E hE => hts hE)
    rw [htc] at this
    push_cast at this
    have hB : 0 ≤ B := le_trans (by positivity) this
    linarith [Nat.lt_floor_add_one B, Nat.floor_le hB]
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card S hfin]
  exact h hfin.toFinset (fun E hE => (Set.Finite.mem_toFinset hfin).mp hE)

/-- A finite set whose elements take values in `1, …, N` under `f`, with every fibre of size
at most `B`, has at most `N B` elements. -/
theorem card_le_of_fibres {ι : Type*} {s : Finset ι} (f : ι → ℕ) (N : ℕ) {B : ℝ}
    (hf : ∀ E ∈ s, 1 ≤ f E ∧ f E ≤ N)
    (hfib : ∀ t : ℕ, 1 ≤ t → t ≤ N → (#{E ∈ s | f E = t} : ℝ) ≤ B) :
    (s.card : ℝ) ≤ N * B := by
  have hmaps : (s : Set ι).MapsTo f (Icc 1 N) := fun E hE => by
    have := hf E hE
    simp only [coe_Icc, Set.mem_Icc]
    exact this
  rw [card_eq_sum_card_fiberwise hmaps]
  push_cast
  calc ∑ t ∈ Icc 1 N, (#{E ∈ s | f E = t} : ℝ) ≤ ∑ _t ∈ Icc 1 N, B := by
        apply sum_le_sum
        intro t ht
        rw [mem_Icc] at ht
        exact hfib t ht.1 ht.2
    _ = N * B := by simp

/-- From `r ^ k · T ≤ X` and `X ^ β < T` (with `X ≥ 1`, `k ≥ 1`): `r ≤ X ^ ((1 - β) / k)`. -/
theorem le_rpow_of_pow_mul_le {r t X β : ℝ} {k : ℕ} (hk : k ≠ 0) (hr : 0 ≤ r) (hX : 1 ≤ X)
    (hrt : r ^ k * t ≤ X) (ht : X ^ β < t) : r ≤ X ^ ((1 - β) / k) := by
  have hX0 : 0 < X := by linarith
  have hXβ : 0 < X ^ β := Real.rpow_pos_of_pos hX0 β
  have ht0 : 0 < t := lt_trans hXβ ht
  have h1 : r ^ k ≤ X ^ (1 - β) := by
    rw [Real.rpow_sub hX0, Real.rpow_one, le_div_iff₀ hXβ]
    calc r ^ k * X ^ β ≤ r ^ k * t := by gcongr
      _ ≤ X := hrt
  have h2 : (r ^ k) ^ ((k : ℝ)⁻¹) ≤ (X ^ (1 - β)) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  rwa [Real.pow_rpow_inv_natCast hr hk, ← Real.rpow_mul hX0.le, ← div_eq_mul_inv] at h2

/-- Abstract curves: a type `ι` (in the application, `ℚ`-isomorphism classes of elliptic
curves over `ℚ`) with the absolute minimal discriminant, the conductor, and the predicate
"semistable at every prime `p ∤ 6`". -/
structure CurveData (ι : Type*) where
  /-- `|Δ_min(E)|`. -/
  disc : ι → ℕ
  disc_ne_zero : ∀ E, disc E ≠ 0
  /-- The conductor `N_E`. -/
  cond : ι → ℕ
  /-- `E` has good or multiplicative reduction at every prime `p ∤ 6`. -/
  Semistable : ι → Prop

namespace CurveData

variable {ι : Type*} (M : CurveData ι)

/-- `𝒮_k(X)`: semistable off `6`, `|Δ_min| ≤ X`, and `v_p(Δ_min) ≥ k` at every prime
`p ∤ 6` dividing `Δ_min`. -/
def S (k : ℕ) (X : ℝ) : Set ι :=
  {E | M.Semistable E ∧ (M.disc E : ℝ) ≤ X ∧ KFullOffSix k (M.disc E)}

/-- `𝒞_n(T)` of Prop S3.2: semistable off `6`, and `n ∣ v_p(Δ_min)` for every prime `p ∤ 6 T`. -/
def twistFamily (n T : ℕ) : Set ι :=
  {E | M.Semistable E ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ 6 * T → n ∣ (M.disc E).factorization p}

/-- `T_k(E)`: the product of the primes `p ∤ 6` with `p ∣ Δ_min(E)` and `k ∤ v_p(Δ_min(E))`. -/
def T (k : ℕ) (E : ι) : ℕ := tPart k (M.disc E)

theorem T_pos (k : ℕ) (E : ι) : 0 < M.T k E := tPart_pos _ _

theorem T_squarefree (k : ℕ) (E : ι) : Squarefree (M.T k E) := tPart_squarefree _ _

theorem T_coprime_six (k : ℕ) (E : ι) : Nat.Coprime (M.T k E) 6 := tPart_coprime_six _ _

/-- The split inequality `rad(Δ′) ^ k · T ≤ X` on `𝒮_k(X)`. -/
theorem rad6_pow_mul_T_le {k : ℕ} {X : ℝ} {E : ι} (hE : E ∈ M.S k X) :
    ((rad6 (M.disc E) : ℝ)) ^ k * M.T k E ≤ X := by
  have h := rad6_pow_mul_tPart_le (M.disc_ne_zero E) hE.2.2
  calc ((rad6 (M.disc E) : ℝ)) ^ k * M.T k E = ((rad6 (M.disc E) ^ k * M.T k E : ℕ) : ℝ) := by
        push_cast; rfl
    _ ≤ M.disc E := by exact_mod_cast h
    _ ≤ X := hE.2.1

/-- Every `E ∈ 𝒮_k(X)` lies in `𝒞_ℓ(T_k(E))` for every `ℓ ∣ k`. -/
theorem mem_twistFamily_of_mem_S {k ℓ : ℕ} {X : ℝ} {E : ι} (hE : E ∈ M.S k X) (hℓ : ℓ ∣ k) :
    E ∈ M.twistFamily ℓ (M.T k E) :=
  ⟨hE.1, fun _ _ hpT => hℓ.trans (dvd_factorization_of_not_dvd_six_mul_tPart hpT)⟩

/-- **Hypothesis** (conductor formula). For `E` semistable off `6`, the conductor is
`2 ^ f₂ 3 ^ f₃ rad(Δ′)` with `f₂ ≤ 8` and `f₃ ≤ 5`: exponent `1` at multiplicative primes
`p ∤ 6` (Ogg), and the bounds of Brumer–Kramer / Lockhart–Rosen–Silverman at `2` and `3`. -/
def ConductorFormula : Prop :=
  ∀ E, M.Semistable E → ∃ f₂ f₃ : ℕ, f₂ ≤ 8 ∧ f₃ ≤ 5 ∧
    M.cond E = 2 ^ f₂ * 3 ^ f₃ * rad6 (M.disc E)

/-- **Hypothesis** (Duke–Kowalski, Invent. Math. 139 (2000), Prop. 1): for every `ε > 0`, the
number of curves of conductor at most `Q` is `≤ c Q ^ (1 + ε)`. -/
def DukeKowalski : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 ≤ c ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ s : Finset ι,
    (∀ E ∈ s, (M.cond E : ℝ) ≤ Q) → (s.card : ℝ) ≤ c * Q ^ (1 + ε)

/-- **Hypothesis** (Prop S3.2(n) of `V6.md` §2, from DGH uniform Mordell, Schmidt's field
count and Serre's discriminant bound): `#𝒞_n(T) ≤ C₀ T ^ C` for every squarefree `T` prime
to `6`, with `C₀, C ≥ 0` depending on `n` only. -/
def UniformTwistBound (n : ℕ) (C₀ C : ℝ) : Prop :=
  0 ≤ C₀ ∧ 0 ≤ C ∧ ∀ T : ℕ, Squarefree T → Nat.Coprime T 6 → ∀ s : Finset ι,
    (∀ E ∈ s, E ∈ M.twistFamily n T) → (s.card : ℝ) ≤ C₀ * (T : ℝ) ^ C

/-- The conductor bound `N_E ≤ 2⁸ 3⁵ rad(Δ′)` for curves semistable off `6`. -/
theorem cond_le (h : M.ConductorFormula) {E : ι} (hE : M.Semistable E) :
    M.cond E ≤ 2 ^ 8 * 3 ^ 5 * rad6 (M.disc E) := by
  obtain ⟨f₂, f₃, h₂, h₃, hN⟩ := h E hE
  rw [hN]
  gcongr <;> norm_num

/-- **Region I** of Theorems V6 and E1. For `0 ≤ β ≤ 1` and `ε > 0` there is `c` with: the
curves of `𝒮_k(X)` with `T_k(E) > X ^ β` number at most `c X ^ ((1 - β) / k + ε)`. Their
conductor is `≤ 2⁸ 3⁵ X ^ ((1 - β) / k)`, and Duke–Kowalski applies. -/
theorem regionI (hcf : M.ConductorFormula) (hdk : M.DukeKowalski) {k : ℕ} (hk : 1 ≤ k)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : ℝ, 1 ≤ X → ∀ s : Finset ι,
      (∀ E ∈ s, E ∈ M.S k X ∧ X ^ β < M.T k E) →
        (s.card : ℝ) ≤ c * X ^ ((1 - β) / k + ε) := by
  obtain ⟨c, hc, hdk⟩ := hdk ε hε
  set K : ℝ := 2 ^ 8 * 3 ^ 5 with hK
  set a : ℝ := (1 - β) / k with ha
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hk0.le
  have ha1 : a ≤ 1 := by
    rw [ha, div_le_one hk0]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  refine ⟨c * K ^ (1 + ε), by positivity, fun X hX s hs => ?_⟩
  have hX0 : 0 ≤ X := by linarith
  have hXa : 1 ≤ X ^ a := Real.one_le_rpow hX ha0
  have hQ : 1 ≤ K * X ^ a := by
    rw [hK]; nlinarith
  have hcond : ∀ E ∈ s, (M.cond E : ℝ) ≤ K * X ^ a := by
    intro E hE
    obtain ⟨hS, hT⟩ := hs E hE
    have h1 : (M.cond E : ℝ) ≤ K * rad6 (M.disc E) := by
      rw [hK]; exact_mod_cast M.cond_le hcf hS.1
    have h2 : (rad6 (M.disc E) : ℝ) ≤ X ^ a :=
      le_rpow_of_pow_mul_le (by omega) (by positivity) hX (M.rad6_pow_mul_T_le hS) hT
    calc (M.cond E : ℝ) ≤ K * rad6 (M.disc E) := h1
      _ ≤ K * X ^ a := by gcongr
  calc (s.card : ℝ) ≤ c * (K * X ^ a) ^ (1 + ε) := hdk _ hQ s hcond
    _ = c * K ^ (1 + ε) * X ^ (a * (1 + ε)) := by
        rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hX0]; ring
    _ ≤ c * K ^ (1 + ε) * X ^ (a + ε) :=
        mul_le_mul_of_nonneg_left (rpow_mul_one_add_le hX ha1 hε.le) (by positivity)

end CurveData

end Iut.Abc.Counting
