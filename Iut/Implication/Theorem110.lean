/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Implication.LogVolumeBound

/-!
# IUT IV, Theorem 1.10 from the Corollary 3.12 variant (taxis #3, #1453)

**Theorem 1.10 (Log-volume estimates for Θ-pilot objects).** In the situation of
Corollary 3.12, with the arithmetic invariants of `Theorem110Invariants`,

`(1/6)·log(q) ≤ (1 + 20·d_mod/ℓ)·(log(d_{F_tpd}) + log(f_{F_tpd})) + 20·(e*_mod·ℓ + η_prm)`.

This file proves it (`Theorem110Invariants.theorem110`) from:

* the Corollary 3.12 variant `Iut.Corollary312Variant X`, i.e. `−|log(q)| ≤ −|log(Θ)|`
  — the **only** IUT I–III input;
* the local estimates of Steps (iv)–(vii) (`LocalEstimate`, Propositions 1.4, 1.5, 1.7);
* the arithmetic certificate of Steps (ii)–(iii) (`Theorem110Certificate`,
  Propositions 1.3, 1.8);
* the prime-counting bound of Proposition 1.6 (`PrimeCountingBound`).

What is proved here, following the printed proof step by step:

* Step (v)/(vii), the procession average: the capsule-wise bounds are averaged over the
  standard procession of length `ℓ* = (ℓ−1)/2` using the identities (E1), (E2)
  (`sum_affine_quadratic`), giving the "procession-normalized upper bound"
  `((ℓ+5)/4)·log(d^K_{v_ℚ}) − ((ℓ+1)/24)·log(q_{v_ℚ}) + log(s^ℚ_{v_ℚ}) +
  (ℓ+5)·l*_mod·log(s^≤_{v_ℚ})` at distinguished primes and `((ℓ+5)/4)·log π` at the
  archimedean place;
* Step (viii): the sum over `v_ℚ`, the substitution of Corollary 3.12, the estimate
  `l*_mod·log(s^≤) ≤ (4/3)·(e*_mod·ℓ + η_prm)` from Proposition 1.6
  (`lmod_mul_logSle_le`), the combination with Steps (ii)–(iii), and the final number
  tracking (`assembly`).
-/

namespace Iut

universe u v

open NumberField

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-! ### Elementary identities (E1), (E2) and real-arithmetic lemmas -/

/-- The sum of an affine-quadratic expression over `Fin L`, via (E1) and (E2):
`∑_{i<L} (a(i+2) + b(i+1)² + c) = a·L(L+3)/2 + b·L(L+1)(2L+1)/6 + c·L`. -/
lemma sum_affine_quadratic (L : ℕ) (a b c : ℝ) :
    ∑ i : Fin L, (a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) =
      a * (L * (L + 3) / 2) + b * (L * (L + 1) * (2 * L + 1) / 6) + c * L := by
  rw [Fin.sum_univ_eq_sum_range (fun i => a * ((i : ℝ) + 2) + b * ((i : ℝ) + 1) ^ 2 + c) L]
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- `log π ≤ 2` (via `π ≤ 4` and `log 2 < 0.7`). -/
lemma log_pi_le_two : Real.log Real.pi ≤ 2 := by
  have h4 : Real.log Real.pi ≤ Real.log 4 :=
    Real.log_le_log Real.pi_pos Real.pi_le_four
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_lt_d9
  linarith

lemma log_pi_nonneg : 0 ≤ Real.log Real.pi :=
  Real.log_nonneg (by linarith [Real.pi_gt_three])

/-- The final numerical bookkeeping of Step (viii), as an inequality between real numbers.
The hypotheses are: `h1`, the summed local bound after substitution of Corollary 3.12
(cleared of denominators); `h2`, `h3`, Steps (ii) and (iii); `h4`, the Proposition 1.6
bound. -/
lemma assembly {ℓ d D Q S T P DF E e lg : ℝ} (hℓ : 7 ≤ ℓ) (hd : 1 ≤ d) (_hD : 0 ≤ D)
    (_hQ : 0 ≤ Q) (_hS : 0 ≤ S) (_hT : 0 ≤ T) (_hP0 : 0 ≤ P) (hP : P ≤ 2) (hDF : 0 ≤ DF)
    (_hlg0 : 0 ≤ lg) (hlg : lg ≤ ℓ) (he : 552960 * ℓ ≤ e) (hE : e ≤ E)
    (h1 : -12 * Q ≤ 6 * ℓ * (ℓ + 5) * D - ℓ * (ℓ + 1) * Q + 24 * ℓ * S +
      24 * ℓ * (ℓ + 5) * T + 6 * ℓ * (ℓ + 5) * P)
    (h2 : D ≤ DF + 2 * lg + 21) (h3 : S ≤ 2 * d * DF + 5 + lg) (h4 : 3 * T ≤ 4 * E) :
    ℓ * Q ≤ 6 * (ℓ + 20 * d) * DF + 120 * ℓ * E := by
  have hE0 : 0 ≤ E := by linarith
  have hℓ5 : 0 ≤ ℓ + 5 := by linarith
  -- the bracket `B` of the local bounds and its estimate `B'`
  set B : ℝ := (ℓ + 5) * D + 4 * S + 4 * (ℓ + 5) * T + (ℓ + 5) * P with hB
  have step1 : (ℓ ^ 2 + ℓ - 12) * Q ≤ 6 * ℓ * B := by rw [hB]; nlinarith
  have hB' : B ≤ (ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
      16 / 3 * (ℓ + 5) * E := by
    rw [hB]
    nlinarith [mul_le_mul_of_nonneg_left h2 hℓ5, mul_le_mul_of_nonneg_left h4 hℓ5,
      mul_le_mul_of_nonneg_left hP hℓ5]
  have hpos : 0 < ℓ ^ 2 + ℓ - 12 := by nlinarith
  -- the polynomial comparison of the two sides
  have hpoly : 6 * ℓ ^ 2 * ((ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
      16 / 3 * (ℓ + 5) * E) ≤ (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d) * DF + 120 * ℓ * E) := by
    have hDFc : 6 * ℓ ^ 2 * (ℓ + 5 + 8 * d) * DF ≤ (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d)) * DF := by
      apply mul_le_mul_of_nonneg_right _ hDF
      nlinarith [mul_nonneg (sub_nonneg.2 hd) (show (0:ℝ) ≤ 12 * ℓ ^ 2 + 20 * ℓ - 240 by nlinarith),
        mul_le_mul hℓ hℓ (by norm_num) (by linarith)]
    have hrest : 6 * ℓ ^ 2 * ((2 * ℓ + 14) * lg + 23 * ℓ + 135 + 16 / 3 * (ℓ + 5) * E) ≤
        (ℓ ^ 2 + ℓ - 12) * (120 * ℓ * E) := by
      have hlg' : (2 * ℓ + 14) * lg + 23 * ℓ + 135 ≤ 63 * ℓ ^ 2 := by nlinarith
      have he' : 63 * ℓ ^ 2 ≤ ℓ * E / 8000 := by nlinarith
      have hA : 6 * ℓ ^ 2 * ((2 * ℓ + 14) * lg + 23 * ℓ + 135) ≤ 6 * ℓ ^ 2 * (ℓ * E / 8000) :=
        mul_le_mul_of_nonneg_left (hlg'.trans he') (by positivity)
      have hpoly' : 0 ≤ ℓ * E * (87 * ℓ ^ 2 - 40 * ℓ - 1440) :=
        mul_nonneg (mul_nonneg (by linarith) hE0) (by nlinarith)
      have hcube : 0 ≤ ℓ ^ 3 * E := by positivity
      nlinarith [hA, hpoly', hcube]
    nlinarith
  have step2 : (ℓ ^ 2 + ℓ - 12) * (ℓ * Q) ≤
      (ℓ ^ 2 + ℓ - 12) * (6 * (ℓ + 20 * d) * DF + 120 * ℓ * E) := by
    calc (ℓ ^ 2 + ℓ - 12) * (ℓ * Q) = ℓ * ((ℓ ^ 2 + ℓ - 12) * Q) := by ring
      _ ≤ ℓ * (6 * ℓ * B) := mul_le_mul_of_nonneg_left step1 (by linarith)
      _ = 6 * ℓ ^ 2 * B := by ring
      _ ≤ 6 * ℓ ^ 2 * ((ℓ + 5 + 8 * d) * DF + (2 * ℓ + 14) * lg + 23 * ℓ + 135 +
          16 / 3 * (ℓ + 5) * E) := mul_le_mul_of_nonneg_left hB' (by positivity)
      _ ≤ _ := hpoly
  exact le_of_mul_le_mul_left step2 hpos

namespace Theorem110Invariants

variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- `ℓ = 2·ℓ* + 1`: the prime `ℓ ≥ 5` is odd. -/
lemma two_mul_lstar_add_one : 2 * X.lstar + 1 = X.ℓ := by
  have hodd : Odd X.ℓ :=
    X.data.prime.ℓ_prime.odd_of_ne_two (by have := X.data.prime.five_le; omega)
  obtain ⟨k, hk⟩ := hodd
  simp only [Corollary312VariantData.lstar, Corollary312VariantData.ℓ] at hk ⊢
  omega

/-- The sum over the capsules of the standard procession of a function of the capsule
cardinalities. -/
lemma sum_card_standard {P : Procession ℕ} {L : ℕ} (hP : P = Procession.standard L)
    (f : ℕ → ℝ) :
    ∑ i : Fin P.length, f (P.capsule i).card = ∑ i : Fin L, f (i + 2) := by
  subst hP
  exact Finset.sum_congr rfl fun i _ => by rw [Procession.standard_capsule_card]

/-- Step (v), the sum over the capsules of the standard procession of the local bound at
a distinguished prime `p`, via (E1) and (E2). -/
lemma sum_capsuleBound (L : ℕ) (p : ℕ) :
    ∑ i : Fin L, inv.capsuleBound (i + 2) p =
      (inv.logDK p + 4 * inv.lmod * inv.ι p) * (L * (L + 3) / 2) -
        X.logQAt p / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + Real.log p * L := by
  calc ∑ i : Fin L, inv.capsuleBound (i + 2) p
      = ∑ i : Fin L, ((inv.logDK p + 4 * inv.lmod * inv.ι p) * ((i : ℝ) + 2) +
          (-(X.logQAt p / (2 * X.ℓ))) * ((i : ℝ) + 1) ^ 2 + Real.log p) :=
        Finset.sum_congr rfl fun i _ => by unfold capsuleBound; push_cast; ring
    _ = _ := by rw [sum_affine_quadratic]; ring

/-- The sum over the capsules of the archimedean bound `(j+1)·log π`, via (E1). -/
lemma sum_arch (L : ℕ) :
    ∑ i : Fin L, (((i : ℕ) + 2 : ℕ) : ℝ) * Real.log Real.pi =
      Real.log Real.pi * (L * (L + 3) / 2) := by
  have := sum_affine_quadratic L (Real.log Real.pi) 0 0
  simp only [zero_mul, add_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- Step (viii), the Proposition 1.6 input: `l*_mod·log(s^≤) ≤ (4/3)·(e*_mod·ℓ + η_prm)`.
Proved from the prime-counting certificate: `log(s^≤)` counts distinguished primes
`≤ e*_mod·ℓ`, hence is at most `π(e*_mod·ℓ)`. -/
lemma lmod_mul_logSle_le (pnt : PrimeCountingBound) :
    inv.lmod * inv.logSle ≤ 4 / 3 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) := by
  set N : ℕ := inv.eStar * X.ℓ with hN
  have hN1 : 2 ≤ N := by
    have h1 := inv.one_le_emod
    have h2 := X.data.prime.five_le
    have h3 : 1 * 5 ≤ inv.emod * X.data.ℓ := Nat.mul_le_mul h1 h2
    simp only [hN, eStar, Corollary312VariantData.ℓ]
    calc 2 ≤ 552960 * (1 * 5) := by norm_num
      _ ≤ 552960 * (inv.emod * X.data.ℓ) := Nat.mul_le_mul_left _ h3
      _ = 552960 * inv.emod * X.data.ℓ := by ring
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNcast : ((inv.eStar : ℝ) * X.ℓ) = N := by simp [hN]
  -- `log(s^≤) ≤ π(N)`
  have hcount : inv.logSle ≤ (Nat.primeCounting N : ℝ) := by
    unfold logSle ι
    rw [Finset.sum_boole]
    have hsub : (inv.dst.filter fun p => p ≤ N) ⊆ Nat.primesLE N := by
      intro p hp
      rw [Finset.mem_filter] at hp
      change p ∈ Nat.primesBelow (N + 1)
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, inv.dst_prime p hp.1⟩
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact_mod_cast Finset.card_le_card hsub
  have hlmod : inv.lmod = Real.log N := by rw [lmod, hNcast]
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hη : 0 < pnt.η := by linarith [pnt.one_lt_η]
  have hlogη : 0 < Real.log pnt.η := Real.log_pos pnt.one_lt_η
  rw [hlmod, hNcast]
  rcases le_or_gt pnt.η N with hle | hlt
  · -- `N ≥ η_prm`: apply the bound at `x = N`
    have hb := pnt.bound N hle
    rw [Nat.floor_natCast] at hb
    calc Real.log N * inv.logSle ≤ Real.log N * (Nat.primeCounting N : ℝ) :=
          mul_le_mul_of_nonneg_left hcount hlogN.le
      _ ≤ Real.log N * (4 * N / (3 * Real.log N)) :=
          mul_le_mul_of_nonneg_left hb hlogN.le
      _ = 4 / 3 * (N : ℝ) := by field_simp
      _ ≤ 4 / 3 * ((N : ℝ) + pnt.η) := by linarith
  · -- `N < η_prm`: `π(N) ≤ π(⌊η_prm⌋)` and apply the bound at `x = η_prm`
    have hb := pnt.bound pnt.η le_rfl
    have hmono : (Nat.primeCounting N : ℝ) ≤ Nat.primeCounting ⌊pnt.η⌋₊ := by
      exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hlt.le)
    have hlogle : Real.log N ≤ Real.log pnt.η := Real.log_le_log (by linarith) hlt.le
    have hcnt0 : (0 : ℝ) ≤ Nat.primeCounting ⌊pnt.η⌋₊ := by positivity
    calc Real.log N * inv.logSle ≤ Real.log N * (Nat.primeCounting N : ℝ) :=
          mul_le_mul_of_nonneg_left hcount hlogN.le
      _ ≤ Real.log pnt.η * (Nat.primeCounting ⌊pnt.η⌋₊ : ℝ) :=
          mul_le_mul hlogle hmono (by positivity) hlogη.le
      _ ≤ Real.log pnt.η * (4 * pnt.η / (3 * Real.log pnt.η)) :=
          mul_le_mul_of_nonneg_left hb hlogη.le
      _ = 4 / 3 * pnt.η := by field_simp
      _ ≤ 4 / 3 * ((N : ℝ) + pnt.η) := by linarith

/-- **IUT IV, Theorem 1.10**, derived from the Corollary 3.12 variant:

`(1/6)·log(q) ≤ (1 + 20·d_mod/ℓ)·(log(d_{F_tpd}) + log(f_{F_tpd})) + 20·(e*_mod·ℓ + η_prm)`.

The only IUT I–III input is `h312 : Corollary312Variant X`; the local estimates `est`,
the arithmetic certificate `cert`, and the prime-counting bound `pnt` are the
non-IUT inputs of the printed proof, all explicit. -/
theorem theorem110 (cert : Theorem110Certificate inv) (est : inv.LocalEstimate)
    (pnt : PrimeCountingBound) (h312 : Corollary312Variant X) :
    1 / 6 * X.qPilot.logQ ≤
      (1 + 20 * (X.dmod : ℝ) / X.ℓ) * (inv.logDtpd + inv.logFtpd) +
        20 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) := by
  -- notation
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = X.lstar := ⟨_, rfl⟩
  have hℓL : (X.ℓ : ℝ) = 2 * L + 1 := by
    have := two_mul_lstar_add_one (X := X)
    rw [hLdef, ← this]; push_cast; ring
  have hℓ7 : (7 : ℝ) ≤ X.ℓ := by exact_mod_cast cert.seven_le
  have hLpos : (0 : ℝ) < L := by linarith
  have hℓpos : (0 : ℝ) < X.ℓ := by linarith
  -- the summed local bound, evaluated on the standard procession
  have hsum := est.rhs_le
  have hproc : X.rhsData.container.proc = Procession.standard L := by
    rw [hLdef]; exact X.rhsData.proc_standard
  have hlen : (X.rhsData.container.proc.length : ℝ) = L := by
    rw [hproc, Procession.standard_length]
  have hs := sum_card_standard hproc
    (fun n => ∑ p ∈ inv.dst, inv.capsuleBound n p + n * Real.log Real.pi)
  beta_reduce at hs
  rw [hlen, hs] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_comm, sum_arch] at hsum
  simp only [sum_capsuleBound] at hsum
  -- the totals over the distinguished primes
  have hQsum : ∑ p ∈ inv.dst, X.logQAt p = X.qPilot.logQ := X.sum_logQAt cert.bad_mem_dst
  have hsum' : ∑ p ∈ inv.dst, ((inv.logDK p + 4 * inv.lmod * inv.ι p) * (L * (L + 3) / 2) -
      X.logQAt p / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + Real.log p * L) =
      (inv.logDKtot + 4 * inv.lmod * inv.logSle) * (L * (L + 3) / 2) -
        X.qPilot.logQ / (2 * X.ℓ) * (L * (L + 1) * (2 * L + 1) / 6) + inv.logSQ * L := by
    unfold logDKtot logSle logSQ
    rw [← hQsum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hsum'] at hsum
  -- Corollary 3.12: `−|log(q)| ≤ −|log(Θ)|`
  set q : ℝ := X.qPilot.logQ / (2 * X.ℓ) with hqdef
  have h312' : -q ≤ X.rhsData.rhs := h312
  have hq : X.qPilot.logQ = 2 * X.ℓ * q := by rw [hqdef]; field_simp
  have hrhs := h312'.trans hsum
  rw [le_div_iff₀ hLpos] at hrhs
  -- clear the denominators: multiply by `24ℓ` and cancel `L`
  have hmul := mul_le_mul_of_nonneg_left hrhs (by positivity : (0 : ℝ) ≤ 24 * X.ℓ)
  have hcancel : (L : ℝ) * (-(24 * X.ℓ * q)) ≤
      L * (12 * X.ℓ * (inv.logDKtot + 4 * inv.lmod * inv.logSle) * (L + 3) -
        4 * X.ℓ * q * ((L + 1) * (2 * L + 1)) + 24 * X.ℓ * inv.logSQ +
        12 * X.ℓ * Real.log Real.pi * (L + 3)) := by linarith [hmul]
  have h1L := le_of_mul_le_mul_left hcancel hLpos
  have hLℓ : (L : ℝ) = (X.ℓ - 1) / 2 := by linarith
  rw [hLℓ] at h1L
  have hq1 : X.ℓ * X.qPilot.logQ = 2 * X.ℓ ^ 2 * q := by rw [hq]; ring
  have hq2 : X.ℓ ^ 2 * X.qPilot.logQ = 2 * X.ℓ ^ 3 * q := by rw [hq]; ring
  have h1 : -12 * X.qPilot.logQ ≤ 6 * X.ℓ * (X.ℓ + 5) * inv.logDKtot -
      X.ℓ * (X.ℓ + 1) * X.qPilot.logQ + 24 * X.ℓ * inv.logSQ +
      24 * X.ℓ * (X.ℓ + 5) * (inv.lmod * inv.logSle) +
      6 * X.ℓ * (X.ℓ + 5) * Real.log Real.pi := by
    linarith [h1L, hq, hq1, hq2]
  -- the remaining inputs of the assembly
  have hD := inv.logDKtot_nonneg
  have hQ : 0 ≤ X.qPilot.logQ := hQsum ▸ Finset.sum_nonneg fun p _ => X.logQAt_nonneg p
  have hS := inv.logSQ_nonneg
  have hT : 0 ≤ inv.lmod * inv.logSle :=
    mul_nonneg (Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ inv.emod := by exact_mod_cast inv.one_le_emod
      have h2 : (5 : ℝ) ≤ X.data.ℓ := by exact_mod_cast X.data.prime.five_le
      have h3 : (1 : ℝ) * 5 ≤ inv.emod * X.data.ℓ :=
        mul_le_mul h1 h2 (by norm_num) (by linarith)
      rw [eStar_cast]; simp only [Corollary312VariantData.ℓ]; linarith)) inv.logSle_nonneg
  have hDF : 0 ≤ inv.logDtpd + inv.logFtpd := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  have hlg0 : 0 ≤ Real.log X.ℓ := Real.log_nonneg (by linarith)
  have hlg : Real.log X.ℓ ≤ X.ℓ := by linarith [Real.log_le_sub_one_of_pos hℓpos]
  have hd : (1 : ℝ) ≤ X.dmod := by exact_mod_cast X.one_le_dmod
  have he : 552960 * (X.ℓ : ℝ) ≤ (inv.eStar : ℝ) * X.ℓ := by
    have h1 : (1 : ℝ) ≤ inv.emod := by exact_mod_cast inv.one_le_emod
    have h3 : 1 * (X.ℓ : ℝ) ≤ inv.emod * X.ℓ := mul_le_mul_of_nonneg_right h1 hℓpos.le
    rw [eStar_cast]; linarith
  have hE : (inv.eStar : ℝ) * X.ℓ ≤ (inv.eStar : ℝ) * X.ℓ + pnt.η := by
    linarith [pnt.one_lt_η]
  have h4 := inv.lmod_mul_logSle_le pnt
  have key := assembly hℓ7 hd hD hQ hS hT log_pi_nonneg log_pi_le_two hDF hlg0 hlg he hE h1
    cert.step_ii cert.step_iii (by linarith)
  -- conclude
  have hfinal : (1 + 20 * (X.dmod : ℝ) / X.ℓ) * (inv.logDtpd + inv.logFtpd) +
      20 * ((inv.eStar : ℝ) * X.ℓ + pnt.η) =
      (6 * (X.ℓ + 20 * X.dmod) * (inv.logDtpd + inv.logFtpd) +
        120 * X.ℓ * ((inv.eStar : ℝ) * X.ℓ + pnt.η)) / (6 * X.ℓ) := by
    field_simp; ring
  rw [hfinal, le_div_iff₀ (by positivity)]
  linarith [key]

end Theorem110Invariants

end Iut
