/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.Statement

/-!
# Arithmetic invariants for Theorem 1.10 (taxis #1449, #1453)

The implication strand derives the ABC conjecture from the Corollary 3.12 variant
(`Iut.Corollary312Variant`) along IUT IV. The first step is IUT IV, Theorem 1.10, whose
statement involves a handful of arithmetic invariants of the initial Θ-data:

* `d_mod = [F_mod : ℚ]` (derived here from the Θ-data: `Theorem110Invariants.dmod`);
* the maximal ramification index `e_mod` of `F_mod` over `ℚ`, and the derived
  `e*_mod = 2¹²·3³·5·e_mod`;
* the normalized degrees `log(d_{F_tpd})`, `log(f_{F_tpd})` of the different and
  conductor divisors of the tripodal field `F_tpd = F_mod(E[2])`;
* the set `V_ℚ^dst` of "distinguished" rational primes (those ramifying in `K`), and the
  local contributions `log(d^K_{v_ℚ})` of the different divisor of `K` at each of them;
* the number `η_prm` of IUT IV, Proposition 1.6 (a prime-counting bound).

## Honesty boundary

Following the data-only carrier design of `Plans/Iut4Sec1Spec.md` §2.2, the invariants
that this repository cannot yet compute from the Θ-data (the tripodal field `F_tpd`,
different and conductor degrees, ramification indices, the distinguished primes) are
carried as **data** in `Theorem110Invariants`, and the arithmetic facts about them that
the proof of Theorem 1.10 consumes are carried as **explicit hypotheses** in
`Theorem110Certificate`. Every such hypothesis is a claim of ordinary algebraic number
theory (IUT IV, Propositions 1.3 and 1.8, and Steps (ii)–(iii) of the proof of
Theorem 1.10); none is the conclusion of Theorem 1.10 or of Corollary 3.12 under
another name. What *is* derived from the Θ-data is `log(q)` itself
(`QPilotData.logQ`, the left-hand side of the variant) and its decomposition by
residue characteristic (`logQAt`).

The prime-counting input (IUT IV, Proposition 1.6) is the separate certificate
`PrimeCountingBound`, exactly as in the specification's route (b): no
prime-number-theorem strength result is proved here (taxis #6).
-/

namespace Iut

universe u v

open NumberField

/-- **IUT IV, Proposition 1.6** as an explicit certificate (taxis #6): a threshold
`η_prm` beyond which the prime-counting function satisfies `π(x) ≤ 4x/(3 log x)`. This is
prime-number-theorem strength and is not proved in this repository. -/
structure PrimeCountingBound where
  /-- The threshold `η_prm`. -/
  η : ℝ
  /-- `η_prm > 1` (so that `log η_prm > 0`; the paper takes `η_prm ≥ 5`). -/
  one_lt_η : 1 < η
  /-- The bound `#{p ≤ x} ≤ 4x/(3 log x)` for all real `x ≥ η_prm`. -/
  bound : ∀ x : ℝ, η ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 4 * x / (3 * Real.log x)

variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- The **arithmetic invariants** entering the statement of IUT IV, Theorem 1.10, for a
Corollary 3.12 variant data bundle (taxis #1453). Data-only; the relations between these
numbers that the proof uses are the explicit hypotheses of `Theorem110Certificate`. -/
structure Theorem110Invariants (X : Corollary312VariantData.{u, v} AG TG) :
    Type where
  /-- The maximal ramification index `e_mod` of `F_mod` over `ℚ`. -/
  emod : ℕ
  /-- `1 ≤ e_mod`. -/
  one_le_emod : 1 ≤ emod
  /-- `e_mod ≤ d_mod = [F_mod : ℚ]`. -/
  emod_le_dmod : emod ≤ Module.finrank ℚ ↥(fieldOfModuli X.data.F X.data.E)
  /-- `log(d_{F_tpd})`: the normalized degree of the different divisor of the tripodal
  field `F_tpd = F_mod(E[2])` over `ℚ`. -/
  logDtpd : ℝ
  /-- `log(d_{F_tpd}) ≥ 0` (the different divisor is effective). -/
  logDtpd_nonneg : 0 ≤ logDtpd
  /-- `log(f_{F_tpd})`: the normalized degree of the conductor divisor of `F_tpd`
  (support of the `q`-divisor, all coefficients `1`). -/
  logFtpd : ℝ
  /-- `log(f_{F_tpd}) ≥ 0`. -/
  logFtpd_nonneg : 0 ≤ logFtpd
  /-- The finite set `V_ℚ^dst` of distinguished rational primes: those that ramify in
  the `ℓ`-torsion field `K` (conditions (D4)–(D7) of the proof of Theorem 1.10). -/
  dst : Finset ℕ
  /-- The distinguished rational places are primes. -/
  dst_prime : ∀ p ∈ dst, p.Prime
  /-- `log(d^K_{v_ℚ})`: the contribution of the rational prime `v_ℚ` to the normalized
  degree of the different divisor of `K`. -/
  logDK : ℕ → ℝ
  /-- Each contribution is nonnegative. -/
  logDK_nonneg : ∀ p, 0 ≤ logDK p
  /-- The different of `K` is supported on the distinguished primes ((D2)/(D6)). -/
  logDK_eq_zero : ∀ p, p ∉ dst → logDK p = 0

namespace Corollary312VariantData

variable (X : Corollary312VariantData.{u, v} AG TG)

/-- The prime `ℓ` of the Θ-data. -/
abbrev ℓ : ℕ := X.data.ℓ

/-- `ℓ* = (ℓ − 1)/2`, the length of the standard procession. -/
abbrev lstar : ℕ := (X.data.ℓ - 1) / 2

/-- `d_mod = [F_mod : ℚ]`, derived from the Θ-data. -/
noncomputable abbrev dmod : ℕ := Module.finrank ℚ ↥(fieldOfModuli X.data.F X.data.E)

/-- `log(q_{v_ℚ})`: the contribution of the places of residue characteristic `p` to
`log(q)` (`QPilotData.logQ`). Derived from the Θ-data, not data. -/
noncomputable def logQAt (p : ℕ) : ℝ :=
  ∑ w ∈ X.qPilot.badFinset.attach.filter (fun w => residueChar w.1 = p),
    X.qPilot.weight w.1 * (X.data.prime.qOrder w.1 (X.qPilot.mem_bad w.2) : ℝ) *
      Real.log (residueChar w.1)

lemma one_le_dmod : 1 ≤ X.dmod :=
  Module.finrank_pos

lemma logQAt_nonneg (p : ℕ) : 0 ≤ X.logQAt p := by
  refine Finset.sum_nonneg fun w hw => ?_
  refine mul_nonneg (mul_nonneg (X.qPilot.weight_pos w.1 w.2).le (by positivity)) ?_
  rcases Nat.eq_zero_or_pos (residueChar w.1) with h | h
  · simp [h]
  · exact Real.log_nonneg (by exact_mod_cast h)

/-- `log(q)` is the sum of its residue-characteristic components over any finite set of
primes containing the residue characteristics of the bad places. -/
lemma sum_logQAt {s : Finset ℕ} (hbad : ∀ w ∈ X.qPilot.badFinset, residueChar w ∈ s) :
    ∑ p ∈ s, X.logQAt p = X.qPilot.logQ := by
  unfold logQAt QPilotData.logQ
  exact Finset.sum_fiberwise_of_maps_to (fun w _ => hbad w.1 w.2) _

end Corollary312VariantData

namespace Theorem110Invariants

variable {X : Corollary312VariantData.{u, v} AG TG} (inv : Theorem110Invariants X)

/-- `e*_mod = 2¹²·3³·5·e_mod = 552960·e_mod`. -/
abbrev eStar : ℕ := 552960 * inv.emod

lemma eStar_cast : (inv.eStar : ℝ) = 552960 * inv.emod := by
  simp only [eStar]; push_cast; ring

/-- `l*_mod = log(e*_mod · ℓ)`. -/
noncomputable def lmod : ℝ := Real.log ((inv.eStar : ℝ) * X.ℓ)

/-- The indicator `ι_{v_ℚ}`: `1` if `p ≤ e*_mod · ℓ`, `0` otherwise. -/
noncomputable def ι (p : ℕ) : ℝ := if p ≤ inv.eStar * X.ℓ then 1 else 0

/-- `log(s^ℚ) = ∑_{p ∈ V_ℚ^dst} log p`, the degree of the arithmetic divisor
`s^ℚ_ADiv` of Step (iii). -/
noncomputable def logSQ : ℝ := ∑ p ∈ inv.dst, Real.log p

/-- `log(s^≤) = #{p ∈ V_ℚ^dst | p ≤ e*_mod · ℓ}`, the degree of the arithmetic divisor
`s^≤_ADiv` of Step (iii). -/
noncomputable def logSle : ℝ := ∑ p ∈ inv.dst, inv.ι p

/-- The total `log(d^K) = ∑_{v_ℚ} log(d^K_{v_ℚ})`. -/
noncomputable def logDKtot : ℝ := ∑ p ∈ inv.dst, inv.logDK p

lemma ι_nonneg (p : ℕ) : 0 ≤ inv.ι p := by
  unfold ι; split_ifs <;> norm_num

lemma ι_le_one (p : ℕ) : inv.ι p ≤ 1 := by
  unfold ι; split_ifs <;> norm_num

lemma logSle_nonneg : 0 ≤ inv.logSle :=
  Finset.sum_nonneg fun p _ => inv.ι_nonneg p

lemma logSQ_nonneg : 0 ≤ inv.logSQ :=
  Finset.sum_nonneg fun p hp => Real.log_nonneg (by exact_mod_cast (inv.dst_prime p hp).one_lt.le)

lemma logDKtot_nonneg : 0 ≤ inv.logDKtot :=
  Finset.sum_nonneg fun p _ => inv.logDK_nonneg p

end Theorem110Invariants

/-- **The arithmetic certificate for Theorem 1.10**: the facts of algebraic number theory
that the proof of IUT IV, Theorem 1.10 consumes about the invariants of
`Theorem110Invariants`, as explicit hypotheses. Sources, field by field:

* `seven_le`: `ℓ ≠ 5` (IUT I, Definition 3.1(c), together with the rationality of the
  `3·5`-torsion assumed in Theorem 1.10), hence `ℓ ≥ 7` for the prime `ℓ ≥ 5`;
* `bad_mem_dst`: the residue characteristics of the bad places are distinguished
  ((D2)/(D6): `Supp(q_ADiv) ⊆ V^dst`);
* `step_ii`: the final display of Step (ii): `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd})
  + 2·log ℓ + 21`, from Proposition 1.3(i),(ii), (E3)–(E6) and the Galois-group
  inclusions `Gal(F/F_tpd) ↪ GL₂(𝔽₃) × GL₂(𝔽₅) × ℤ/2`, `Gal(K/F) ↪ GL₂(𝔽_ℓ)`;
* `step_iii`: the estimate `log(s^ℚ) ≤ 2·d_mod·(log(d_{F_tpd}) + log(f_{F_tpd})) + 5 +
  log ℓ` of Step (iii), from Proposition 1.3(i) and (D1)–(D7).

None of these is an IUT I–III input; all are consequences of Propositions 1.3 and 1.8
(the latter through the reduction certificate of taxis #5). -/
structure Theorem110Certificate {X : Corollary312VariantData.{u, v} AG TG}
    (inv : Theorem110Invariants X) : Prop where
  /-- `ℓ ≥ 7`. -/
  seven_le : 7 ≤ X.ℓ
  /-- The residue characteristic of every bad place is a distinguished prime. -/
  bad_mem_dst : ∀ w ∈ X.qPilot.badFinset, residueChar w ∈ inv.dst
  /-- Step (ii): `log(d_K) ≤ log(d_{F_tpd}) + log(f_{F_tpd}) + 2·log ℓ + 21`. -/
  step_ii : inv.logDKtot ≤ inv.logDtpd + inv.logFtpd + 2 * Real.log X.ℓ + 21
  /-- Step (iii): `log(s^ℚ) ≤ 2·d_mod·(log(d_{F_tpd}) + log(f_{F_tpd})) + 5 + log ℓ`. -/
  step_iii : inv.logSQ ≤ 2 * X.dmod * (inv.logDtpd + inv.logFtpd) + 5 + Real.log X.ℓ

end Iut
