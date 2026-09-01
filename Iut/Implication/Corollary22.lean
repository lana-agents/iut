/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Implication.Theorem110
import Iut.Implication.PrimeSelection
import Iut.Abc.Target

/-!
# IUT IV, Corollary 2.2 (taxis #1454)

**Corollary 2.2 (Construction of suitable initial Θ-data).** For a compactly bounded
subset `K_V` of the λ-line `ℙ¹ ∖ {0,1,∞}` and a degree bound `d`, every elliptic curve
`E_F` corresponding to a point `x ∈ K_V ∩ U_X(ℚ̄)^{≤d}` of large enough height carries
initial Θ-data whose prime `ℓ` satisfies (C1) and whose invariants satisfy

`(C2)  (1/6)·log(q) ≤ (1 + ε_E)·(log-diff_X(x) + log-cond_D(x)) + C_K`,

with `ε_E = (60δ)²·h^{−1/2}·log(2δh)`, `δ = 2¹²·3³·5·d`, `h = log(q_∀(x))`; and (iii)
`ε_E ≤ ε` outside a finite set.

## Structure of the formalization

The proof mixes three kinds of input, which are separated here:

1. **Standard height theory** (`Corollary22Inputs`): the function `log(q_∀)`, the local
   height data of each curve, Corollary 2.2(i) (`(1/6)·log(q_∀) ≈ ht_{ω_X(D)}` on `K_V`),
   Northcott finiteness, the bound at the prime `2` coming from `(∗j-inv)`, and the two
   [GenEll] inputs of the proof: Lemma 3.5 (an `ℓ`-cyclic subgroup scheme forces a bound
   on the height) and Lemma 3.1(iii) (the mod-`ℓ` image contains `SL₂`). These are
   delegated to `LANA-Project/genl` (taxis #1452) and `lana-agents/orbicurve-cores`
   (taxis #10, the four exceptional `j`-invariants of [CanLift], Proposition 2.7).
2. **The prime number theorem** (`ChebyshevBound`, `PrimeCountingBound`; taxis #6).
3. **The existence of the anabelian part of the Θ-data** (`ThetaDataExistence`, (P7)):
   given a curve and a prime `ℓ` satisfying (P1)–(P6), initial Θ-data in the situation
   of Theorem 1.10 with the expected invariants. This is the one input of IUT-theoretic
   nature (IUT I, Definition 3.1(d)–(f); *The Étale Theta Function*, §2); it cannot be
   discharged before the anabelian interfaces have constructions (taxis #276, #279) and
   is tracked as an open obligation of this repository.

Everything else — the choice of `ℓ` (`LocalHeightData.exists_prime_selection`), the
arguments for (P4) and (P5) at large height, the application of Theorem 1.10 and the
derivation of (C2), and assertion (iii) — is proved here.
-/

namespace Iut

universe u v

open Finset Real

/-! ### Real-analysis helpers -/

/-- `log h ≤ 4·√√h` for `h ≥ 1`. -/
lemma log_le_four_mul_sqrt_sqrt {h : ℝ} (hh : 1 ≤ h) :
    Real.log h ≤ 4 * Real.sqrt (Real.sqrt h) := by
  set s := Real.sqrt (Real.sqrt h) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = Real.sqrt h := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs4 : s * s * (s * s) = h := by rw [hs2]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  have hlog : Real.log h = 4 * Real.log s := by
    rw [← hs4, show s * s * (s * s) = s ^ 4 by ring, Real.log_pow]; push_cast; ring
  rw [hlog]
  have := Real.log_le_sub_one_of_pos (by linarith : 0 < s)
  linarith

/-- `log y ≤ y` for `y > 0`. -/
lemma log_le_self_of_pos {y : ℝ} (hy : 0 < y) : Real.log y ≤ y := by
  linarith [Real.log_le_sub_one_of_pos hy]

/-- `log y ≤ y/2` for `y > 0`. -/
lemma log_le_half_of_pos {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  set s := Real.sqrt y with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr hy
  have hss : s * s = y := Real.mul_self_sqrt hy.le
  have h1 : Real.log y = 2 * Real.log s := by
    rw [← hss, Real.log_mul hs0.ne' hs0.ne']; ring
  have h2 := Real.log_le_sub_one_of_pos hs0
  have h3 : s ≤ y / 4 + 1 := by nlinarith [sq_nonneg (s - 2)]
  linarith

/-- `log(20·δ²·h²) ≤ 6·log(2·δ·h)` for `δ, h ≥ 1`. -/
lemma log_bound_ell {δ h : ℝ} (hδ : 1 ≤ δ) (hh : 1 ≤ h) :
    Real.log (20 * δ ^ 2 * h ^ 2) ≤ 6 * Real.log (2 * δ * h) := by
  have h1 : Real.log (20 * δ ^ 2 * h ^ 2) = Real.log 20 + 2 * Real.log δ + 2 * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]; push_cast; ring
  have h2 : Real.log (2 * δ * h) = Real.log 2 + Real.log δ + Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have h20 : Real.log 20 ≤ 6 * Real.log 2 := by
    have : Real.log 20 ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
    have h64 : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hδ0 : 0 ≤ Real.log δ := Real.log_nonneg hδ
  have hh0 : 0 ≤ Real.log h := Real.log_nonneg hh
  linarith

/-- The tolerance `ε_E = (60δ)²·log(2δh)/√h` of Corollary 2.2(ii). -/
noncomputable def epsilonE (δ h : ℝ) : ℝ :=
  (60 * δ) ^ 2 * Real.log (2 * δ * h) / Real.sqrt h

/-- `ε_E` is small for large `h`: `ε_E ≤ ε` as soon as `h ≥ ((60δ)²(2δ+4)/ε)⁴`. -/
lemma epsilonE_le {δ h ε : ℝ} (hδ : 1 ≤ δ) (hε : 0 < ε)
    (hh : ((60 * δ) ^ 2 * (2 * δ + 4) / ε) ^ 4 ≤ h) (hh1 : 1 ≤ h) :
    epsilonE δ h ≤ ε := by
  set s := Real.sqrt (Real.sqrt h) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = Real.sqrt h := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hs4 : s * s * (s * s) = h := by rw [hs2]; exact Real.mul_self_sqrt (by linarith)
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  set M := (60 * δ) ^ 2 * (2 * δ + 4) / ε with hM
  have hM0 : 0 ≤ M := by positivity
  have hsM : M ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < M ^ 4 := by
      apply pow_lt_pow_left₀ hlt hs0 (by norm_num)
    have : s ^ 4 = h := by rw [← hs4]; ring
    linarith
  -- `log(2δh) ≤ 2δ + 4s`
  have hlog : Real.log (2 * δ * h) ≤ 2 * δ + 4 * s := by
    rw [Real.log_mul (by positivity) (by linarith)]
    have h1 := log_le_self_of_pos (by positivity : (0 : ℝ) < 2 * δ)
    have h2 := log_le_four_mul_sqrt_sqrt hh1
    linarith
  have hlog0 : 0 ≤ Real.log (2 * δ * h) := Real.log_nonneg (by nlinarith)
  unfold epsilonE
  rw [← hs2, div_le_iff₀ (by positivity)]
  -- `(60δ)²·log ≤ (60δ)²(2δ + 4s) ≤ (60δ)²(2δ+4)·s = ε·M·s ≤ ε·s·s`
  have h1 : (60 * δ) ^ 2 * Real.log (2 * δ * h) ≤ (60 * δ) ^ 2 * (2 * δ + 4 * s) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2 : (60 * δ) ^ 2 * (2 * δ + 4 * s) ≤ (60 * δ) ^ 2 * (2 * δ + 4) * s := by
    have : 2 * δ + 4 * s ≤ (2 * δ + 4) * s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ (60 * δ) ^ 2)]
  have h3 : (60 * δ) ^ 2 * (2 * δ + 4) = ε * M := by rw [hM]; field_simp
  have h4 : ε * M * s ≤ ε * (s * s) := by
    have := mul_le_mul_of_nonneg_left hsM (mul_nonneg hε.le hs0)
    calc ε * M * s = ε * s * M := by ring
      _ ≤ ε * s * s := this
      _ = ε * (s * s) := by ring
  calc (60 * δ) ^ 2 * Real.log (2 * δ * h) ≤ (60 * δ) ^ 2 * (2 * δ + 4) * s := h1.trans h2
    _ = ε * M * s := by rw [h3]
    _ ≤ ε * (s * s) := h4

/-- The bound on `log ℓ` from (P1): `log ℓ ≤ 3 + 2δ + 8·√√h` when `ℓ ≤ 20δ²h²`. -/
lemma log_ell_bound {δ h ℓ s : ℝ} (hδ : 1 ≤ δ) (hh1 : 1 ≤ h) (hℓ : 1 ≤ ℓ)
    (hℓup : ℓ ≤ 20 * δ ^ 2 * h ^ 2) (hlogh : Real.log h ≤ 4 * s) :
    Real.log ℓ ≤ 3 + 2 * δ + 8 * s := by
  have h1 : Real.log ℓ ≤ Real.log (20 * δ ^ 2 * h ^ 2) := Real.log_le_log (by linarith) hℓup
  have h2 : Real.log (20 * δ ^ 2 * h ^ 2) = Real.log 20 + 2 * Real.log δ + 2 * Real.log h := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow]
    push_cast; ring
  have h3 : Real.log 20 ≤ 3 := by
    have : Real.log 20 ≤ Real.log (Real.exp 3) :=
      Real.log_le_log (by norm_num) (by
        have := Real.exp_one_gt_d9
        have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
        have h4 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
          pow_le_pow_left₀ (by norm_num) this.le 3
        rw [h3]; norm_num at h4 ⊢; linarith)
    rwa [Real.log_exp] at this
  have h4 : Real.log δ ≤ δ := log_le_self_of_pos (by linarith)
  linarith

/-- The (P5) argument: if `h ≤ B + √h·log ℓ` with `log ℓ ≤ 3 + 2δ + 8·√√h`, then
`h ≤ (B + 11 + 2δ)⁴`. -/
lemma p5_height_bound {B δ h r s lg : ℝ} (hB : 0 ≤ B) (hδ : 1 ≤ δ) (_hr0 : 0 ≤ r)
    (hrr : r * r = h) (hs0 : 0 ≤ s) (hss : s * s = r) (hh1 : 1 ≤ h)
    (hlg : lg ≤ 3 + 2 * δ + 8 * s) (hmain : h ≤ B + r * lg) :
    h ≤ (B + 11 + 2 * δ) ^ 4 := by
  have hs4 : s * s * (s * s) = h := by rw [hss]; exact hrr
  have hs1 : 1 ≤ s := by
    by_contra hlt
    push Not at hlt
    have : s ^ 4 < 1 := pow_lt_one₀ hs0 hlt (by norm_num)
    nlinarith [show s ^ 4 = s * s * (s * s) by ring]
  have hrs : r * lg ≤ (3 + 2 * δ) * (s * s) + 8 * (s * s * s) := by
    rw [← hss]; nlinarith [mul_le_mul_of_nonneg_left hlg (by positivity : (0:ℝ) ≤ s * s)]
  have hs3 : s * s * (s * s) ≤ B + (11 + 2 * δ) * (s * s * s) := by
    have : (3 + 2 * δ) * (s * s) ≤ (3 + 2 * δ) * (s * s * s) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith
    nlinarith
  have hsle : s ≤ B + 11 + 2 * δ := by
    have hs3' : 0 < s * s * s := by positivity
    have : (s * s * s) * s ≤ (s * s * s) * (B + 11 + 2 * δ) := by
      have : B ≤ B * (s * s * s) := le_mul_of_one_le_right hB (by nlinarith)
      nlinarith
    exact le_of_mul_le_mul_left this hs3'
  rw [← hs4]
  calc s * s * (s * s) = s ^ 4 := by ring
    _ ≤ (B + 11 + 2 * δ) ^ 4 := pow_le_pow_left₀ hs0 hsle 4

/-- The final arithmetic of Corollary 2.2(ii): from Theorem 1.10 (`h110`), the comparison
of `log(q_∀)` with `log(q)` (`hlogQ`), and the bounds (P1) on `ℓ`, derive (C2) with
`ε_E = (60δ)²·log(2δh)/√h ≤ 1` and `C_K = 40η + B/3`. -/
lemma c2_final {h r lg δ ℓ dm e D F LD LC Q B η ε : ℝ}
    (hr0 : 0 < r) (hrr : r * r = h) (hlg1 : 1 ≤ lg) (hδ1 : 1 ≤ δ)
    (hℓlo : r ≤ ℓ) (hℓhi : ℓ ≤ 10 * δ * r * lg)
    (hdm : 20 * dm ≤ δ) (he : e ≤ δ) (hDF0 : 0 ≤ D + F) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (h110 : 1 / 6 * Q ≤ (1 + 20 * dm / ℓ) * (D + F) + 20 * (e * ℓ + η))
    (hlogQ : h ≤ Q + B + 6 * (r * lg))
    (hD : LD = D) (hF : F ≤ LC)
    (hε : ε = (60 * δ) ^ 2 * lg / r) (hε1 : ε ≤ 1) :
    1 / 6 * h ≤ (1 + ε) * (LD + LC) + (40 * η + B / 3) := by
  have hℓpos : 0 < ℓ := by linarith
  have hlg0 : 0 ≤ lg := by linarith
  have hrlg : 0 ≤ r * lg := by positivity
  have hεr : ε * r = (60 * δ) ^ 2 * lg := by rw [hε, div_mul_cancel₀ _ hr0.ne']
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  -- `20·dm/ℓ ≤ δ/r`
  have hcoef : 20 * dm / ℓ ≤ δ / r := by
    rw [div_le_div_iff₀ hℓpos hr0]
    nlinarith [mul_le_mul_of_nonneg_right hdm hr0.le,
      mul_le_mul_of_nonneg_left hℓlo (by linarith : 0 ≤ δ)]
  -- Theorem 1.10 in the form `(1/6)Q ≤ (1 + δ/r)(D+F) + 200δ²·r·lg + 20η`
  have h110' : 1 / 6 * Q ≤ (1 + δ / r) * (D + F) + 200 * δ ^ 2 * (r * lg) + 20 * η := by
    have h1 : (1 + 20 * dm / ℓ) * (D + F) ≤ (1 + δ / r) * (D + F) :=
      mul_le_mul_of_nonneg_right (by linarith) hDF0
    have h2 : e * ℓ ≤ δ * (10 * δ * r * lg) := mul_le_mul he hℓhi hℓpos.le (by linarith)
    nlinarith
  -- `δ/r ≤ ε/5` and `(200δ² + 1)·r·lg ≤ (2/5)·ε·(h/6)`
  have hδr : δ / r ≤ ε / 5 := by
    rw [div_le_iff₀ hr0]
    have : ε / 5 * r = (60 * δ) ^ 2 * lg / 5 := by rw [← hεr]; ring
    rw [this]
    nlinarith
  have hbig : (200 * δ ^ 2 + 1) * (r * lg) ≤ 2 / 5 * ε * (h / 6) := by
    have : 2 / 5 * ε * (h / 6) = (2 / 5) * (ε * r) * r / 6 := by rw [← hrr]; ring
    rw [this, hεr]
    nlinarith
  -- `(1 − 2ε/5)(h/6) ≤ (1 + ε/5)(D+F) + (20η + B/6)`
  have hstep : (1 - 2 / 5 * ε) * (h / 6) ≤ (1 + ε / 5) * (D + F) + (20 * η + B / 6) := by
    have h1 : (1 + δ / r) * (D + F) ≤ (1 + ε / 5) * (D + F) :=
      mul_le_mul_of_nonneg_right (by linarith) hDF0
    nlinarith
  -- `(1+ε/5)/(1−2ε/5) ≤ 1 + ε` and `1/(1−2ε/5) ≤ 2` for `0 ≤ ε ≤ 1`
  have hden : 3 / 5 ≤ 1 - 2 / 5 * ε := by linarith
  have hεε : ε * ε ≤ ε := mul_le_of_le_one_left hε0 hε1
  have hfrac : (1 + ε / 5) * (D + F) ≤ (1 - 2 / 5 * ε) * ((1 + ε) * (D + F)) := by
    have h1 : (1 + ε / 5) ≤ (1 - 2 / 5 * ε) * (1 + ε) := by linarith
    have := mul_le_mul_of_nonneg_right h1 hDF0
    linarith
  have hconst : 20 * η + B / 6 ≤ (1 - 2 / 5 * ε) * (40 * η + B / 3) := by
    have h1 : ε * η ≤ η := mul_le_of_le_one_left hη hε1
    have h2 : ε * B ≤ B := mul_le_of_le_one_left hB hε1
    linarith
  have hall : (1 - 2 / 5 * ε) * (h / 6) ≤
      (1 - 2 / 5 * ε) * ((1 + ε) * (D + F) + (40 * η + B / 3)) := by linarith
  have hfin := le_of_mul_le_mul_left hall (by linarith)
  have hmono : (1 + ε) * (D + F) ≤ (1 + ε) * (LD + LC) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  linarith

/-! ### The inputs -/

/-- `δ = 2¹²·3³·5·d = 552960·d`, the bound on `[F : ℚ]` for the Θ-data field of a point of degree
`≤ d` ((E3)–(E5) in the proof of Theorem 1.10). -/
noncomputable def deltaBound (d : ℕ) : ℝ := 552960 * (d : ℝ)

variable (T : Genl.HeightTheory)

/-- **The standard height-theoretic inputs of Corollary 2.2** for a compactly bounded
subset `K` of the tripod and a degree bound `d`: the function `log(q_∀)`, the local height
data of each curve over its Θ-data field `F` (with `[F : ℚ] ≤ δ`), Corollary 2.2(i),
Northcott finiteness, the bound of the contribution of the prime `2`, [GenEll] Lemma 3.5
and Lemma 3.1(iii), and the four exceptional `j`-invariants of [CanLift], Proposition 2.7.
All are standard arithmetic geometry or absolute anabelian geometry, delegated to the
sibling projects (taxis #1452, #10). -/
structure Corollary22Inputs (K : T.CBS) (d : ℕ) where
  /-- The height `h = log(q_∀(−))`: the normalized degree of the `q`-divisor at all
  nonarchimedean primes. -/
  h : T.Pt T.tripod → ℝ
  /-- The local height data of the elliptic curve of `x` over its Θ-data field `F`. -/
  localData : ∀ x : T.Pt T.tripod, x ∈ T.cbsSet K ∩ T.ptLE T.tripod d → LocalHeightData
  /-- The local height data computes `h`. -/
  localData_height : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).height = h x
  /-- `[F : ℚ] ≤ δ = 2¹²·3³·5·d` ((E3)–(E5) in the proof of Theorem 1.10). -/
  localData_deg_le : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).deg ≤ 552960 * d
  /-- **Corollary 2.2(i)**: `(1/6)·log(q_∀) ≈ ht_{ω_X(D)}` on `K_V` ([GenEll],
  Proposition 1.4(i),(iii), Lemma 3.7, and `(∗j-inv)`). -/
  htCan_equiv : ((1 / 6 : ℝ) • h) ≈[T.cbsSet K] T.htCan T.tripod
  /-- **Northcott finiteness** ([GenEll], Proposition 1.4(iv) with (i)): finitely many
  points of `K_V ∩ U_X(ℚ̄)^{≤d}` of bounded height. -/
  northcott : ∀ H : ℝ, {x | x ∈ T.cbsSet K ∩ T.ptLE T.tripod d ∧ h x ≤ H}.Finite
  /-- The bound `B_K` on the contribution of the prime `2` to `log(q_∀)`, from
  `(∗j-inv)`. -/
  B : ℝ
  /-- `B_K ≥ 0`. -/
  B_nonneg : 0 ≤ B
  /-- The contribution of the places over `2` is bounded on `K_V`. -/
  heightEq_two_le : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    (localData x hx).heightEq 2 ≤ B
  /-- `E_x` has an `ℓ`-cyclic subgroup scheme (in the terminology of [GenEll],
  Lemma 3.5). -/
  HasCyclicSubgroup : T.Pt T.tripod → ℕ → Prop
  /-- The number `T_K` of [GenEll], Lemma 3.5 (with `ε = 1`). -/
  TK : ℝ
  /-- **[GenEll], Lemma 3.5 with Proposition 3.4**: an `ℓ`-cyclic subgroup scheme forces
  `((ℓ−2)/24)·log(q_∀) ≤ 2·log ℓ + T_K`. -/
  cyclic_bound : ∀ (x : T.Pt T.tripod) (_hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → HasCyclicSubgroup x ℓ →
    ((ℓ : ℝ) - 2) / 24 * h x ≤ 2 * Real.log ℓ + TK
  /-- The image of `Gal(ℚ̄/F) → GL₂(𝔽_ℓ)` on the `ℓ`-torsion of `E_x` contains
  `SL₂(𝔽_ℓ)`. -/
  SL2Image : T.Pt T.tripod → ℕ → Prop
  /-- **[GenEll], Lemma 3.1(iii)**: (P2), (P4) and (P5) imply (P6). -/
  sl2_of : ∀ (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d),
    ∀ ℓ : ℕ, ℓ.Prime → 5 ≤ ℓ →
    (∀ v ∈ (localData x hx).bad, ¬ ℓ ∣ (localData x hx).hv v) →
    ¬ HasCyclicSubgroup x ℓ →
    (∃ v ∈ (localData x hx).bad, (localData x hx).p v ≠ 2 ∧ (localData x hx).p v ≠ ℓ) →
    SL2Image x ℓ
  /-- The points whose once-punctured elliptic curve fails to have an `F`-core
  ([CanLift], Proposition 2.7: four `j`-invariants; taxis #10). -/
  excCore : Set (T.Pt T.tripod)
  /-- Finitely many such points of bounded degree. -/
  excCore_finite : (excCore ∩ (T.cbsSet K ∩ T.ptLE T.tripod d)).Finite

variable {T}
variable {AG : AnabelianGeometry.{u}} {TG : TemperedGeometry AG}

/-- **Existence of suitable initial Θ-data** ((P7) in the proof of Corollary 2.2): for a
point `x` outside the exceptional set and a prime `ℓ ≥ 7` satisfying (P2), (P3), (P5),
(P6), there are initial Θ-data with prime `ℓ` in the situation of Theorem 1.10 — i.e.
a Corollary 3.12 variant data bundle with its Theorem 1.10 invariants, certificate and
local estimates — whose `log(q)` is the part of `log(q_∀)` away from `2` and `ℓ`, with
`d_mod ≤ d`, and whose different and conductor invariants match `log-diff_X(x)` and
`log-cond_D(x)` (the equality and the two inequalities recorded at the end of the proof of
Corollary 2.2). The predicate `P` restricts the data bundles produced (e.g. to the concrete
ones of `Iut.concreteVariantData`); the Corollary 3.12 variant is only assumed on them.

This is the IUT-theoretic input of Corollary 2.2 (IUT I, Definition 3.1(d)–(f); *The
Étale Theta Function*, Definitions 2.1–2.5): the construction of `C̲_K`, `V`, `ε` from
the `SL₂` image. It is an open obligation of this repository, blocked on the anabelian
interfaces (taxis #276, #279). -/
structure ThetaDataExistence (P : Corollary312VariantData.{u, v} AG TG → Prop)
    {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d) : Prop where
  thetaData : ∀ x (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d), x ∉ I.excCore →
    ∀ ℓ : ℕ, ℓ.Prime → 7 ≤ ℓ →
    (∀ v ∈ (I.localData x hx).bad, ¬ ℓ ∣ (I.localData x hx).hv v) →
    (∀ v ∈ (I.localData x hx).bad, (I.localData x hx).p v = ℓ →
      ((I.localData x hx).hv v : ℝ) < Real.sqrt (I.h x)) →
    (∃ v ∈ (I.localData x hx).bad, (I.localData x hx).p v ≠ 2 ∧ (I.localData x hx).p v ≠ ℓ) →
    I.SL2Image x ℓ →
    ∃ (X : Corollary312VariantData.{u, v} AG TG) (inv : Theorem110Invariants X), P X ∧
      Theorem110Certificate inv ∧ Nonempty inv.LocalEstimate ∧ X.ℓ = ℓ ∧ X.dmod ≤ d ∧
      X.qPilot.logQ = (I.localData x hx).heightOther 2 ℓ ∧
      T.logDiff T.tripod x = inv.logDtpd ∧
      inv.logFtpd ≤ T.logCond T.tripod x ∧
      T.logCond T.tripod x ≤ inv.logFtpd + Real.log (2 * ℓ)

namespace Corollary22Inputs

variable {K : T.CBS} {d : ℕ} (I : Corollary22Inputs T K d)

/-- The threshold above which (P4), (P5), `√h ≥ ξ_prm` and `ε_E ≤ 1` all hold. -/
noncomputable def threshold (cheb : ChebyshevBound) : ℝ :=
  max (max (cheb.ξ ^ 2) (49 + 8 * max I.TK 0))
    (max ((I.B + 11 + 2 * deltaBound d) ^ 4 + 1)
      (((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4)) ^ 4 + 1))

/-- **Corollary 2.2(ii), the inequality (C2)**: outside the exceptional set and above the
threshold, `(1/6)·log(q_∀(x)) ≤ (1 + ε_E)·(log-diff_X(x) + log-cond_D(x)) + C_K` with
`C_K = 40·η_prm + B_K/3`, `ε_E ≤ 1`, and `log-diff_X(x) + log-cond_D(x) ≥ 0`. -/
theorem c2 {P : Corollary312VariantData.{u, v} AG TG → Prop} (hd : 1 ≤ d)
    (ex : ThetaDataExistence P I) (cheb : ChebyshevBound) (pnt : PrimeCountingBound)
    (h312 : ∀ X : Corollary312VariantData.{u, v} AG TG, P X → Corollary312Variant X)
    (x : T.Pt T.tripod) (hx : x ∈ T.cbsSet K ∩ T.ptLE T.tripod d) (hxe : x ∉ I.excCore)
    (hH : I.threshold cheb ≤ I.h x) :
    1 / 6 * I.h x ≤ (1 + epsilonE (deltaBound d) (I.h x)) *
        (T.logDiff T.tripod x + T.logCond T.tripod x) + (40 * pnt.η + I.B / 3) ∧
      epsilonE (deltaBound d) (I.h x) ≤ 1 ∧
      0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x := by
  classical
  -- notation and the size of `h`
  obtain ⟨L, hLdef⟩ : ∃ L, L = I.localData x hx := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h, h = I.h x := ⟨_, rfl⟩
  rw [← hhdef] at hH ⊢
  have hδ : (2 : ℝ) ≤ deltaBound d := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold deltaBound; nlinarith
  have hδ1 : (1 : ℝ) ≤ deltaBound d := by linarith
  have hLh : L.height = h := by rw [hLdef, hhdef]; exact I.localData_height x hx
  have hξ2 : cheb.ξ ^ 2 ≤ h := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hH)
  have hT : 49 + 8 * max I.TK 0 ≤ h :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hH)
  have hP5 : (I.B + 11 + 2 * deltaBound d) ^ 4 + 1 ≤ h :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hH)
  have hε1 : ((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4)) ^ 4 + 1 ≤ h :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hH)
  have hξ5 := cheb.five_le
  have hh25 : 25 ≤ h := by nlinarith
  have hh1 : 1 ≤ h := by linarith
  have hh0 : 0 < h := by linarith
  -- consume the fourth-power thresholds now, and drop them from the context
  have hε1' : epsilonE (deltaBound d) h ≤ 1 := epsilonE_le hδ1 one_pos (by
    have : ((60 * deltaBound d) ^ 2 * (2 * deltaBound d + 4) / 1) ^ 4 ≤ h := by
      rw [div_one]; linarith
    exact this) hh1
  have hP5big : ¬ h ≤ (I.B + 11 + 2 * deltaBound d) ^ 4 := fun hle => by linarith
  clear hε1 hP5 hH
  obtain ⟨r, hrdef⟩ : ∃ r, r = Real.sqrt h := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hrdef ▸ Real.sqrt_nonneg _
  have hrr : r * r = h := hrdef ▸ Real.mul_self_sqrt hh0.le
  have hξr : cheb.ξ ≤ r := by
    rw [hrdef]; exact Real.le_sqrt_of_sq_le hξ2
  have hr5 : 5 ≤ r := hξ5.trans hξr
  have hr7 : 7 ≤ r := by nlinarith [le_max_left I.TK 0, le_max_right I.TK 0]
  have hlog1 : 1 ≤ Real.log (2 * deltaBound d * h) := by
    have : Real.exp 1 ≤ 2 * deltaBound d * h := by
      have := Real.exp_one_lt_d9; nlinarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  -- the prime `ℓ` ((P1)–(P3))
  have hdeg : (L.deg : ℝ) ≤ deltaBound d := by
    have := I.localData_deg_le x hx
    rw [hLdef]; unfold deltaBound; exact_mod_cast this
  obtain ⟨ℓ, hℓp, hℓlo, hℓhi, hP2, hP3⟩ :=
    L.exists_prime_selection cheb (deltaBound d) hδ hdeg (by rw [hLh, ← hrdef]; exact hξr)
  rw [hLh, ← hrdef] at hℓlo hℓhi hP3
  have hℓ5 : (5 : ℝ) ≤ ℓ := hr5.trans hℓlo
  have hℓ7r : (7 : ℝ) ≤ ℓ := hr7.trans hℓlo
  have hℓ7 : 7 ≤ ℓ := by exact_mod_cast hℓ7r
  have hℓ2 : ℓ ≠ 2 := by omega
  have hlogℓ0 : 0 ≤ Real.log ℓ := Real.log_nonneg (by linarith)
  -- (P4): no `ℓ`-cyclic subgroup scheme, since `h` is large
  have hP4 : ¬ I.HasCyclicSubgroup x ℓ := by
    intro hcyc
    have hb := I.cyclic_bound x hx ℓ hℓp hcyc
    rw [← hhdef] at hb
    have hlogℓ : Real.log ℓ ≤ ℓ - 2 := by
      have := log_le_half_of_pos (by linarith : (0:ℝ) < ℓ); linarith
    -- `(ℓ-2)/24 · h ≤ 2 log ℓ + T_K ≤ 2(ℓ-2) + T_K`, so `h ≤ 48 + 24 T_K/(ℓ-2) ≤ 48 + 8 T_K`
    have hTK : I.TK ≤ max I.TK 0 := le_max_left _ _
    have hmax0 : 0 ≤ max I.TK 0 := le_max_right _ _
    have hℓ2' : (5 : ℝ) ≤ ℓ - 2 := by linarith
    have h1 : (ℓ - 2 : ℝ) * h ≤ 24 * (2 * (ℓ - 2) + max I.TK 0) := by
      have : (ℓ - 2 : ℝ) / 24 * h ≤ 2 * (ℓ - 2) + max I.TK 0 := by linarith
      linarith
    have h2 : 24 * (2 * (ℓ - 2) + max I.TK 0) ≤ (ℓ - 2 : ℝ) * (48 + 8 * max I.TK 0) := by
      nlinarith
    have := le_of_mul_le_mul_left (h1.trans h2) (by linarith : (0:ℝ) < ℓ - 2)
    linarith
  -- (P5): some bad place away from `2` and `ℓ`, since `h` is large
  have hℓup : (ℓ : ℝ) ≤ 20 * deltaBound d ^ 2 * h ^ 2 := by
    have h1 : Real.log (2 * deltaBound d * h) ≤ 2 * deltaBound d * h :=
      log_le_self_of_pos (by positivity)
    have h2 : r ≤ h := by nlinarith [mul_nonneg hr0 (by linarith : (0:ℝ) ≤ r - 1)]
    calc (ℓ : ℝ) ≤ 10 * deltaBound d * r * Real.log (2 * deltaBound d * h) := hℓhi
      _ ≤ 10 * deltaBound d * r * (2 * deltaBound d * h) := by gcongr
      _ = 20 * deltaBound d ^ 2 * (r * h) := by ring
      _ ≤ 20 * deltaBound d ^ 2 * (h * h) := by gcongr
      _ = 20 * deltaBound d ^ 2 * h ^ 2 := by ring
  have hlogℓ6 : Real.log ℓ ≤ 6 * Real.log (2 * deltaBound d * h) :=
    (Real.log_le_log (by linarith) hℓup).trans (log_bound_ell hδ1 hh1)
  -- the part of the height over `ℓ` is at most `√h · log ℓ`
  have hheightℓ : L.heightEq ℓ ≤ r * Real.log ℓ := by
    have hbound : ∀ v ∈ L.bad.filter (fun v => L.p v = ℓ),
        (L.hv v : ℝ) * L.f v * Real.log (L.p v) ≤ r * Real.log ℓ * L.f v := by
      intro v hv
      rw [Finset.mem_filter] at hv
      rw [hv.2]
      have := hP3 v hv.1 hv.2
      have hf : (0 : ℝ) ≤ L.f v := by positivity
      nlinarith [mul_nonneg hf hlogℓ0]
    unfold LocalHeightData.heightEq
    rw [div_le_iff₀ (by exact_mod_cast L.one_le_deg)]
    calc ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), (L.hv v : ℝ) * L.f v * Real.log (L.p v)
        ≤ ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), r * Real.log ℓ * L.f v :=
          Finset.sum_le_sum hbound
      _ = r * Real.log ℓ * ∑ v ∈ L.bad.filter (fun v => L.p v = ℓ), (L.f v : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ r * Real.log ℓ * L.deg := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact_mod_cast L.sum_f_le ℓ
  have hsplit := L.height_eq_add 2 ℓ hℓ2.symm
  rw [hLh] at hsplit
  have hP5' : ∃ v ∈ L.bad, L.p v ≠ 2 ∧ L.p v ≠ ℓ := by
    by_contra hnone
    push Not at hnone
    have hother : L.heightOther 2 ℓ = 0 := by
      unfold LocalHeightData.heightOther
      rw [Finset.filter_false_of_mem, Finset.sum_empty, zero_div]
      intro v hv ⟨h1, h2⟩
      exact h2 (hnone v hv h1)
    -- `h ≤ B + √h·log ℓ ≤ B + (3 + 2δ)√h + 8 h^{3/4}`, contradicting `h ≥ (B+11+2δ)⁴+1`
    have hB2 : L.heightEq 2 ≤ I.B := hLdef ▸ I.heightEq_two_le x hx
    obtain ⟨s, hsdef⟩ : ∃ s, s = Real.sqrt r := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := hsdef ▸ Real.sqrt_nonneg _
    have hss : s * s = r := hsdef ▸ Real.mul_self_sqrt hr0
    have hlogh : Real.log h ≤ 4 * s := by
      have := log_le_four_mul_sqrt_sqrt hh1
      rw [← hrdef, ← hsdef] at this; exact this
    have hlogℓ' : Real.log ℓ ≤ 3 + 2 * deltaBound d + 8 * s :=
      log_ell_bound hδ1 hh1 (by linarith) hℓup hlogh
    have hmain : h ≤ I.B + r * Real.log ℓ := by linarith
    exact hP5big (p5_height_bound I.B_nonneg hδ1 hr0 hrr hs0 hss hh1 hlogℓ' hmain)
  -- (P6) and the Θ-data
  have hP6 : I.SL2Image x ℓ := by
    subst hLdef
    exact I.sl2_of x hx ℓ hℓp (by exact_mod_cast hℓ5) hP2 hP4 hP5'
  obtain ⟨X, inv, hPX, cert, ⟨est⟩, hXℓ, hXd, hXq, hDiff, hCond1, hCond2⟩ :=
    ex.thetaData x hx hxe ℓ hℓp hℓ7 (hLdef ▸ hP2) (by rw [← hLdef, ← hhdef, ← hrdef]; exact hP3)
      (hLdef ▸ hP5') hP6
  rw [← hLdef] at hXq
  -- Theorem 1.10
  have h110 := inv.theorem110 cert est pnt (h312 X hPX)
  rw [hXℓ, hXq] at h110
  -- the numerical factors of Theorem 1.10 in terms of `δ`
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdmod : 20 * (X.dmod : ℝ) ≤ deltaBound d := by
    have : (X.dmod : ℝ) ≤ d := by exact_mod_cast hXd
    unfold deltaBound; linarith
  have heStar : (inv.eStar : ℝ) ≤ deltaBound d := by
    have h1 : (inv.emod : ℝ) ≤ X.dmod := by exact_mod_cast inv.emod_le_dmod
    have h2 : (X.dmod : ℝ) ≤ d := by exact_mod_cast hXd
    rw [inv.eStar_cast]; unfold deltaBound; linarith
  have hDF0 : 0 ≤ inv.logDtpd + inv.logFtpd := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  -- `h ≤ log(q) + B + 6·√h·log(2δh)`
  have hlogQ : h ≤ L.heightOther 2 ℓ + I.B + 6 * (r * Real.log (2 * deltaBound d * h)) := by
    have hB2 : L.heightEq 2 ≤ I.B := hLdef ▸ I.heightEq_two_le x hx
    have := mul_le_mul_of_nonneg_left hlogℓ6 hr0
    linarith
  have hLC0 : 0 ≤ T.logDiff T.tripod x + T.logCond T.tripod x := by
    linarith [inv.logDtpd_nonneg, inv.logFtpd_nonneg]
  refine ⟨?_, hε1', hLC0⟩
  exact c2_final (by linarith) hrr hlog1 hδ1 hℓlo hℓhi hdmod heStar hDF0 I.B_nonneg
    (by linarith [pnt.one_lt_η]) h110 hlogQ hDiff hCond1 (by rw [epsilonE, hrdef]) hε1'

end Corollary22Inputs

end Iut
