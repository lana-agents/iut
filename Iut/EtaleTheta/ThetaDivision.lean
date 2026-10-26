/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.TateMulByN

/-!
# Theta block division and the division polynomial in theta functions (MR14, G1 step 3)

Analytic inputs for showing that the theta level function `F_N` is a unit on `Ÿ'_N`
(`MR14-plan.md`, run-3 hand-off):

* `exists_theta_pull_div`: for `T₂.q^m = T₁.q^r` (`m > 0`, `r > 0` even),
  `θ_{T₁}(-u^m) = θ_{T₂}(-u)·C(u)` with `C` an everywhere convergent weight-`(rm - 1)` theta
  family for `T₂` (`tate-curves-theta`'s division theorem `exists_convBlock_eq'`, by dimension
  counting). Special cases: `θ(-u^m) = θ(-u)·C(u)` and `θ_q(-v) = θ_{q^N}(-v)·C(v)` (`N` even).
* `exists_poly_of_isWeightFamily_deg`: Tate's theorem with the degree bounds
  `deg P < k/2 + 1`, `deg Q < (k-1)/2` (pole order `≤ k`).
* `poly_eq_zero_of_eval_off`: polynomial identities from values off the zeros of `R ≠ 0`.
* **`exists_ΨSq_theta`** (`m = 2(i+1)`, `‖2‖ = 1`): the `m`-division polynomial in theta
  functions, `u^{-(m²-m)}·θ(-u^m)² = α·ΨSq_m(X(u))·θ(-u)^{2m²}` with `α ≠ 0`. Proof: by the
  division `θ(-u^m)²/θ(-u)^{2m²} = u^{-a}C(u)²/θ(-u)^{2m²-2}` is `P₁(x) + y Q₁(x)` with
  `deg P₁ ≤ m² - 1`, `deg Q₁ < m² - 2`; the group law `X(u^m) = Φ_m/ΨSq_m` and
  `X·θ² = XThetaSq` give `Φ_m (P₁ + y Q₁) = ΨSq_m (P₂ + y Q₂)`, so `ΨSq_m ∣ P₁, Q₁`
  (`IsCoprime Φ_m ΨSq_m`), hence `Q₁ = 0` and `P₁ = α ΨSq_m` by degrees.
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

lemma theta_one_ne_zero_of_charZero [CharZero K] (T : TateParameter K) : T.theta 1 ≠ 0 := by
  intro h
  obtain ⟨k, hk⟩ := (T.theta_eq_zero_iff 1).mp h
  have hn := congrArg norm hk
  rw [Units.val_one, norm_one, norm_neg, norm_zpow, eq_comm,
    zpow_eq_one_iff_right₀ (norm_nonneg _) T.norm_lt_one.ne] at hn
  subst hn
  rw [zpow_zero, Units.val_one] at hk
  have h2 : (2 : K) = 0 := by linear_combination hk
  exact two_ne_zero h2

/-- **Division of a pulled-back theta function by a theta block.** Let `T₂.q^m = T₁.q^r` with
`m > 0` and `r > 0` even. Then `u ↦ θ_{T₁}(-u^m)` (a weight-`rm` family for `T₂`) vanishes at
`u = 1`, and `θ_{T₁}(-u^m) = θ_{T₂}(-u)·C(u)` with `C` a weight-`(rm - 1)` family for `T₂`. -/
theorem exists_theta_pull_div [CharZero K] (T₁ T₂ : TateParameter K) {m r : ℕ} (hm0 : 0 < m)
    (hr : Even r) (hr0 : 0 < r) (hmr : T₂.q ^ m = T₁.q ^ r) :
    ∃ (A : Kˣ) (c : ℤ → K), T₂.IsWeightFamily (r * m - 1) A c ∧
      (T₂.q * (-1))⁻¹ * A =
        (T₂.q ^ (0 : ℤ))⁻¹ * (T₁.q * (-1))⁻¹ ^ r * (T₁.q ^ (1 * r.choose 2))⁻¹ ∧
      ∀ u : Kˣ, T₁.theta (-(u ^ m)) = T₂.theta (-u) * ∑' n : ℤ, c n * (u : K) ^ n := by
  set M : Kˣ := (T₂.q ^ (0 : ℤ))⁻¹ * (T₁.q * (-1))⁻¹ ^ r * (T₁.q ^ (1 * r.choose 2))⁻¹
    with hMdef
  have hF := isWeightFamily_pullIter hm0 hmr (isWeightFamily_thetaBlock (t := T₁) (-1)) 0
  have hG := isWeightFamily_pullIter hm0 hmr (isWeightFamily_thetaBlock (t := T₁) 1) 0
  have hMG : (T₂.q ^ (0 : ℤ))⁻¹ * (T₁.q * 1)⁻¹ ^ r * (T₁.q ^ (1 * r.choose 2))⁻¹ = M := by
    rw [hMdef]
    congr 2
    obtain ⟨j, rfl⟩ := hr
    rw [inv_pow, inv_pow, mul_pow, mul_pow, ← two_mul, pow_mul (-1 : Kˣ), neg_one_sq, one_pow,
      one_pow]
  rw [hMG] at hG
  have hw : 1 * r * m = 1 + (r * m - 1) := by
    have : 1 ≤ r * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [one_mul]
    omega
  rw [hw] at hF hG
  have hk : 0 < r * m - 1 := by
    obtain ⟨j, rfl⟩ := hr
    have : 1 ≤ j := by omega
    have : 2 ≤ (j + j) * m := by nlinarith
    omega
  have hser : ∀ (e : Kˣ) (u : Kˣ),
      (∑' n : ℤ, pullCoef (T₁.thetaBlock e) m 0 n * (u : K) ^ n) = T₁.theta (e * u ^ m) := by
    intro e u
    rw [(hasSum_pullCoef (isWeightFamily_thetaBlock (t := T₁) e) hm0 0 u).tsum_eq,
      tsum_thetaBlock]
    simp
  obtain ⟨c, hc⟩ := exists_convBlock_eq' (t := T₂) hk (-1) (A := (T₂.q * (-1)) * M)
    (by group) (x₀ := 1) (by rw [mul_one]; exact T₂.theta_neg_one)
    ⟨_, hG⟩ (by
      rw [evalAt_apply]
      change (∑' n : ℤ, pullCoef (T₁.thetaBlock 1) m 0 n * ((1 : Kˣ) : K) ^ n) ≠ 0
      rw [hser, one_pow, one_mul]
      exact theta_one_ne_zero_of_charZero T₁)
    ⟨_, hF⟩ (by
      rw [evalAt_apply]
      change (∑' n : ℤ, pullCoef (T₁.thetaBlock (-1)) m 0 n * ((1 : Kˣ) : K) ^ n) = 0
      rw [hser, one_pow, mul_one]
      exact T₁.theta_neg_one)
  refine ⟨(T₂.q * (-1)) * M, c, c.2, by group, fun u => ?_⟩
  have h := tsum_eq_theta_mul_of_forall_conv_eq (t := T₂) c hc u
  rw [hser, neg_one_mul] at h
  rw [h, neg_one_mul]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem degree_polyOf_lt {m : ℕ} (a : Fin m → K) : (polyOf a).degree < m :=
  Polynomial.degree_sum_fin_lt a

/-- **Tate's theorem with degree bounds**: a weight-`k` family with the multiplier of `θ(-u)ᵏ`
has values `(P(X) + Y·Q(X))·θ(-u)ᵏ` with `deg P < k/2 + 1` and `deg Q < (k-1)/2` (pole order
`≤ k` at the origin). -/
theorem exists_poly_of_isWeightFamily_deg (t : TateParameter K) (h12 : (12 : K) ≠ 0) {k : ℕ}
    (hk : 0 < k) {F : ℤ → K} (hF : t.IsWeightFamily k (multθ t ^ k) F) :
    ∃ P Q : Polynomial K, P.degree < (k / 2 + 1 : ℕ) ∧ Q.degree < ((k - 1) / 2 : ℕ) ∧
      ∀ u : Kˣ, OffOrbit t u →
      (∑' n : ℤ, F n * (u : K) ^ n) =
        (P.eval (t.X u) + t.Y u * Q.eval (t.X u)) * t.theta (-u) ^ k := by
  haveI := finiteDimensional_weightSpace (t := t) (A := multθ t ^ k) hk
  have hli := linearIndependent_monoBasis t h12 k
  have hspan : Submodule.span K (Set.range (monoBasis t k)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by
      rw [card_monoIdx hk, finrank_weightSpace hk])
  have hmem : (⟨F, hF⟩ : t.weightSpace k (multθ t ^ k)) ∈
      Submodule.span K (Set.range (monoBasis t k)) := hspan ▸ Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
  refine ⟨polyOf fun i => g (Sum.inl i), polyOf fun i => g (Sum.inr i), degree_polyOf_lt _,
    degree_polyOf_lt _, fun u hu => ?_⟩
  rw [← tsum_monoBasis_comb t g hu, hg]

/-- A polynomial identity from values off the zeros of a fixed nonzero polynomial `R`. -/
theorem poly_eq_zero_of_eval_off (t : TateParameter K) (h12 : (12 : K) ≠ 0) {R : Polynomial K}
    (hR : R ≠ 0) (P Q : Polynomial K)
    (h : ∀ u : Kˣ, OffOrbit t u → R.eval (t.X u) ≠ 0 →
      P.eval (t.X u) + t.Y u * Q.eval (t.X u) = 0) :
    P = 0 ∧ Q = 0 := by
  obtain ⟨hP, hQ⟩ := poly_eq_zero_of_eval t h12 (R * P) (R * Q) fun u hu => by
    by_cases h0 : R.eval (t.X u) = 0
    · simp [h0]
    · simp only [Polynomial.eval_mul]
      linear_combination R.eval (t.X u) * h u hu h0
  exact ⟨(mul_eq_zero.mp hP).resolve_left hR, (mul_eq_zero.mp hQ).resolve_left hR⟩

lemma choose_two_even (i : ℕ) : (2 * (i + 1)).choose 2 = (i + 1) * (2 * i + 1) := by
  rw [Nat.choose_two_right]
  refine Nat.div_eq_of_eq_mul_left two_pos ?_
  rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
  ring

/-- **The `m`-division polynomial in theta functions** (`m = 2(i+1)` even, odd residue
characteristic): there is `α ≠ 0` with
`u^{-(m²-m)}·θ(-u^m)² = α·ΨSq_m(X(u))·θ(-u)^{2m²}` for all `u` off the period orbit, i.e.
`ψ_m² = α⁻¹·u^{-(m²-m)}θ(-u^m)²/θ(-u)^{2m²}` on the Tate curve. -/
theorem exists_ΨSq_theta [CharZero K] (t : TateParameter K) (h2 : ‖(2 : K)‖ = 1)
    (h12 : (12 : K) ≠ 0) (i : ℕ) :
    ∃ α : K, α ≠ 0 ∧ ∀ u : Kˣ, OffOrbit t u →
      (u : K) ^ (-(((2 * (i + 1)) * (2 * i + 1) : ℕ) : ℤ)) * t.theta (-(u ^ (2 * (i + 1)))) ^ 2 =
        α * (t.tateCurve.ΨSq ((2 * (i + 1) : ℕ) : ℤ)).eval (t.X u) *
          t.theta (-u) ^ (2 * (2 * (i + 1)) * (2 * (i + 1))) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  have hm0 : 0 < 2 * (i + 1) := by omega
  have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
  have hch := choose_two_even i
  -- the division `θ(-u^m) = θ(-u)·C(u)`
  obtain ⟨A, c, hc, hA, hdiv⟩ := exists_theta_pull_div t t hm0 ⟨i + 1, by omega⟩ hm0 rfl
  have hA' : A = (t.q * (-1)) * ((t.q ^ (0 : ℤ))⁻¹ * (t.q * (-1))⁻¹ ^ (2 * (i + 1)) *
      (t.q ^ (1 * (2 * (i + 1)).choose 2))⁻¹) := by rw [← hA]; group
  -- the family `u^{-a}·C(u)²`, weight `2m² - 2`
  have hFc : t.IsWeightFamily (2 * (2 * (i + 1)) * (2 * (i + 1)) - 2)
      (multθ t ^ (2 * (2 * (i + 1)) * (2 * (i + 1)) - 2))
      (pullCoef (cpow c 2) 1 (((2 * (i + 1)) * (2 * i + 1) : ℕ) : ℤ)) := by
    have h := isWeightFamily_pullIter (T₁ := t) (T₂ := t) one_pos rfl
      (isWeightFamily_cpow t hc 2) (((2 * (i + 1)) * (2 * i + 1) : ℕ) : ℤ)
    convert h using 1
    · rw [mul_one, mul_one]
      ring_nf
      omega
    · rw [hA', hch, show Nat.choose 1 2 = 0 from rfl, mul_zero, pow_zero, inv_one, mul_one,
        show 2 * (2 * (i + 1)) * (2 * (i + 1)) - 2 = 2 * (4 * i * i + 8 * i + 3) by
          ring_nf; omega]
      ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_neg, zpow_natCast, zpow_zero, multθ, mul_neg_one, pow_mul,
        inv_pow, neg_sq, one_mul, inv_one]
      field_simp
      ring
  -- the family `u^{-a}·X(u^m)·θ(-u^m)²`, weight `2m²`
  have hFX : t.IsWeightFamily (2 * (2 * (i + 1)) * (2 * (i + 1)))
      (multθ t ^ (2 * (2 * (i + 1)) * (2 * (i + 1))))
      (pullCoef t.XThetaSqCoeff (2 * (i + 1)) (((2 * (i + 1)) * (2 * i + 1) : ℕ) : ℤ)) := by
    have h := isWeightFamily_pullIter (T₁ := t) (T₂ := t) hm0 rfl (isWeightFamily_XThetaSq t)
      (((2 * (i + 1)) * (2 * i + 1) : ℕ) : ℤ)
    convert h using 1
    rw [hch]
    ext
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      zpow_natCast, multθ, mul_neg_one, pow_mul, inv_pow, neg_sq]
    field_simp
    ring
  have hmm : 8 ≤ 2 * (2 * (i + 1)) * (2 * (i + 1)) := by nlinarith
  obtain ⟨P₁, Q₁, hP₁, hQ₁, e₁⟩ := exists_poly_of_isWeightFamily_deg t h12 (by omega) hFc
  obtain ⟨P₂, Q₂, -, -, e₂⟩ := exists_poly_of_isWeightFamily_deg t h12 (by omega) hFX
  set m := 2 * (i + 1) with hm
  set a : ℤ := ((m * (2 * i + 1) : ℕ) : ℤ) with ha
  have hk : 2 * m * m = (2 * m * m - 2) + 2 := by omega
  have hmm2 : 2 * m * m = 2 * (m * m) := by ring
  -- values of the two families
  have vc : ∀ u : Kˣ, (∑' n : ℤ, pullCoef (cpow c 2) 1 a n * (u : K) ^ n) =
      (u : K) ^ (-a) * (∑' n : ℤ, c n * (u : K) ^ n) ^ 2 := fun u => by
    rw [(hasSum_pullCoef (isWeightFamily_cpow t hc 2) one_pos a u).tsum_eq, pow_one,
      tsum_cpow t hc]
  have vX : ∀ u : Kˣ, OffOrbit t (u ^ m) →
      (∑' n : ℤ, pullCoef t.XThetaSqCoeff m a n * (u : K) ^ n) =
        (u : K) ^ (-a) * (t.X (u ^ m) * t.theta (-(u ^ m)) ^ 2) := fun u hum => by
    rw [(hasSum_pullCoef (isWeightFamily_XThetaSq t) hm0 a u).tsum_eq,
      (t.hasSum_XThetaSqCoeff hum).tsum_eq]
  -- the polynomial relation `Φ·(P₁ + y Q₁) = ΨSq·(P₂ + y Q₂)`
  have hm' : (((m : ℤ) : K)) ≠ 0 := by rw [Int.cast_natCast]; exact Nat.cast_ne_zero.2 hm0.ne'
  have hΨ0 : t.tateCurve.ΨSq (m : ℤ) ≠ 0 := t.tateCurve.ΨSq_ne_zero hm'
  obtain ⟨hpP, hpQ⟩ := poly_eq_zero_of_eval_off t h12 hΨ0
    (t.tateCurve.Φ (m : ℤ) * P₁ - t.tateCurve.ΨSq (m : ℤ) * P₂)
    (t.tateCurve.Φ (m : ℤ) * Q₁ - t.tateCurve.ΨSq (m : ℤ) * Q₂) fun u hu hΨ => by
      obtain ⟨hum, hX, -⟩ := tate_pow_coords h2 h12 hu hΨ
      have h1 := e₁ u hu
      have h2' := e₂ u hu
      rw [vc] at h1
      rw [vX u hum, hX, hdiv u] at h2'
      have hθ : t.theta (-u) ≠ 0 := theta_neg_ne_zero t hu
      have hθk : t.theta (-u) ^ (2 * m * m - 2) ≠ 0 := pow_ne_zero _ hθ
      rw [hk, pow_add] at h2'
      simp only [Polynomial.eval_sub, Polynomial.eval_mul]
      have hr : (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) *
          ((t.tateCurve.Φ (m : ℤ)).eval (t.X u) / (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u)) =
          (t.tateCurve.Φ (m : ℤ)).eval (t.X u) := by field_simp
      have key : ((t.tateCurve.Φ (m : ℤ)).eval (t.X u) *
          ((P₁.eval (t.X u) + t.Y u * Q₁.eval (t.X u)))
          - (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) *
            (P₂.eval (t.X u) + t.Y u * Q₂.eval (t.X u))) *
          (t.theta (-u) ^ (2 * m * m - 2) * t.theta (-u) ^ 2) = 0 := by
        linear_combination (-((t.tateCurve.Φ (m : ℤ)).eval (t.X u) * t.theta (-u) ^ 2)) * h1 +
          (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) * h2' -
          ((u : K) ^ (-a) * t.theta (-u) ^ 2 * (∑' n : ℤ, c n * (u : K) ^ n) ^ 2) * hr
      rcases mul_eq_zero.mp key with h | h
      · linear_combination h
      · exact absurd h (mul_ne_zero hθk (pow_ne_zero _ hθ))
  have hΦP : t.tateCurve.Φ (m : ℤ) * P₁ = t.tateCurve.ΨSq (m : ℤ) * P₂ := sub_eq_zero.mp hpP
  have hΦQ : t.tateCurve.Φ (m : ℤ) * Q₁ = t.tateCurve.ΨSq (m : ℤ) * Q₂ := sub_eq_zero.mp hpQ
  obtain ⟨a', b', hab⟩ :=
    WeierstrassCurve.Affine.isCoprime_Φ_ΨSq (W := t.tateCurve.toAffine) two_ne_zero (m : ℤ)
  have hab' : a' * t.tateCurve.Φ (m : ℤ) + b' * t.tateCurve.ΨSq (m : ℤ) = 1 := hab
  have dP : t.tateCurve.ΨSq (m : ℤ) ∣ P₁ :=
    ⟨a' * P₂ + b' * P₁, by linear_combination (-P₁) * hab' + a' * hΦP⟩
  have dQ : t.tateCurve.ΨSq (m : ℤ) ∣ Q₁ :=
    ⟨a' * Q₂ + b' * Q₁, by linear_combination (-Q₁) * hab' + a' * hΦQ⟩
  have hdeg : (t.tateCurve.ΨSq (m : ℤ)).natDegree = m * m - 1 := by
    rw [t.tateCurve.natDegree_ΨSq hm', Int.natAbs_natCast, sq]
  have hQ0 : Q₁ = 0 := by
    by_contra hQne
    have := dQ
    refine hQne (Polynomial.eq_zero_of_dvd_of_natDegree_lt dQ ?_)
    rw [hdeg]
    have h' := (Polynomial.natDegree_lt_iff_degree_lt hQne).mpr hQ₁
    omega
  obtain ⟨g, hg⟩ := dP
  have hg0 : g.natDegree = 0 := by
    by_cases hP0 : P₁ = 0
    · rw [hP0, eq_comm, mul_eq_zero, or_iff_right hΨ0] at hg
      rw [hg, Polynomial.natDegree_zero]
    have hgne : g ≠ 0 := by rintro rfl; exact hP0 (by rw [hg, mul_zero])
    have h' := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hP₁
    rw [hg, Polynomial.natDegree_mul hΨ0 hgne, hdeg] at h'
    have : 1 ≤ m * m := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hgC := Polynomial.eq_C_of_natDegree_eq_zero hg0
  -- the identity
  have main : ∀ u : Kˣ, OffOrbit t u →
      (u : K) ^ (-a) * t.theta (-(u ^ m)) ^ 2 =
        g.coeff 0 * (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) * t.theta (-u) ^ (2 * m * m) := by
    intro u hu
    have h1 := e₁ u hu
    rw [vc, hQ0, hg, hgC] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_zero, mul_zero,
      add_zero] at h1
    rw [hdiv u, hk, pow_add, mul_pow]
    linear_combination t.theta (-u) ^ 2 * h1
  refine ⟨g.coeff 0, fun h0 => ?_, main⟩
  obtain ⟨u₀, hn, hne⟩ := exists_good_unit t (N := i + 1) (by omega)
  have hu₀ : OffOrbit t u₀ := offOrbit_of_norm hn fun h1 => hne (by rw [h1, one_pow])
  have hum : OffOrbit t (u₀ ^ m) := offOrbit_of_norm (by rw [Units.val_pow_eq_pow_val,
    norm_pow, hn, one_pow]) (by rw [Units.val_pow_eq_pow_val]; exact hne)
  have := main u₀ hu₀
  rw [h0, zero_mul, zero_mul, mul_eq_zero, or_iff_right (zpow_ne_zero _ u₀.ne_zero)] at this
  exact theta_neg_ne_zero t hum (pow_eq_zero_iff two_ne_zero |>.mp this)

end Iut.EtaleTheta
