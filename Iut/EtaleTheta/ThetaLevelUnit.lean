/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaDivision
import Iut.EtaleTheta.ThetaLevelGalois

/-!
# The theta level function is a unit on `Ÿ'_N` (MR14, G1 step 3)

Let `q` be a Tate parameter over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1`, `s² = q`, `N` even, `Q = s^N`, `Q' = q^N`, `w = u^{2N}`. The theta level function
`F_N = f_N∘ψ` of `exists_thetaLevel_etale` has the values
`F_N(u) = Θ̈_q(u^N)/Θ̈_{q^N}(u^N)^N = u^{N-N²}·θ_q(-w)/θ_{Q'}(-w)^N`. We show that `F_N` and
`F_N⁻¹` lie in `K[E][1/ψ_{2N}]` (the coordinate ring of `E_q ∖ E_q[2N]`), i.e. `F_N` is a unit on
`Ÿ'_N` ([EtTh], §1: the divisor of `f_N` is supported on the cusps, MR14 plan, route R-alg):

* `exists_invLevelFam`: `u^{-(3N²-N)}·θ_{Q'}(-w)^N·θ_q(-w)` is a weight-`8N²` theta family with
  the multiplier of `θ(-u)^{8N²}`; by `exists_ΨSq_theta` it is
  `α·F_N(u)⁻¹·ΨSq_{2N}(X(u))·θ(-u)^{8N²}`;
* `exists_levelFam`: with the division `θ_q(-w) = θ_{Q'}(-w)·C(w)` (`exists_theta_pull_div`),
  `u^{-(4N³-N²-N)}·θ_q(-w)^{N+1}·C(w)^N` is a weight-`8N³` family; it is
  `α^N·F_N(u)·ΨSq_{2N}(X(u))^N·θ(-u)^{8N³}`;
* Tate's theorem turns both into elements `P + yQ` of `K[E]`, so
  `F_N⁻¹ = α⁻¹(P₁ + yQ₁)/ψ_{2N}²` and `F_N = α^{-N}(P₂ + yQ₂)/ψ_{2N}^{2N}`
  (**`exists_thetaLevel_unit`**), and the images of `F_N^{±1}` in `Ω` are integral over `K[τ]`
  (`isIntegral_mulByNEmb`).
-/

open CategoryTheory AlgebraicGeometry Polynomial Belyi Belyi.P1 Belyi.Anabelian Pi1.Orbifold
open AffOrbicurve

noncomputable section

universe u

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine CurvesJacobian.Cusp

section Families

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-- The family of `θ_{q^N}(-u^{2N})^N · u^{-(3N²-N)}·θ_q(-u^{2N})` (`N = j + 1`). -/
def invLevelFam (t : TateParameter K) (j : ℕ) : ℤ → K :=
  fun n => ∑' l : ℤ,
    cpow (pullCoef ((tatePow t (j + 1) (Nat.succ_pos j)).thetaBlock (-1)) (2 * (j + 1)) 0)
      (j + 1) (n - l) *
    pullCoef (t.thetaBlock (-1)) (2 * (j + 1)) (((j + 1) * (3 * j + 2) : ℕ) : ℤ) l

theorem isWeightFamily_invLevelFam (t : TateParameter K) (j : ℕ) :
    t.IsWeightFamily (8 * (j + 1) * (j + 1)) (multθ t ^ (8 * (j + 1) * (j + 1)))
      (invLevelFam t j) := by
  have h1 := isWeightFamily_pullIter (T₁ := tatePow t (j + 1) (Nat.succ_pos j)) (T₂ := t)
    (m := 2 * (j + 1)) (r := 2) (by omega) (by rw [tatePow_q, ← pow_mul, mul_comm])
    (isWeightFamily_thetaBlock (t := tatePow t (j + 1) (Nat.succ_pos j)) (-1)) 0
  have h2 := isWeightFamily_pullIter (T₁ := t) (T₂ := t) (m := 2 * (j + 1)) (r := 2 * (j + 1))
    (by omega) rfl (isWeightFamily_thetaBlock (t := t) (-1)) (((j + 1) * (3 * j + 2) : ℕ) : ℤ)
  have h := (isWeightFamily_cpow t h1 (j + 1)).conv h2
  convert h using 1
  · ring
  · rw [choose_two_even j, show Nat.choose 2 2 = 1 from rfl, tatePow_q]
    ext
    have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_neg, zpow_natCast, zpow_zero, multθ, mul_neg_one, pow_mul, inv_pow, neg_sq,
      one_mul, inv_one, mul_one]
    field_simp
    ring_nf
    simp only [inv_pow]
    field_simp
    ring
  · rfl

theorem tsum_invLevelFam (t : TateParameter K) (j : ℕ) (u : Kˣ) :
    (∑' n : ℤ, invLevelFam t j n * (u : K) ^ n) =
      (tatePow t (j + 1) (Nat.succ_pos j)).theta (-(u ^ (2 * (j + 1)))) ^ (j + 1) *
        ((u : K) ^ (-(((j + 1) * (3 * j + 2) : ℕ) : ℤ)) * t.theta (-(u ^ (2 * (j + 1))))) := by
  have h1 := isWeightFamily_pullIter (T₁ := tatePow t (j + 1) (Nat.succ_pos j)) (T₂ := t)
    (m := 2 * (j + 1)) (r := 2) (by omega) (by rw [tatePow_q, ← pow_mul, mul_comm])
    (isWeightFamily_thetaBlock (t := tatePow t (j + 1) (Nat.succ_pos j)) (-1)) 0
  have h2 := isWeightFamily_pullIter (T₁ := t) (T₂ := t) (m := 2 * (j + 1)) (r := 2 * (j + 1))
    (by omega) rfl (isWeightFamily_thetaBlock (t := t) (-1)) (((j + 1) * (3 * j + 2) : ℕ) : ℤ)
  have h := ((isWeightFamily_cpow t h1 (j + 1)).conv_hasSum h2 u).tsum_eq
  change (∑' n : ℤ, invLevelFam t j n * (u : K) ^ n) = _ at h
  rw [h, tsum_cpow t h1,
    (hasSum_pullCoef (isWeightFamily_thetaBlock (t := tatePow t (j + 1) (Nat.succ_pos j)) (-1))
      (by omega : 0 < 2 * (j + 1)) 0 u).tsum_eq,
    (hasSum_pullCoef (isWeightFamily_thetaBlock (t := t) (-1))
      (by omega : 0 < 2 * (j + 1)) _ u).tsum_eq, tsum_thetaBlock, tsum_thetaBlock]
  simp

/-- **The family of `F_N⁻¹·ΨSq_{2N}`**: `u^{-(3N²-N)}·θ_{q^N}(-u^{2N})^N·θ_q(-u^{2N})` is a
weight-`8N²` family with the multiplier of `θ(-u)^{8N²}` (stated with the exponent cleared). -/
theorem exists_invLevelFam (t : TateParameter K) (N : ℕ) (hN : 0 < N) :
    ∃ F₁ : ℤ → K, t.IsWeightFamily (8 * N * N) (multθ t ^ (8 * N * N)) F₁ ∧
      ∀ u : Kˣ, (∑' n : ℤ, F₁ n * (u : K) ^ n) * (u : K) ^ (3 * N * N) =
        (tatePow t N hN).theta (-(u ^ (2 * N))) ^ N * t.theta (-(u ^ (2 * N))) *
          (u : K) ^ N := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  refine ⟨invLevelFam t j, isWeightFamily_invLevelFam t j, fun u => ?_⟩
  rw [tsum_invLevelFam, zpow_neg, zpow_natCast]
  have hu : (u : K) ≠ 0 := u.ne_zero
  field_simp
  ring

/-- **The family of `F_N·ΨSq_{2N}^N`** (`N` even): with the division
`θ_q(-w) = θ_{q^N}(-w)·C(u)` (`w = u^{2N}`), the function
`u^{-(4N³-N²-N)}·θ_q(-w)^{N+1}·C(u)^N` is a weight-`8N³` family with the multiplier of
`θ(-u)^{8N³}` (stated with the exponent cleared). -/
theorem exists_levelFam [CharZero K] (t : TateParameter K) (N : ℕ) (hN : 0 < N)
    (hev : Even N) :
    ∃ (F₂ : ℤ → K) (C : Kˣ → K),
      t.IsWeightFamily (8 * N * N * N) (multθ t ^ (8 * N * N * N)) F₂ ∧
      (∀ u : Kˣ, t.theta (-(u ^ (2 * N))) = (tatePow t N hN).theta (-(u ^ (2 * N))) * C u) ∧
      ∀ u : Kˣ, (∑' n : ℤ, F₂ n * (u : K) ^ n) * (u : K) ^ (4 * N * N * N) =
        t.theta (-(u ^ (2 * N))) ^ (N + 1) * C u ^ N * (u : K) ^ (N * N + N) := by
  obtain ⟨i, rfl⟩ : ∃ i, N = 2 * (i + 1) := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  set T' := tatePow t (2 * (i + 1)) hN with hT'
  obtain ⟨A, c, hc, hA, hdiv⟩ := exists_theta_pull_div t T' (m := 1) (r := 2 * (i + 1)) one_pos
    hev hN (by rw [hT', tatePow_q, pow_one])
  have hA' : A = (T'.q * (-1)) * ((T'.q ^ (0 : ℤ))⁻¹ * (t.q * (-1))⁻¹ ^ (2 * (i + 1)) *
      (t.q ^ (1 * (2 * (i + 1)).choose 2))⁻¹) := by rw [← hA]; group
  have h1 := isWeightFamily_pullIter (T₁ := t) (T₂ := t) (m := 2 * (2 * (i + 1)))
    (r := 2 * (2 * (i + 1))) (by omega) rfl (isWeightFamily_thetaBlock (t := t) (-1)) 0
  have hC := isWeightFamily_pullIter (T₁ := T') (T₂ := t) (m := 2 * (2 * (i + 1))) (r := 2)
    (by omega) (by rw [hT', tatePow_q, ← pow_mul, mul_comm]) hc 0
  have hP := (isWeightFamily_cpow t h1 (2 * (i + 1) + 1)).conv
    (isWeightFamily_cpow t hC (2 * (i + 1)))
  set a : ℤ := ((2 * (i + 1) * (16 * i * i + 30 * i + 13) : ℕ) : ℤ) with ha
  have h := isWeightFamily_pullIter (T₁ := t) (T₂ := t) one_pos rfl hP a
  have hc2 : (2 * (2 * (i + 1))).choose 2 = 2 * (i + 1) * (4 * i + 3) := by
    rw [Nat.choose_two_right]
    refine Nat.div_eq_of_eq_mul_left two_pos ?_
    rw [show 2 * (2 * (i + 1)) - 1 = 4 * i + 3 by omega]
    ring
  have hk1 : 2 * (i + 1) * 1 - 1 = 2 * i + 1 := by omega
  refine ⟨pullCoef (fun n => ∑' m : ℤ,
      cpow (pullCoef (t.thetaBlock (-1)) (2 * (2 * (i + 1))) 0) (2 * (i + 1) + 1) (n - m) *
        cpow (pullCoef c (2 * (2 * (i + 1))) 0) (2 * (i + 1)) m) 1 a,
    fun u => ∑' n : ℤ, c n * ((u ^ (2 * (2 * (i + 1))) : Kˣ) : K) ^ n, ?_, fun u => ?_, fun u => ?_⟩
  · convert h using 1
    · rw [hk1]; ring
    · rw [hA', hc2, choose_two_even i, hk1, show Nat.choose 1 2 = 0 from rfl,
        show Nat.choose 2 2 = 1 from rfl, hT', tatePow_q, ha]
      ext
      have hq0 : (t.q : K) ≠ 0 := t.q.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        Units.val_neg, zpow_natCast, zpow_zero, multθ, mul_neg_one, pow_mul, inv_pow, neg_sq,
        one_mul, inv_one, mul_one, mul_zero, pow_zero]
      field_simp
      ring_nf
      simp only [inv_pow]
      field_simp
      ring
  · have := hdiv (u ^ (2 * (2 * (i + 1))))
    rwa [pow_one] at this
  · have e := (hasSum_pullCoef hP one_pos a u).tsum_eq
    have e2 := ((isWeightFamily_cpow t h1 (2 * (i + 1) + 1)).conv_hasSum
      (isWeightFamily_cpow t hC (2 * (i + 1))) (u ^ 1)).tsum_eq
    rw [e2, tsum_cpow t h1, tsum_cpow t hC,
      (hasSum_pullCoef (isWeightFamily_thetaBlock (t := t) (-1)) (by omega) 0 (u ^ 1)).tsum_eq,
      tsum_thetaBlock, (hasSum_pullCoef hc (by omega) 0 (u ^ 1)).tsum_eq] at e
    rw [e, zpow_neg, ha, zpow_natCast]
    simp only [pow_one, neg_zero, zpow_zero, one_mul, neg_one_mul]
    have hu : (u : K) ≠ 0 := u.ne_zero
    field_simp
    ring

end Families

section Unit

variable {K : Type u} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]
  {t : TateParameter K}

/-- `exists_ΨSq_theta` for `m = 2N`, with the exponent cleared:
`θ(-u^{2N})²·u^{2N} = α·ΨSq_{2N}(X(u))·θ(-u)^{8N²}·u^{4N²}`. -/
theorem exists_ΨSq_theta_two_mul (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) (N : ℕ)
    (hN : 0 < N) :
    ∃ α : K, α ≠ 0 ∧ ∀ u : Kˣ, OffOrbit t u →
      t.theta (-(u ^ (2 * N))) ^ 2 * (u : K) ^ (2 * N) =
        α * (t.tateCurve.ΨSq ((2 * N : ℕ) : ℤ)).eval (t.X u) * t.theta (-u) ^ (8 * N * N) *
          (u : K) ^ (4 * N * N) := by
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 1 := ⟨N - 1, by omega⟩
  obtain ⟨α, hα, h⟩ := exists_ΨSq_theta t h2 h12 j
  refine ⟨α, hα, fun u hu => ?_⟩
  have e := h u hu
  rw [zpow_neg, zpow_natCast, inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ u.ne_zero)] at e
  rw [e]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem offOrbit_tatePow {N : ℕ} (hN : 0 < N) {v : Kˣ} (h : OffOrbit t v) :
    OffOrbit (tatePow t N hN) v := fun n hn => h (N * n) (by
  rwa [tatePow_q, Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul] at hn)

omit [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem pow_sq_eq {M : Type*} [Monoid M] (u : M) (N : ℕ) : (u ^ N) ^ 2 = u ^ (2 * N) := by
  rw [← pow_mul, mul_comm]

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- Points of `Ÿ'_N` over `u` with `u^{2N} ∉ qᶻ` are off the period orbit of `Q = s^N`. -/
theorem offOrbit_sqrt_pow {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (T : TateParameter K)
    (hT : T.q = s ^ N) {u : Kˣ} (h : OffOrbit t (u ^ (2 * N))) : OffOrbit T (u ^ N) := by
  intro k hk
  apply h (N * k)
  have hsq := congrArg (· ^ 2) hk
  simp only [one_pow, mul_pow] at hsq
  have e1 : ((T.q : K) ^ k) ^ 2 = (t.q : K) ^ ((N : ℤ) * k) := by
    rw [hT, ← hs, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← zpow_natCast (s : K) N,
      ← zpow_mul, ← zpow_natCast _ 2, ← zpow_mul, ← zpow_natCast (s : K) 2, ← zpow_mul]
    ring_nf
  have e2 : (((u ^ N : Kˣ) : K)) ^ 2 = ((u ^ (2 * N) : Kˣ) : K) := by
    rw [← Units.val_pow_eq_pow_val, pow_sq_eq]
  rw [← e1, ← e2]
  exact hsq

omit [CharZero K] in
theorem etaleTheta_pow_ne_zero {N : ℕ} {u : Kˣ} (h : OffOrbit t (u ^ (2 * N))) :
    etaleTheta t (u ^ N) ≠ 0 := by
  rw [etaleTheta_def, pow_sq_eq]
  exact mul_ne_zero (u ^ N).ne_zero (theta_neg_ne_zero t h)

omit [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
theorem thetaLevel_pow_eq (N : ℕ) (hN : 0 < N) (u : Kˣ) :
    thetaLevel t N hN (u ^ N) = (u : K) ^ N * t.theta (-(u ^ (2 * N))) /
      ((u : K) ^ N * (tatePow t N hN).theta (-(u ^ (2 * N)))) ^ N := by
  rw [thetaLevel, etaleTheta_def, etaleTheta_def, pow_sq_eq, Units.val_pow_eq_pow_val]

omit [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- The field identity behind `F_N = α^{-N}(P₂ + yQ₂)/ψ_{2N}^{2N}`. -/
theorem level_identity {L : Type*} [Field L] {N : ℕ} {y a bb θ Ψ V S c α : L} (hy : y ≠ 0)
    (ha : a ≠ 0) (hb : bb ≠ 0) (hθ : θ ≠ 0) (hΨ0 : Ψ ≠ 0)
    (hv : S = V * θ ^ (8 * N * N * N))
    (he : S * y ^ (4 * N * N * N) = a ^ (N + 1) * c ^ N * y ^ (N * N + N))
    (hd : a = bb * c) (hΨ : a ^ 2 * y ^ (2 * N) = α * Ψ * θ ^ (8 * N * N) * y ^ (4 * N * N)) :
    (α ^ N)⁻¹ * V * (Ψ ^ N)⁻¹ = y ^ N * a / (y ^ N * bb) ^ N := by
  have hΨN := congrArg (· ^ N) hΨ
  have hdN := congrArg (· ^ N) hd
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul, zero_mul] at hΨ
    exact mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hy) hΨ
  have G : V * (y ^ N * bb) ^ N * (θ ^ (8 * N * N * N) * y ^ (4 * N * N * N)) =
      α ^ N * Ψ ^ N * (y ^ N * a) * (θ ^ (8 * N * N * N) * y ^ (4 * N * N * N)) := by
    linear_combination (-(y ^ N * bb) ^ N * y ^ (4 * N * N * N)) * hv +
      (y ^ N * bb) ^ N * he - y ^ (2 * N * N + N) * a ^ (N + 1) * hdN + y ^ N * a * hΨN
  have G' := mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ hθ) (pow_ne_zero _ hy)) G
  field_simp
  linear_combination G'

omit [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K] in
/-- The field identity behind `F_N⁻¹ = α⁻¹(P₁ + yQ₁)/ψ_{2N}²`. -/
theorem level_identity_inv {L : Type*} [Field L] {N : ℕ} {y a bb θ Ψ V S α : L} (hy : y ≠ 0)
    (ha : a ≠ 0) (hθ : θ ≠ 0) (hΨ0 : Ψ ≠ 0)
    (hv : S = V * θ ^ (8 * N * N))
    (he : S * y ^ (3 * N * N) = bb ^ N * a * y ^ N)
    (hΨ : a ^ 2 * y ^ (2 * N) = α * Ψ * θ ^ (8 * N * N) * y ^ (4 * N * N)) :
    α⁻¹ * V * Ψ⁻¹ = (y ^ N * a / (y ^ N * bb) ^ N)⁻¹ := by
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul, zero_mul] at hΨ
    exact mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hy) hΨ
  have G : V * (y ^ N * a) * (θ ^ (8 * N * N) * y ^ (3 * N * N)) =
      α * Ψ * (y ^ N * bb) ^ N * (θ ^ (8 * N * N) * y ^ (3 * N * N)) := by
    linear_combination (-(y ^ N * a * y ^ (3 * N * N))) * hv + y ^ N * a * he + bb ^ N * hΨ
  have G' := mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ hθ) (pow_ne_zero _ hy)) G
  field_simp
  linear_combination G'

/-- **G1, step 3: the theta level function `F_N` is a unit on `Ÿ'_N`.** In the setting of
`exists_thetaLevel_etale`, `F_N` and `F_N⁻¹` lie in `K[E][1/ψ_{2N}]`; at every Tate point `u`
with `ψ_{2N}(u) ≠ 0`, `F_N` has the value `f_N(u^N) ≠ 0`, and `Θ̈(u^N) ≠ 0`. -/
theorem exists_thetaLevel_unit (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {s : Kˣ}
    (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (T : TateParameter K) (hT : T.q = s ^ N)
    (hev : Even N) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    haveI : NeZero (2 * N) := ⟨by omega⟩
    ∃ (gX gY F : TateField t),
      (∃ h₁ : (hemiData t.tateCurve).L ≤ IntermediateField.adjoin
          (K₀ K (coordT (xN t.tateCurve))) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}),
        (ringMap (coordT (xN t.tateCurve)) h₁).toRingHom.Etale) ∧
      mulByNEmb t.tateCurve (2 * N) F ∈ IntermediateField.adjoin
          (K₀ K (coordT (xN t.tateCurve))) (mulByNEmb t.tateCurve (2 * N) '' {gX, gY}) ∧
      (∃ b b' : coverRingN t.tateCurve (2 * N),
        algebraMap _ (TateField t) b = F ∧ algebraMap _ (TateField t) b' = F⁻¹) ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u),
        evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 →
          OffOrbit t (u ^ (2 * N)) ∧ etaleTheta t (u ^ N) ≠ 0 ∧
          thetaLevel t N hN (u ^ N) ≠ 0 ∧ HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  haveI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨gX, gY, F, D, -, -, het, hFL, hspec⟩ := exists_thetaLevel_etale h2 h12 hs hN T hT hev
  have pt : ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu (psiN t.tateCurve (2 * N)) ≠ 0 →
        OffOrbit t (u ^ (2 * N)) ∧ etaleTheta t (u ^ N) ≠ 0 ∧
        thetaLevel t N hN (u ^ N) ≠ 0 ∧ HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)) ∧
        evalTate t h12 hu (psiN t.tateCurve (2 * N)) ^ 2 =
          (t.tateCurve.ΨSq ((2 * N : ℕ) : ℤ)).eval (t.X u) := by
    intro u hu hψ
    obtain ⟨hum, -⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu hψ
    have hU := etaleTheta_pow_ne_zero hum
    have hU' : etaleTheta (tatePow t N hN) (u ^ N) ≠ 0 :=
      etaleTheta_pow_ne_zero (offOrbit_tatePow hN hum)
    have hT0 : T.theta (-(u ^ N)) ≠ 0 := theta_neg_ne_zero T (offOrbit_sqrt_pow hs T hT hum)
    refine ⟨hum, hU, thetaLevel_ne_zero t N hN hU, ((hspec u hu).2 hT0).2.2 hU', ?_⟩
    rw [show evalTate t h12 hu (psiN t.tateCurve (2 * N)) =
      (t.tateCurve.ψ ((2 * N : ℕ) : ℤ)).evalEval (t.X u) (t.Y u) from evalTate_mkT hu _]
    exact ψ_sq_evalEval (t.tatePoint_mem' h12 hu) _
  obtain ⟨α, hα, hΨ⟩ := exists_ΨSq_theta_two_mul (t := t) h2 h12 N hN
  obtain ⟨F₁, hF₁, e₁⟩ := exists_invLevelFam t N hN
  obtain ⟨P₁, Q₁, v₁⟩ := exists_poly_of_isWeightFamily t h12 (by positivity) hF₁
  obtain ⟨F₂, C, hF₂, hdiv, e₂⟩ := exists_levelFam t N hN hev
  obtain ⟨P₂, Q₂, v₂⟩ := exists_poly_of_isWeightFamily t h12 (by positivity) hF₂
  have hD₀ := psiN_ne_zero_of_neZero t.tateCurve (2 * N)
  refine ⟨gX, gY, F, het, hFL,
    ⟨algebraMap _ _ (algebraMap K (TateRing t) (α ^ N)⁻¹ * polyXY t P₂ Q₂) *
      invPsiNB t.tateCurve (2 * N) ^ (2 * N),
     algebraMap _ _ (algebraMap K (TateRing t) α⁻¹ * polyXY t P₁ Q₁) *
      invPsiNB t.tateCurve (2 * N) ^ 2, ?_, ?_⟩,
    fun u hu hψ => ?_⟩
  · refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => thetaLevel t N hN (u ^ N))
      (fun u hu hψ => ?_) (fun u hu hψ => (pt u hu hψ).2.2.2.1)
    obtain ⟨hum, -, -, -, hsq⟩ := pt u hu hψ
    refine (hasTateValue_cover (2 * N) hu hψ _).congr ?_
    simp only [map_mul, map_pow, evalCover_algebraMap, evalCover_invPsiNB, evalTate_algebraMap,
      evalTate_polyXY]
    rw [thetaLevel_pow_eq, inv_pow, pow_mul, hsq]
    exact level_identity u.ne_zero (theta_neg_ne_zero t hum)
      (theta_neg_ne_zero _ (offOrbit_tatePow hN hum)) (theta_neg_ne_zero t hu)
      (by rw [← hsq]; exact pow_ne_zero _ hψ) (v₂ u hu) (e₂ u) (hdiv u) (hΨ u hu)
  · refine eq_of_hasTateValue (h12 := h12) hD₀ (G := fun u => (thetaLevel t N hN (u ^ N))⁻¹)
      (fun u hu hψ => ?_) (fun u hu hψ => (pt u hu hψ).2.2.2.1.inv (pt u hu hψ).2.2.1)
    obtain ⟨hum, -, -, -, hsq⟩ := pt u hu hψ
    refine (hasTateValue_cover (2 * N) hu hψ _).congr ?_
    simp only [map_mul, map_pow, evalCover_algebraMap, evalCover_invPsiNB, evalTate_algebraMap,
      evalTate_polyXY]
    rw [thetaLevel_pow_eq, inv_pow, hsq]
    exact level_identity_inv u.ne_zero (theta_neg_ne_zero t hum) (theta_neg_ne_zero t hu)
      (by rw [← hsq]; exact pow_ne_zero _ hψ) (v₁ u hu) (e₁ u) (hΨ u hu)
  · obtain ⟨hum, hU, hl, hv, -⟩ := pt u hu hψ
    exact ⟨hum, hU, hl, hv⟩

end Unit

end Iut.EtaleTheta
