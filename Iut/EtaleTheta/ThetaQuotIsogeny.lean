/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaIsogeny

/-!
# The cyclic isogeny `E_{Q^M} → E_Q`, `v ↦ v`, in Tate coordinates (MR14, level system)

Let `T, T'` be Tate parameters with `T'.q = T.q^M`. The identity of `Kˣ` induces the cyclic
isogeny `E_{T'} = Kˣ/T'.q^ℤ → E_T = Kˣ/T.q^ℤ` (kernel `T.q^ℤ/T'.q^ℤ ≅ ℤ/M`). It is algebraic:
`X_T(v)` and `Y_T(v)` are rational functions of `X_{T'}(v)`, `Y_{T'}(v)`
(`exists_poly_quotX`, `exists_poly_quotY`).

For the level system of the étale theta function (`MR14-plan.md`, run 5) this is the transition
map `Ÿ'_{NM} → Ÿ'_N` of the levels `Ÿ'_N = E_{s^N} ∖ C_N`: with `Q = s^N`, `Q^M = s^{NM}`.

The proof is the engine of `ThetaIsogeny.lean` with `m = 1`: a weight-`k` family `c` for `T` gives
the weight-`kM` family `v ↦ v^{-a}·∑ c(n) vⁿ` for `T'` (`isWeightFamily_pullIter`), with the
multiplier of `θ_{T'}(-v)^{kM}` for `k = 2j`, `a = j(M-1)` (`quotMult`). For `Y` we use the
weight-`4` family `Y·θ⁴` (a convolution), since `a = 3(M-1)/2` is not an integer for even `M`.
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- The multiplier identity for the quotient isogeny (`k = 2j`, `a = j(M-1)`). -/
theorem quotMult {T T' : TateParameter K} {M : ℕ} (hM0 : 0 < M) (hM : T'.q = T.q ^ M) (j : ℕ) :
    (T'.q ^ ((j * (M - 1) : ℕ) : ℤ))⁻¹ * ((T.q * (-1))⁻¹ ^ (2 * j)) ^ M *
        (T.q ^ (2 * j * M.choose 2))⁻¹ = multθ T' ^ (2 * j * M * 1) := by
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have hC : 2 * j * (M + 1).choose 2 = j * ((M + 1) * M) := by
    rw [mul_comm 2 j, mul_assoc, two_mul_choose_two]
  rw [hC, show M + 1 - 1 = M by omega, hM]
  ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, zpow_natCast, multθ]
  have hq : (T.q : K) ≠ 0 := T.q.ne_zero
  have hT' : (T'.q : K) = (T.q : K) ^ (M + 1) := by rw [hM, Units.val_pow_eq_pow_val]
  have e1 : ((-1 : K)) ^ (2 * j) = 1 := Even.neg_one_pow ⟨j, two_mul j⟩
  have e3 : ((-1 : K)) ^ (2 * j * (M + 1)) = 1 := Even.neg_one_pow ⟨j * (M + 1), by ring⟩
  rw [hT']
  simp only [inv_pow, mul_pow, e1, e3, mul_one]
  field_simp
  ring

/-- **The engine for `E_{T'} → E_T`** (`T'.q = T.q^M`): two weight-`k` families for `T` with the
same multiplier give, after the shift `v^{-a}`, weight-`kM` families for `T'` with values
`(P + Y·Q)(X_{T'}(v), Y_{T'}(v))·θ_{T'}(-v)^{kM}`. -/
theorem exists_poly_quot {T T' : TateParameter K} {M : ℕ} (hM : T'.q ^ 1 = T.q ^ M)
    (h12 : (12 : K) ≠ 0) {k : ℕ} (hk : 0 < k) (hM0 : 0 < M) {A : Kˣ} {c₁ c₂ : ℤ → K}
    (h₁ : T.IsWeightFamily k A c₁) (h₂ : T.IsWeightFamily k A c₂) (a : ℤ)
    (hmult : (T'.q ^ a)⁻¹ * A ^ M * (T.q ^ (k * M.choose 2))⁻¹ = multθ T' ^ (k * M * 1)) :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T' v →
      (v : K) ^ (-a) * ∑' n : ℤ, c₁ n * (v : K) ^ n =
        (P₁.eval (T'.X v) + T'.Y v * Q₁.eval (T'.X v)) * T'.theta (-v) ^ (k * M * 1) ∧
      (v : K) ^ (-a) * ∑' n : ℤ, c₂ n * (v : K) ^ n =
        (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v)) * T'.theta (-v) ^ (k * M * 1) := by
  have g₁ := isWeightFamily_pullIter (m := 1) one_pos hM h₁ a
  have g₂ := isWeightFamily_pullIter (m := 1) one_pos hM h₂ a
  rw [hmult] at g₁ g₂
  obtain ⟨P₁, Q₁, e₁⟩ := exists_poly_of_isWeightFamily T' h12 (by positivity) g₁
  obtain ⟨P₂, Q₂, e₂⟩ := exists_poly_of_isWeightFamily T' h12 (by positivity) g₂
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv => ⟨?_, ?_⟩⟩
  · rw [← e₁ v hv, (hasSum_pullCoef h₁ one_pos a v).tsum_eq, pow_one]
  · rw [← e₂ v hv, (hasSum_pullCoef h₂ one_pos a v).tsum_eq, pow_one]

omit [NormedField K] [CompleteSpace K] [IsUltrametricDist K] in
/-- The quotient of two series from their engine expressions. -/
theorem ratio_of_engine {L : Type*} [Field L] {S₁ S₂ R₁ R₂ θ w : L} (hw : w ≠ 0) (hθ : θ ≠ 0)
    (e₁ : w * S₁ = R₁ * θ) (e₂ : w * S₂ = R₂ * θ) :
    (R₂ ≠ 0 ↔ S₂ ≠ 0) ∧ (S₂ ≠ 0 → S₁ / S₂ = R₁ / R₂) := by
  have key : R₂ ≠ 0 ↔ S₂ ≠ 0 := by
    constructor
    · intro h hS; rw [hS, mul_zero] at e₂; exact mul_ne_zero h hθ e₂.symm
    · intro h hR; rw [hR, zero_mul] at e₂; exact mul_ne_zero hw h e₂
  refine ⟨key, fun h => ?_⟩
  rw [div_eq_div_iff h (key.mpr h)]
  apply mul_left_cancel₀ hw
  linear_combination R₂ * e₁ - R₁ * e₂

/-- **`X_T(v)` is a rational function of `X_{T'}(v)`, `Y_{T'}(v)`** for `T'.q = T.q^M`; the
denominator vanishes exactly where `θ_T(-v) = 0`. -/
theorem exists_poly_quotX {T T' : TateParameter K} {M : ℕ} (hM0 : 0 < M) (hM : T'.q = T.q ^ M)
    (h12 : (12 : K) ≠ 0) :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T' v →
      (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v) ≠ 0 ↔ T.theta (-v) ≠ 0) ∧
      (T.theta (-v) ≠ 0 → T.X v = (P₁.eval (T'.X v) + T'.Y v * Q₁.eval (T'.X v)) /
        (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v))) := by
  have h₂ := isWeightFamily_cpow T (isWeightFamily_thetaBlock (t := T) (-1)) 2
  rw [one_mul] at h₂
  have hm := quotMult hM0 hM 1
  rw [mul_one] at hm
  obtain ⟨P₁, Q₁, P₂, Q₂, h⟩ := exists_poly_quot (by rw [pow_one, hM]) h12 two_pos hM0
    (isWeightFamily_XThetaSq T) h₂ _ hm
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv => ?_⟩
  obtain ⟨e₁, e₂⟩ := h v hv
  have hS₂ : (∑' n : ℤ, cpow (T.thetaBlock (-1)) 2 n * (v : K) ^ n) = T.theta (-v) ^ 2 := by
    rw [tsum_cpow T (isWeightFamily_thetaBlock (t := T) (-1)), tsum_thetaBlock, neg_one_mul]
  obtain ⟨hiff, hval⟩ := ratio_of_engine (zpow_ne_zero _ v.ne_zero)
    (pow_ne_zero _ (theta_neg_ne_zero T' hv)) e₁ e₂
  rw [hS₂] at hiff hval
  refine ⟨hiff.trans (pow_ne_zero_iff two_ne_zero), fun h0 => ?_⟩
  rw [← hval (pow_ne_zero _ h0), (T.hasSum_XThetaSqCoeff (offOrbit_of_theta_ne_zero h0)).tsum_eq]
  field_simp

/-- **`Y_T(v)` is a rational function of `X_{T'}(v)`, `Y_{T'}(v)`** for `T'.q = T.q^M` (via the
weight-`4` family `Y·θ⁴`). -/
theorem exists_poly_quotY {T T' : TateParameter K} {M : ℕ} (hM0 : 0 < M) (hM : T'.q = T.q ^ M)
    (h12 : (12 : K) ≠ 0) :
    ∃ P₁ Q₁ P₂ Q₂ : K[X], ∀ v : Kˣ, OffOrbit T' v →
      (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v) ≠ 0 ↔ T.theta (-v) ≠ 0) ∧
      (T.theta (-v) ≠ 0 → T.Y v = (P₁.eval (T'.X v) + T'.Y v * Q₁.eval (T'.X v)) /
        (P₂.eval (T'.X v) + T'.Y v * Q₂.eval (T'.X v))) := by
  have h₁ := (isWeightFamily_YThetaCube T).conv (isWeightFamily_thetaBlock (t := T) (-1))
  rw [← pow_succ] at h₁
  have h₁' := weightFamily_of_eq T h₁ (show 3 + 1 = 2 * 2 by rfl)
  have h₂ := isWeightFamily_cpow T (isWeightFamily_thetaBlock (t := T) (-1)) 4
  rw [one_mul] at h₂
  have h₂' := weightFamily_of_eq T h₂ (show 4 = 2 * 2 by rfl)
  have hm := quotMult hM0 hM 2
  obtain ⟨P₁, Q₁, P₂, Q₂, h⟩ := exists_poly_quot (by rw [pow_one, hM]) h12 (by norm_num) hM0
    h₁' h₂' _ hm
  refine ⟨P₁, Q₁, P₂, Q₂, fun v hv => ?_⟩
  obtain ⟨e₁, e₂⟩ := h v hv
  have hS₂ : (∑' n : ℤ, cpow (T.thetaBlock (-1)) 4 n * (v : K) ^ n) = T.theta (-v) ^ 4 := by
    rw [tsum_cpow T (isWeightFamily_thetaBlock (t := T) (-1)), tsum_thetaBlock, neg_one_mul]
  obtain ⟨hiff, hval⟩ := ratio_of_engine (zpow_ne_zero _ v.ne_zero)
    (pow_ne_zero _ (theta_neg_ne_zero T' hv)) e₁ e₂
  rw [hS₂] at hiff hval
  refine ⟨hiff.trans (pow_ne_zero_iff four_ne_zero), fun h0 => ?_⟩
  rw [← hval (pow_ne_zero _ h0), ((isWeightFamily_YThetaCube T).conv_hasSum
    (isWeightFamily_thetaBlock (t := T) (-1)) v).tsum_eq,
    (T.hasSum_YThetaCubeCoeff (offOrbit_of_theta_ne_zero h0)).tsum_eq, tsum_thetaBlock,
    neg_one_mul]
  field_simp

end Iut.EtaleTheta
