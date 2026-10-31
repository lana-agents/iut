/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaTranslate
import Iut.EtaleTheta.ThetaLevelRational
import Iut.EtaleTheta.ThetaIsogeny
import Iut.EtaleTheta.ThetaDivision
import Iut.EtaleTheta.ThetaLevelInversion
import EllipticCurves.FunctionField.PointClosedPoint
import EllipticCurves.FunctionField.PlaceOrder
import EllipticCurves.FunctionField.CoordinateRingNormalGeneral

/-!
# The orders of the theta level functions at the cusps (MR14, [EtTh] Prop. 1.4(i), finite level)

Stage 1: the elements of `K(E_Q)` (`Q = s^N`, `N` even) that the order computation uses, with their
values at Tate points and the degree bounds of Tate's theorem.

* `evalTate_eq_evalEvalHom`, `ptT`: the closed point of a Tate point; `ord_pos_of_evalTate_eq_zero`,
  `ord_eq_zero_of_evalTate_ne_zero`.
* `exists_poly_thetaLevel_deg`, `exists_poly_thetaSq_deg`, `exists_poly_isogenyX_deg`: Tate's
  theorem with degree bounds for `Θ̈_q`, `Θ̈_{q^N}^N`, `Θ̈_{q^N}^2` and `X_q(Ü²)`.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

section Points

variable {T : TateParameter K} {h12 : (12 : K) ≠ 0} [T.tateCurve.IsElliptic]

omit [T.tateCurve.IsElliptic] in
/-- Evaluation at a Tate point is `elliptic-curves`' evaluation at the point `(X(u), Y(u))`. -/
theorem evalTate_eq_evalEvalHom {u : Kˣ} (hu : OffOrbit T u) :
    evalTate T h12 hu = evalEvalHom (tateEquation h12 hu) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
  exact (evalTate_mkT hu p).trans (evalEvalHom_mk _ p).symm

variable (h12) in
/-- The closed point of `E_T` at the Tate point of `u`. -/
abbrev ptT {u : Kˣ} (hu : OffOrbit T u) : ProjPoint T.tateCurve.toAffine :=
  some (pointClosedPoint (tateEquation h12 hu))

omit [T.tateCurve.IsElliptic] in
theorem mem_ptT_iff {u : Kˣ} (hu : OffOrbit T u) (a : TateRing T) :
    a ∈ (pointClosedPoint (tateEquation h12 hu)).asIdeal ↔ evalTate T h12 hu a = 0 := by
  rw [pointClosedPoint_asIdeal, ← ker_evalEvalHom, RingHom.mem_ker, evalTate_eq_evalEvalHom]

theorem ord_pos_of_evalTate_eq_zero {u : Kˣ} (hu : OffOrbit T u)
    {a : TateRing T} (ha : a ≠ 0) (h0 : evalTate T h12 hu a = 0) :
    0 < divisorProj _ (algebraMap (TateRing T) (TateField T) a) (ptT h12 hu) := by
  rw [divisorProj_apply_some]
  set v := pointClosedPoint (tateEquation h12 hu)
  have hmem : a ∈ v.asIdeal := (mem_ptT_iff hu a).mpr h0
  rw [HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := TateField T),
    ValuationSubring.mem_nonunits_iff_or] at hmem
  rcases hmem with h | h
  · exact absurd h (by simpa using ha)
  · by_contra hc
    exact h ((mem_valuationSubringAtPrime_iff_ord_nonneg v
      (inv_ne_zero (by simpa using ha))).2 (by rw [ord_inv]; omega))

theorem ord_eq_zero_of_evalTate_ne_zero {u : Kˣ} (hu : OffOrbit T u)
    {a : TateRing T} (h0 : evalTate T h12 hu a ≠ 0) :
    divisorProj _ (algebraMap (TateRing T) (TateField T) a) (ptT h12 hu) = 0 := by
  rw [divisorProj_apply_some]
  set v := pointClosedPoint (tateEquation h12 hu)
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have hnot : a ∉ v.asIdeal := fun h => h0 ((mem_ptT_iff hu a).mp h)
  have hnn : 0 ≤ ord v (algebraMap (TateRing T) (TateField T) a) :=
    (mem_valuationSubringAtPrime_iff_ord_nonneg v (by simpa using ha)).1
      (HeightOneSpectrum.algebraMap_mem_valuationSubringAtPrime v a)
  rw [HeightOneSpectrum.mem_asIdeal_iff_mem_nonunits (K := TateField T),
    ValuationSubring.mem_nonunits_iff_or] at hnot
  push Not at hnot
  have hinv := (mem_valuationSubringAtPrime_iff_ord_nonneg v
    (inv_ne_zero (by simpa using ha))).1 hnot.2
  rw [ord_inv] at hinv
  omega

end Points

section Poly

variable (t : TateParameter K) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
  (hN : 0 < N) (hev : Even N) (T : TateParameter K) (hT : T.q = s ^ N)

include h12 hs hev hT in
/-- `exists_poly_thetaLevel` with the degree bounds of Tate's theorem (weight `2N`). -/
theorem exists_poly_thetaLevel_deg :
    ∃ P₁ Q₁ P₂ Q₂ : Polynomial K,
      P₁.degree < ((2 * N) / 2 + 1 : ℕ) ∧ Q₁.degree < ((2 * N - 1) / 2 : ℕ) ∧
      P₂.degree < ((2 * N) / 2 + 1 : ℕ) ∧ Q₂.degree < ((2 * N - 1) / 2 : ℕ) ∧
      ∀ u : Kˣ, OffOrbit T u →
      etaleTheta t u = (P₁.eval (T.X u) + T.Y u * Q₁.eval (T.X u)) * (u : K) ^ N *
          T.theta (-u) ^ (2 * N) ∧
        etaleTheta (tatePow t N hN) u ^ N =
          (P₂.eval (T.X u) + T.Y u * Q₂.eval (T.X u)) * (u : K) ^ N * T.theta (-u) ^ (2 * N) := by
  have h2N : 0 < 2 * N := by omega
  have hA := multθ_pow_two_mul hev T
  obtain ⟨P₁, Q₁, d₁, d₁', h₁⟩ := exists_poly_of_isWeightFamily_deg T h12 h2N
    (hA ▸ isWeightFamily_oddShift t hs N T hT)
  obtain ⟨P₂, Q₂, d₂, d₂', h₂⟩ := exists_poly_of_isWeightFamily_deg T h12 h2N
    (hA ▸ isWeightFamily_oddShiftPow t hs N hN T hT)
  refine ⟨P₁, Q₁, P₂, Q₂, d₁, d₁', d₂, d₂', fun u hu => ⟨?_, ?_⟩⟩
  · have e := h₁ u hu
    rw [(hasSum_oddShift t N u).tsum_eq, zpow_neg, zpow_natCast] at e
    have hu0 : (u : K) ^ N ≠ 0 := pow_ne_zero _ u.ne_zero
    field_simp at e
    rw [e]; ring
  · have e := h₂ u hu
    rw [tsum_oddShiftPow t N hN T hs hT, zpow_neg, zpow_natCast] at e
    have hu0 : (u : K) ^ N ≠ 0 := pow_ne_zero _ u.ne_zero
    field_simp at e
    rw [e]; ring

include h12 hs hT in
/-- **`Θ̈_{q^N}(Ü)²` in Tate coordinates of `E_Q`** (weight `4`):
`Θ̈_{q^N}(Ü)² = (P(X_Q) + Y_Q·Q(X_Q))·Ü²·θ_Q(-Ü)⁴`, with `deg P ≤ 2`, `deg Q ≤ 0`. -/
theorem exists_poly_thetaSq_deg :
    ∃ P Q : Polynomial K, P.degree < ((4 : ℕ) / 2 + 1 : ℕ) ∧ Q.degree < ((4 - 1) / 2 : ℕ) ∧
      ∀ u : Kˣ, OffOrbit T u →
        etaleTheta (tatePow t N hN) u ^ 2 =
          (P.eval (T.X u) + T.Y u * Q.eval (T.X u)) * (u : K) ^ 2 * T.theta (-u) ^ 4 := by
  have hs' : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  have h1 := isWeightFamily_oddShift (tatePow t N hN) hs' 1 T (by rw [hT, pow_one])
  rw [pow_one] at h1
  have h2 := isWeightFamily_cpow T h1 2
  rw [← multθ_pow_two_mul (even_two) T] at h2
  obtain ⟨P, Q, d, d', h⟩ := exists_poly_of_isWeightFamily_deg T h12 (by norm_num) h2
  refine ⟨P, Q, d, d', fun u hu => ?_⟩
  have e := h u hu
  rw [tsum_cpow T h1 u 2, (hasSum_oddShift _ 1 u).tsum_eq, mul_pow] at e
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  rw [zpow_neg, zpow_natCast, pow_one] at e
  field_simp at e
  rw [show (2 * 2 : ℕ) = 4 by norm_num] at e
  linear_combination e

include h12 hs hN hT in
/-- `exists_poly_isogenyX` with the degree bounds of Tate's theorem (weight `4N`):
`X_q(Ü²) = (P₁ + Y Q₁)/(P₂ + Y Q₂)` in Tate coordinates of `E_Q`. -/
theorem exists_poly_isogenyX_deg :
    ∃ P₁ Q₁ P₂ Q₂ : K[X],
      P₁.degree < ((2 * N * 2) / 2 + 1 : ℕ) ∧ Q₁.degree < ((2 * N * 2 - 1) / 2 : ℕ) ∧
      P₂.degree < ((2 * N * 2) / 2 + 1 : ℕ) ∧ Q₂.degree < ((2 * N * 2 - 1) / 2 : ℕ) ∧
      ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)) := by
  have hlat := isogeny_lattice t hs T hT
  have h1 := isWeightFamily_pullIter (m := 2) two_pos hlat (isWeightFamily_XThetaSq t)
    ((2 * N - 2 : ℕ) : ℤ)
  rw [isogenyMult_X t hs hN T hT] at h1
  have h2 := isWeightFamily_pullIter (m := 2) two_pos hlat
    (isWeightFamily_cpow t (isWeightFamily_thetaBlock (t := t) (-1)) 2) ((2 * N - 2 : ℕ) : ℤ)
  rw [one_mul, isogenyMult_X t hs hN T hT] at h2
  obtain ⟨P₁, Q₁, d₁, d₁', e₁⟩ := exists_poly_of_isWeightFamily_deg T h12 (by positivity) h1
  obtain ⟨P₂, Q₂, d₂, d₂', e₂⟩ := exists_poly_of_isWeightFamily_deg T h12 (by positivity) h2
  refine ⟨P₁, Q₁, P₂, Q₂, d₁, d₁', d₂, d₂', fun v hv hθ => ?_⟩
  have f₁ := e₁ v hv
  have f₂ := e₂ v hv
  rw [(hasSum_pullCoef (isWeightFamily_XThetaSq t) two_pos _ v).tsum_eq,
    (t.hasSum_XThetaSqCoeff (offOrbit_of_theta_ne_zero hθ)).tsum_eq] at f₁
  rw [tsum_pull_theta two_pos 2 v] at f₂
  have hv0 : (v : K) ^ (-((2 * N - 2 : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ v.ne_zero
  have hθT : T.theta (-v) ^ (2 * N * 2) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hv)
  have hden : P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at f₂
    exact mul_ne_zero hv0 (pow_ne_zero _ hθ) f₂
  refine ⟨hden, ?_⟩
  rw [eq_div_iff hden]
  apply mul_left_cancel₀ (mul_ne_zero hv0 (mul_ne_zero (pow_ne_zero 2 hθ) hθT))
  linear_combination
    (T.theta (-v) ^ (2 * N * 2) * (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v))) * f₁ -
    ((P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) * T.theta (-v) ^ (2 * N * 2)) * f₂

end Poly

end Iut.EtaleTheta
