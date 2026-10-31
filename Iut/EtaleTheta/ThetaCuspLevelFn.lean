/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCuspOrder
import Iut.EtaleTheta.CurveDivisorAux
import EllipticCurves.FunctionField.TranslationPlaceAtInfinity

/-!
# The cusp data of the theta level function `f = num / den` on `E_Q`

For the polynomials of `exists_poly_thetaLevel_deg` and `exists_poly_thetaSq_deg`
(`Q = s^N`, `N` even), `f = num / den ∈ K(E_Q)` has the values `Θ̈_q / Θ̈_{q^N}^N`. Here:

* `cusp_ne_zero`, `cusp_deg_num_le`: `num, den, f ≠ 0` and `deg num ≤ 2N`;
* `cusp_negT`, `cusp_ordInfty_odd`: `[-1]^* f = -f`, so `f` has odd order at infinity;
* `cusp_transT`, `cusp_divisorProj_neg_one`: translation by the `2`-torsion point of `-1` negates
  `f`, so the orders of `f` at that point and at infinity agree;
* `cusp_ordInfty_ge`: `-N ≤ ord_∞ f` (`den = g^{N/2}`, `g` outside the field of constants);
* `cusp_one_le_divisorProj`: `f` vanishes at the Tate points `±s^a`, `0 < a < N`;
* `exists_thetaLevel_cuspData`: everything for the polynomials of `exists_poly_thetaLevel_deg`.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

section Aux

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem eq_zero_of_norm_zpow {x : K} (h0 : x ≠ 0) (h1 : ‖x‖ < 1) {k : ℤ} (h : ‖x‖ ^ k = 1) :
    k = 0 :=
  zpow_right_injective₀ (norm_pos_iff.mpr h0) h1.ne (h.trans (zpow_zero _).symm)

/-- `Θ̈` does not vanish at a point of norm one whose square is not `1`. -/
theorem etaleTheta_ne_zero_of_norm (t : TateParameter K) {u : Kˣ} (hu : ‖(u : K)‖ = 1)
    (h1 : (u : K) ^ 2 ≠ 1) : etaleTheta t u ≠ 0 := by
  rw [Ne, etaleTheta_eq_zero_iff]
  rintro ⟨k, hk⟩
  exact h1 (eq_of_eq_q_zpow_mul t (a := (u : K) ^ 2) (b := 1)
    (by rw [norm_pow, hu, one_pow]) norm_one (by rw [hk, mul_one]))

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem two_ne_zero_of_norm (h2 : ‖(2 : K)‖ = 1) : (2 : K) ≠ 0 := fun h => by
  rw [h, norm_zero] at h2; exact zero_ne_one h2

/-- The unit `2`. -/
abbrev twoU (h2 : ‖(2 : K)‖ = 1) : Kˣ := Units.mk0 2 (two_ne_zero_of_norm h2)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_twoU (T : TateParameter K) (h2 : ‖(2 : K)‖ = 1) : OffOrbit T (twoU h2) :=
  offOrbit_of_norm h2 (by
    intro h
    have h' : (2 : K) = 1 := h
    have : (1 : K) = 0 := by linear_combination h'
    exact one_ne_zero this)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem offOrbit_neg_one (T : TateParameter K) (h2 : ‖(2 : K)‖ = 1) : OffOrbit T (-1) :=
  offOrbit_of_norm (by simp) (by
    intro h
    apply two_ne_zero_of_norm h2
    have h' : (-1 : K) = 1 := by simpa using h
    linear_combination -h')

theorem etaleTheta_twoU_ne_zero (t : TateParameter K) {h12 : (12 : K) ≠ 0}
    (h2 : ‖(2 : K)‖ = 1) : etaleTheta t (twoU h2) ≠ 0 :=
  etaleTheta_ne_zero_of_norm t h2 (fun h => h12 (by
    have h' : (2 : K) ^ 2 = 1 := by simpa using h
    linear_combination 4 * h'))

end Aux

section Cusp

variable {t T : TateParameter K} {h12 : (12 : K) ≠ 0} {s : Kˣ} {N : ℕ} {hN : 0 < N}
  [T.tateCurve.IsElliptic] {P₁ Q₁ P₂ Q₂ P Q : K[X]}

/-- The identities of `exists_poly_thetaLevel_deg`. -/
def LevelIdentity (t T : TateParameter K) (N : ℕ) (hN : 0 < N) (P₁ Q₁ P₂ Q₂ : K[X]) : Prop :=
  ∀ u : Kˣ, OffOrbit T u →
    etaleTheta t u = (P₁.eval (T.X u) + T.Y u * Q₁.eval (T.X u)) * (u : K) ^ N *
        T.theta (-u) ^ (2 * N) ∧
      etaleTheta (tatePow t N hN) u ^ N =
        (P₂.eval (T.X u) + T.Y u * Q₂.eval (T.X u)) * (u : K) ^ N * T.theta (-u) ^ (2 * N)

/-- The identity of `exists_poly_thetaSq_deg`. -/
def SqIdentity (t T : TateParameter K) (N : ℕ) (hN : 0 < N) (P Q : K[X]) : Prop :=
  ∀ u : Kˣ, OffOrbit T u →
    etaleTheta (tatePow t N hN) u ^ 2 =
      (P.eval (T.X u) + T.Y u * Q.eval (T.X u)) * (u : K) ^ 2 * T.theta (-u) ^ 4

/-- The theta level function `f = num / den` in `K(E_Q)`. -/
abbrev cuspF (T : TateParameter K) (P₁ Q₁ P₂ Q₂ : K[X]) : TateField T :=
  algebraMap (TateRing T) (TateField T) (polyXY T P₁ Q₁) /
    algebraMap (TateRing T) (TateField T) (polyXY T P₂ Q₂)

omit [T.tateCurve.IsElliptic] in
theorem factor_ne_zero {u : Kˣ} (hu : OffOrbit T u) (k m : ℕ) :
    (u : K) ^ k * T.theta (-u) ^ m ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ u.ne_zero) (pow_ne_zero _ (theta_neg_ne_zero T hu))

omit [T.tateCurve.IsElliptic] in
theorem evalTate_num_eq (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) {u : Kˣ}
    (hu : OffOrbit T u) :
    etaleTheta t u = evalTate T h12 hu (polyXY T P₁ Q₁) * ((u : K) ^ N * T.theta (-u) ^ (2 * N))
    := by
  rw [evalTate_polyXY, (hlev u hu).1, mul_assoc]

omit [T.tateCurve.IsElliptic] in
theorem evalTate_den_eq (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) {u : Kˣ}
    (hu : OffOrbit T u) :
    etaleTheta (tatePow t N hN) u ^ N =
      evalTate T h12 hu (polyXY T P₂ Q₂) * ((u : K) ^ N * T.theta (-u) ^ (2 * N)) := by
  rw [evalTate_polyXY, (hlev u hu).2, mul_assoc]

omit [T.tateCurve.IsElliptic] in
theorem evalTate_den_ne_zero_iff (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) {u : Kˣ}
    (hu : OffOrbit T u) :
    evalTate T h12 hu (polyXY T P₂ Q₂) ≠ 0 ↔ etaleTheta (tatePow t N hN) u ≠ 0 := by
  rw [Ne, Ne, ← pow_eq_zero_iff (a := etaleTheta (tatePow t N hN) u) hN.ne',
    evalTate_den_eq hlev hu, mul_eq_zero, or_iff_left (factor_ne_zero hu _ _)]

omit [T.tateCurve.IsElliptic] in
/-- **Values of `f`**: `f(u) = Θ̈_q(u)/Θ̈_{q^N}(u)^N` where `Θ̈_{q^N}(u) ≠ 0`. -/
theorem hasTateValue_cuspF (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) {u : Kˣ}
    (hu : OffOrbit T u) (hθ : etaleTheta (tatePow t N hN) u ≠ 0) :
    HasTateValue T h12 (cuspF T P₁ Q₁ P₂ Q₂) hu (thetaLevel t N hN u) := by
  have hd := (evalTate_den_ne_zero_iff (h12 := h12) hlev hu).2 hθ
  refine ((HasTateValue.ofRing hu _).div (HasTateValue.ofRing hu _) hd).congr ?_
  have hu0 : (u : K) ^ N ≠ 0 := pow_ne_zero _ u.ne_zero
  have hθT : T.theta (-u) ^ (2 * N) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hu)
  rw [thetaLevel, evalTate_num_eq (h12 := h12) hlev hu, evalTate_den_eq (h12 := h12) hlev hu]
  field_simp

/-! ### Nonvanishing and the degree bound -/

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_num_ne_zero (h2 : ‖(2 : K)‖ = 1) (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    polyXY T P₁ Q₁ ≠ 0 := by
  intro h0
  have e := evalTate_num_eq (h12 := h12) hlev (offOrbit_twoU T h2)
  rw [h0, map_zero, zero_mul] at e
  exact etaleTheta_twoU_ne_zero t (h12 := h12) h2 e

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_den_ne_zero (h2 : ‖(2 : K)‖ = 1) (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    polyXY T P₂ Q₂ ≠ 0 :=
  ne_zero_of_evalTate_ne_zero ((evalTate_den_ne_zero_iff (h12 := h12) hlev
    (offOrbit_twoU T h2)).2 (etaleTheta_twoU_ne_zero _ (h12 := h12) h2))

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_ne_zero (h2 : ‖(2 : K)‖ = 1) (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    cuspF T P₁ Q₁ P₂ Q₂ ≠ 0 :=
  div_ne_zero (algebraMap_ne_zero (cusp_num_ne_zero (h12 := h12) h2 hlev))
    (algebraMap_ne_zero (cusp_den_ne_zero (h12 := h12) h2 hlev))

omit [CompleteSpace K] [IsUltrametricDist K] [T.tateCurve.IsElliptic] in
theorem cusp_deg_num_le (hP₁ : P₁.degree < ((2 * N) / 2 + 1 : ℕ))
    (hQ₁ : Q₁.degree < ((2 * N - 1) / 2 : ℕ)) :
    CoordinateRing.deg T.tateCurve.toAffine (polyXY T P₁ Q₁) ≤ 2 * N :=
  deg_smul_basis_le_of_degree_lt hP₁ hQ₁

/-! ### Inversion -/

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_negT (h2 : ‖(2 : K)‖ = 1) (hev : Even N)
    (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    negT T (cuspF T P₁ Q₁ P₂ Q₂) = -cuspF T P₁ Q₁ P₂ Q₂ := by
  refine eq_of_hasTateValue (h12 := h12) (cusp_den_ne_zero (h12 := h12) h2 hlev)
    (G := fun u => -thetaLevel t N hN u) (fun u hu hd => ?_) (fun u hu hd => ?_)
  · have hθ := (evalTate_den_ne_zero_iff (h12 := h12) hlev hu).1 hd
    have hθ' : etaleTheta (tatePow t N hN) u⁻¹ ≠ 0 := by
      rw [etaleTheta_inv, neg_ne_zero]; exact hθ
    exact hasTateValue_negY hu ((hasTateValue_cuspF (h12 := h12) hlev (offOrbit_inv T hu)
      hθ').congr (by rw [thetaLevel_inv N hN hev]))
  · exact (hasTateValue_cuspF (h12 := h12) hlev hu
      ((evalTate_den_ne_zero_iff (h12 := h12) hlev hu).1 hd)).neg

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_ordInfty_odd (h2 : ‖(2 : K)‖ = 1) (hev : Even N)
    (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    Odd (ordInfty T.tateCurve.toAffine (cuspF T P₁ Q₁ P₂ Q₂)) :=
  ordInfty_odd_of_negY (two_ne_zero_of_norm h2) (cusp_ne_zero (h12 := h12) h2 hlev)
    (cusp_negT (h12 := h12) h2 hev hlev)

/-! ### Translation by the `2`-torsion point `-1` -/

omit [T.tateCurve.IsElliptic] in
theorem offOrbit_mul_neg_one_of_etaleTheta (hs : s ^ 2 = t.q) (hT : T.q = s ^ N) {u : Kˣ}
    (hθ : etaleTheta (tatePow t N hN) u ≠ 0) : OffOrbit T (u * -1) := by
  intro n hn
  apply hθ
  rw [etaleTheta_eq_zero_iff]
  refine ⟨-n, ?_⟩
  rw [hT] at hn
  rw [tatePow_q, ← hs]
  push_cast at hn ⊢
  rw [← pow_mul (s : K) 2 N, mul_comm 2 N, pow_mul (s : K) N 2, sq ((s : K) ^ N), mul_zpow,
    zpow_neg, ← mul_inv]
  exact eq_inv_of_mul_eq_one_left (show (u : K) ^ 2 * (((s : K) ^ N) ^ n * ((s : K) ^ N) ^ n) = 1
    by linear_combination (((s : K) ^ N) ^ n * ((u : K) * -1) + 1) * hn)

omit [T.tateCurve.IsElliptic] in
theorem cusp_transT (h2 : ‖(2 : K)‖ = 1) (hs : s ^ 2 = t.q) (hT : T.q = s ^ N) (hev : Even N)
    (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    transT h12 (offOrbit_neg_one T h2) (cuspF T P₁ Q₁ P₂ Q₂) = -cuspF T P₁ Q₁ P₂ Q₂ := by
  set c := T.X (-1)
  have hx0 : mkT T (C (Polynomial.X - C c)) ≠ 0 := mk_C_ne_zero (X_sub_C_ne_zero c)
  have key : ∀ (u : Kˣ) (hu : OffOrbit T u),
      evalTate T h12 hu (polyXY T P₂ Q₂ * mkT T (C (Polynomial.X - C c))) ≠ 0 →
      etaleTheta (tatePow t N hN) u ≠ 0 ∧ T.X u ≠ T.X (-1) := by
    intro u hu hD
    rw [map_mul] at hD
    have hx := right_ne_zero_of_mul hD
    rw [evalTate_mk_C, eval_sub, eval_X, eval_C, sub_ne_zero] at hx
    exact ⟨(evalTate_den_ne_zero_iff (h12 := h12) hlev hu).1 (left_ne_zero_of_mul hD), hx⟩
  refine eq_of_hasTateValue (h12 := h12)
    (mul_ne_zero (cusp_den_ne_zero (h12 := h12) h2 hlev) hx0)
    (G := fun u => -thetaLevel t N hN u) (fun u hu hD => ?_) (fun u hu hD => ?_)
  · obtain ⟨hθ, hx⟩ := key u hu hD
    have huw := offOrbit_mul_neg_one_of_etaleTheta hs hT hθ
    have hθ' : etaleTheta (tatePow t N hN) (u * -1) ≠ 0 := by
      rw [mul_neg_one, etaleTheta_neg, neg_ne_zero]; exact hθ
    refine hasTateValue_trans (h12 := h12) h2 hu (offOrbit_neg_one T h2) huw hx _ _
      ((hasTateValue_cuspF (h12 := h12) hlev huw hθ').congr ?_)
    rw [mul_neg_one]
    simp only [thetaLevel, etaleTheta_neg, Even.neg_pow hev, neg_div]
  · exact (hasTateValue_cuspF (h12 := h12) hlev hu (key u hu hD).1).neg

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem divisorProj_neg' {f : TateField T} (hf : f ≠ 0) :
    divisorProj _ (-f) = divisorProj _ f := by
  rw [show -f = algebraMap K (TateField T) (-1) * f by simp,
    divisorProj_mul (by simp) hf, divisorProj_algebraMap_base (by simp), zero_add]

/-- **The orders of `f` at the `2`-torsion point `-1` and at infinity agree.** -/
theorem cusp_divisorProj_neg_one (h2 : ‖(2 : K)‖ = 1) (hs : s ^ 2 = t.q) (hT : T.q = s ^ N)
    (hev : Even N) (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) :
    divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) (ptT h12 (offOrbit_neg_one T h2)) =
      divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) none := by
  have hf := cusp_ne_zero (h12 := h12) h2 hlev
  have h := divisorProj_translateEndo_none (tateEquation h12 (offOrbit_neg_one T h2)) hf
  have ht := cusp_transT (h12 := h12) h2 hs hT hev hlev
  change translateEndo (tateEquation h12 (offOrbit_neg_one T h2)) _ = _ at ht
  rw [ht, divisorProj_neg' hf] at h
  exact h.symm

/-! ### The order at infinity -/

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_den_eq_pow (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂)
    (hsq : SqIdentity t T N hN P Q) {m : ℕ} (hm : N = 2 * m) :
    polyXY T P₂ Q₂ = polyXY T P Q ^ m := by
  rw [← sub_eq_zero]
  refine eq_zero_of_evalTate (h12 := h12) _ fun u hu => ?_
  rw [map_sub, map_pow, sub_eq_zero]
  have e1 := evalTate_den_eq (h12 := h12) hlev hu
  have e2 := hsq u hu
  rw [← evalTate_polyXY (h12 := h12) hu] at e2
  have hc := factor_ne_zero hu N (2 * N)
  apply mul_right_cancel₀ hc
  rw [← e1]
  subst hm
  rw [pow_mul, e2]
  ring

omit [CompleteSpace K] [IsUltrametricDist K] [T.tateCurve.IsElliptic] in
theorem deg_pow' (a : TateRing T) (m : ℕ) :
    CoordinateRing.deg T.tateCurve.toAffine (a ^ m) =
      m * CoordinateRing.deg T.tateCurve.toAffine a := by
  simp only [CoordinateRing.deg, map_pow, natDegree_pow]

include h12 in
omit [T.tateCurve.IsElliptic] in
theorem cusp_two_le_deg (h2 : ‖(2 : K)‖ = 1) (hsq : SqIdentity t T N hN P Q) :
    2 ≤ CoordinateRing.deg T.tateCurve.toAffine (polyXY T P Q) := by
  apply two_le_deg
  rintro ⟨c, hc⟩
  have e1 := hsq (-1) (offOrbit_neg_one T h2)
  have e2 := hsq (twoU h2) (offOrbit_twoU T h2)
  rw [← evalTate_polyXY (h12 := h12) (offOrbit_neg_one T h2), ← hc, evalTate_algebraMap] at e1
  rw [← evalTate_polyXY (h12 := h12) (offOrbit_twoU T h2), ← hc, evalTate_algebraMap] at e2
  have h0 : etaleTheta (tatePow t N hN) (-1) = 0 :=
    (etaleTheta_eq_zero_iff _ _).2 ⟨0, by simp⟩
  rw [h0, zero_pow two_ne_zero, mul_assoc] at e1
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp e1.symm with h | h
    · exact h
    · exact absurd h (factor_ne_zero (offOrbit_neg_one T h2) 2 4)
  rw [hc0, zero_mul, zero_mul] at e2
  exact etaleTheta_twoU_ne_zero _ (h12 := h12) h2 (pow_eq_zero_iff two_ne_zero |>.mp e2)

include h12 in
omit [T.tateCurve.IsElliptic] in
/-- **`-N ≤ ord_∞ f`.** -/
theorem cusp_ordInfty_ge (h2 : ‖(2 : K)‖ = 1) (hev : Even N)
    (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) (hsq : SqIdentity t T N hN P Q)
    (hP₁ : P₁.degree < ((2 * N) / 2 + 1 : ℕ)) (hQ₁ : Q₁.degree < ((2 * N - 1) / 2 : ℕ)) :
    -(N : ℤ) ≤ ordInfty T.tateCurve.toAffine (cuspF T P₁ Q₁ P₂ Q₂) := by
  obtain ⟨m, hm⟩ := hev
  have hf := cusp_ne_zero (h12 := h12) h2 hlev
  have hd0 := cusp_den_ne_zero (h12 := h12) h2 hlev
  have hmul : cuspF T P₁ Q₁ P₂ Q₂ * algebraMap (TateRing T) (TateField T) (polyXY T P₂ Q₂) =
      algebraMap (TateRing T) (TateField T) (polyXY T P₁ Q₁) :=
    div_mul_cancel₀ _ (algebraMap_ne_zero hd0)
  rw [ordInfty_eq_sub hf hd0 hmul, cusp_den_eq_pow (h12 := h12) hlev hsq (m := m) (by omega),
    deg_pow']
  have h1 := cusp_deg_num_le (T := T) hP₁ hQ₁
  have h3 := cusp_two_le_deg (h12 := h12) h2 hsq
  have h4 : m * 2 ≤ m * CoordinateRing.deg T.tateCurve.toAffine (polyXY T P Q) :=
    Nat.mul_le_mul_left m h3
  zify at h1 h4 hm ⊢
  linarith

/-! ### Zeros at the points `±s^a` -/

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem norm_s_lt_one (hs : s ^ 2 = t.q) : ‖(s : K)‖ < 1 := by
  have := t.norm_lt_one
  rw [← hs, Units.val_pow_eq_pow_val, norm_pow] at this
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem norm_eps {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) : ‖(ε : K)‖ = 1 := by
  have := congrArg norm hε
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this

omit [CompleteSpace K] [IsUltrametricDist K] [T.tateCurve.IsElliptic] in
theorem offOrbit_sign_pow (hs : s ^ 2 = t.q) (hT : T.q = s ^ N) {ε : Kˣ}
    (hε : (ε : K) ^ 2 = 1) {a : ℕ} (ha : 0 < a) (haN : a < N) : OffOrbit T (ε * s ^ a) := by
  intro n hn
  rw [hT] at hn
  have := congrArg norm hn
  push_cast at this
  rw [norm_mul, norm_zpow, norm_mul, norm_eps hε, one_mul, norm_pow, norm_pow, norm_one] at this
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hr0 : ‖(s : K)‖ ≠ 0 := norm_ne_zero_iff.mpr hs0
  have e : ‖(s : K)‖ ^ ((N : ℤ) * n + a) = 1 := by
    rw [zpow_add₀ hr0, zpow_mul, zpow_natCast, zpow_natCast]; exact this
  have := eq_zero_of_norm_zpow hs0 (norm_s_lt_one hs) e
  rcases le_or_gt 0 n with h | h <;> nlinarith

omit [T.tateCurve.IsElliptic] in
theorem etaleTheta_sign_pow_eq_zero (hs : s ^ 2 = t.q) {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) (a : ℕ) :
    etaleTheta t (ε * s ^ a) = 0 := by
  rw [etaleTheta_eq_zero_iff]
  refine ⟨a, ?_⟩
  rw [zpow_natCast, ← hs]
  push_cast
  rw [mul_pow, hε, one_mul, ← pow_mul, ← pow_mul, mul_comm]

omit [T.tateCurve.IsElliptic] in
theorem etaleTheta_tatePow_sign_pow_ne_zero (hs : s ^ 2 = t.q) {ε : Kˣ}
    (hε : (ε : K) ^ 2 = 1) {a : ℕ} (ha : 0 < a) (haN : a < N) :
    etaleTheta (tatePow t N hN) (ε * s ^ a) ≠ 0 := by
  rw [Ne, etaleTheta_eq_zero_iff]
  rintro ⟨k, hk⟩
  rw [tatePow_q, ← hs] at hk
  have := congrArg norm hk
  push_cast at this
  simp only [norm_pow, norm_mul, norm_eps hε, one_mul, norm_zpow] at this
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have e : ‖(s : K)‖ ^ (((a * 2 : ℕ) : ℤ)) = ‖(s : K)‖ ^ (((2 * N : ℕ) : ℤ) * k) := by
    rw [zpow_mul, zpow_natCast, zpow_natCast, pow_mul, pow_mul]; exact this
  have := zpow_right_injective₀ (norm_pos_iff.mpr hs0) (norm_s_lt_one hs).ne e
  push_cast at this
  rcases le_or_gt k 0 with h | h <;> nlinarith

include h12 in
/-- **`f` vanishes at the Tate points `±s^a`, `0 < a < N`.** -/
theorem cusp_one_le_divisorProj (h2 : ‖(2 : K)‖ = 1) (hs : s ^ 2 = t.q)
    (hlev : LevelIdentity t T N hN P₁ Q₁ P₂ Q₂) {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) {a : ℕ}
    (ha : 0 < a) (haN : a < N) (hw : OffOrbit T (ε * s ^ a)) :
    1 ≤ divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) (ptT h12 hw) := by
  have hnum0 := cusp_num_ne_zero (h12 := h12) h2 hlev
  have hden0 := cusp_den_ne_zero (h12 := h12) h2 hlev
  have hnum : evalTate T h12 hw (polyXY T P₁ Q₁) = 0 := by
    have e := evalTate_num_eq (h12 := h12) hlev hw
    rw [etaleTheta_sign_pow_eq_zero hs hε a] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact h
    · exact absurd h (factor_ne_zero hw _ _)
  have hden : evalTate T h12 hw (polyXY T P₂ Q₂) ≠ 0 :=
    (evalTate_den_ne_zero_iff (h12 := h12) hlev hw).2
      (etaleTheta_tatePow_sign_pow_ne_zero hs hε ha haN)
  rw [divisorProj_div (algebraMap_ne_zero hnum0) (algebraMap_ne_zero hden0), Finsupp.sub_apply,
    ord_eq_zero_of_evalTate_ne_zero hw hden, sub_zero]
  have := ord_pos_of_evalTate_eq_zero hw hnum0 hnum
  omega

end Cusp

/-! ### The cusp data for the polynomials of Tate's theorem -/

/-- **The cusp data of the theta level function.** For `Q = s^N` (`s² = q`, `N` even), the
polynomials of `exists_poly_thetaLevel_deg` give `f = num/den ∈ K(E_Q)` with values
`Θ̈_q/Θ̈_{q^N}^N`, and: `num, den, f ≠ 0`, `deg num ≤ 2N`, `[-1]^* f = -f`, `ord_∞ f` odd,
translation by `-1` negates `f` (so the orders of `f` at `-1` and `∞` agree), `-N ≤ ord_∞ f`,
and `f` vanishes at `±s^a` for `0 < a < N`. -/
theorem exists_thetaLevel_cuspData (t : TateParameter K) (h12 : (12 : K) ≠ 0)
    (h2 : ‖(2 : K)‖ = 1) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (hev : Even N)
    (T : TateParameter K) (hT : T.q = s ^ N) [T.tateCurve.IsElliptic] :
    ∃ P₁ Q₁ P₂ Q₂ : K[X],
      P₁.degree < ((2 * N) / 2 + 1 : ℕ) ∧ Q₁.degree < ((2 * N - 1) / 2 : ℕ) ∧
      P₂.degree < ((2 * N) / 2 + 1 : ℕ) ∧ Q₂.degree < ((2 * N - 1) / 2 : ℕ) ∧
      LevelIdentity t T N hN P₁ Q₁ P₂ Q₂ ∧
      polyXY T P₁ Q₁ ≠ 0 ∧ polyXY T P₂ Q₂ ≠ 0 ∧ cuspF T P₁ Q₁ P₂ Q₂ ≠ 0 ∧
      CoordinateRing.deg T.tateCurve.toAffine (polyXY T P₁ Q₁) ≤ 2 * N ∧
      negT T (cuspF T P₁ Q₁ P₂ Q₂) = -cuspF T P₁ Q₁ P₂ Q₂ ∧
      Odd (ordInfty T.tateCurve.toAffine (cuspF T P₁ Q₁ P₂ Q₂)) ∧
      transT h12 (offOrbit_neg_one T h2) (cuspF T P₁ Q₁ P₂ Q₂) = -cuspF T P₁ Q₁ P₂ Q₂ ∧
      divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) (ptT h12 (offOrbit_neg_one T h2)) =
        divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) none ∧
      -(N : ℤ) ≤ ordInfty T.tateCurve.toAffine (cuspF T P₁ Q₁ P₂ Q₂) ∧
      ∀ (ε : Kˣ), (ε : K) ^ 2 = 1 → ∀ a : ℕ, 0 < a → a < N →
        ∀ hw : OffOrbit T (ε * s ^ a), 1 ≤ divisorProj _ (cuspF T P₁ Q₁ P₂ Q₂) (ptT h12 hw) := by
  obtain ⟨P₁, Q₁, P₂, Q₂, d₁, d₁', d₂, d₂', hlev⟩ :=
    exists_poly_thetaLevel_deg t h12 hs hN hev T hT
  obtain ⟨P, Q, -, -, hsq⟩ := exists_poly_thetaSq_deg t h12 hs hN T hT
  exact ⟨P₁, Q₁, P₂, Q₂, d₁, d₁', d₂, d₂', hlev,
    cusp_num_ne_zero (h12 := h12) h2 hlev, cusp_den_ne_zero (h12 := h12) h2 hlev,
    cusp_ne_zero (h12 := h12) h2 hlev, cusp_deg_num_le d₁ d₁',
    cusp_negT (h12 := h12) h2 hev hlev, cusp_ordInfty_odd (h12 := h12) h2 hev hlev,
    cusp_transT (h12 := h12) h2 hs hT hev hlev,
    cusp_divisorProj_neg_one (h12 := h12) h2 hs hT hev hlev,
    cusp_ordInfty_ge (h12 := h12) h2 hev hlev (P := P) (Q := Q) hsq d₁ d₁',
    fun ε hε a ha haN hw => cusp_one_le_divisorProj (h12 := h12) h2 hs hlev hε ha haN hw⟩

end Iut.EtaleTheta
