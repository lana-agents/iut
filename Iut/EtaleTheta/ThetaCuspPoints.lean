/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCuspOrder
import EllipticCurves.FunctionField.RationalPointDegree
import EllipticCurves.FunctionField.TranslationProjAction

/-!
# The `2N` cusps of `Ÿ'_N` as points of `E_Q` (MR14)

For `Q = s^N` the kernel of `φ : E_Q → E_q`, `Ü ↦ Ü²`, consists of the `2N` points `±s^a`
(`0 ≤ a < N`) modulo `Q^ℤ`; `+s^0 = 1` is the origin `O`. This file builds the set `cuspSet` of the
corresponding projective points (`none` for `O`, `ptT` otherwise), proves that it has `2N` elements
and that all of them have degree `1`.
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {s : Kˣ} {N : ℕ} {T : TateParameter K} (hT : T.q = s ^ N) (hN : 0 < N)

/-- The kernel element `(-1)^e · s^a`. -/
def cuspElt (s : Kˣ) (e : Fin 2) (a : ℕ) : Kˣ := (-1) ^ (e : ℕ) * s ^ a

omit [CompleteSpace K] [IsUltrametricDist K] in
include hT hN in
theorem norm_s_lt_one_of_q : ‖(s : K)‖ < 1 := by
  have h := T.norm_lt_one
  rw [hT, Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hN.ne').mp h

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem norm_cuspElt (e : Fin 2) (a : ℕ) : ‖(cuspElt s e a : K)‖ = ‖(s : K)‖ ^ a := by
  simp [cuspElt, norm_pow]

omit [CompleteSpace K] [IsUltrametricDist K] in
include hT hN in
/-- If `(-1)^e s^a = Q^n (-1)^{e'} s^{a'}` with `a, a' < N` then `n = 0`, `a = a'`, `e = e'`. -/
theorem cuspElt_eq_of [CharZero K] {e e' : Fin 2} {a a' : ℕ} (ha : a < N) (ha' : a' < N) {n : ℤ}
    (h : (cuspElt s e a : K) = (T.q : K) ^ n * (cuspElt s e' a' : K)) :
    e = e' ∧ a = a' := by
  have hs1 := norm_s_lt_one_of_q hT hN
  have hs0 : 0 < ‖(s : K)‖ := norm_pos_iff.mpr s.ne_zero
  have hn := congrArg norm h
  rw [norm_mul, norm_zpow, norm_cuspElt, norm_cuspElt, hT, Units.val_pow_eq_pow_val, norm_pow,
    ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hs0.ne'] at hn
  have hinj := zpow_right_injective₀ hs0 (ne_of_lt hs1)
  have he := hinj hn
  have haa : a = a' := by
    have : (a : ℤ) - a' = N * n := by linarith
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · nlinarith
    · subst hn0; omega
    · nlinarith
  subst haa
  have hn0 : n = 0 := by
    have : (N : ℤ) * n = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · omega
    · exact h0
  subst hn0
  refine ⟨?_, rfl⟩
  rw [zpow_zero, one_mul] at h
  have hs : ((s : K) ^ a) ≠ 0 := pow_ne_zero _ s.ne_zero
  simp only [cuspElt, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
    at h
  have h' := mul_right_cancel₀ hs h
  fin_cases e <;> fin_cases e'
  · rfl
  · norm_num at h'
  · norm_num at h'
  · rfl

omit [CompleteSpace K] [IsUltrametricDist K] in
include hT hN in
theorem offOrbit_cuspElt [CharZero K] {e : Fin 2} {a : ℕ} (ha : a < N) (h0 : (e, a) ≠ (0, 0)) :
    OffOrbit T (cuspElt s e a) := by
  intro n hn
  have h1 : (cuspElt s e a : K) = (T.q : K) ^ (-n) * (cuspElt s 0 0 : K) := by
    simp only [cuspElt, Fin.val_zero, pow_zero, mul_one, Units.val_one, zpow_neg]
    exact eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans hn)
  obtain ⟨he, ha'⟩ := cuspElt_eq_of hT hN ha hN h1
  exact h0 (by rw [he, ha'])

variable [CharZero K] (h12 : (12 : K) ≠ 0) (h2 : ‖(2 : K)‖ = 1) [T.tateCurve.IsElliptic]

open Classical in
/-- The projective point of the kernel element `(-1)^e s^a` (`none` for `e = a = 0`). -/
def cuspPt (p : Fin 2 × Fin N) : ProjPoint T.tateCurve.toAffine :=
  if h : (p.1, (p.2 : ℕ)) = (0, 0) then none
  else ptT h12 (offOrbit_cuspElt hT hN p.2.2 h)

include h12 h2 in
omit [T.tateCurve.IsElliptic] [CharZero K] in
/-- Two Tate points with the same coordinates differ by a power of `Q`. -/
theorem exists_zpow_of_coords_eq {u v : Kˣ} (hu : OffOrbit T u) (hv : OffOrbit T v)
    (hX : T.X u = T.X v) (hY : T.Y u = T.Y v) : ∃ n : ℤ, (u : K) = (T.q : K) ^ n * (v : K) := by
  classical
  have hmem : ∀ w : Kˣ, (∀ n : ℤ, (T.q : K) ^ n * (w : K) ≠ 1) →
      T.tateCurve.toAffine.Equation (T.X w) (T.Y w) := fun w hw => T.tatePoint_mem' h12 hw
  have htame : TameResidueChar K := ⟨h2, h12⟩
  have hnq : ∀ {w : Kˣ}, OffOrbit T w → w ∉ T.qpowers := by
    intro w hw hq
    obtain ⟨n, hn⟩ := (T.mem_qpowers_iff_val_eq).mp hq
    exact hw (-n) (by rw [hn, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ T.q.ne_zero)])
  have he : T.tatePoint hmem htame u = T.tatePoint hmem htame v := by
    rw [T.tatePoint_of_notMem hmem htame (hnq hu), T.tatePoint_of_notMem hmem htame (hnq hv)]
    simp only [hX, hY]
  have hk : u * v⁻¹ ∈ T.qpowers := by
    rw [← T.tatePointHom_ker hmem htame, MonoidHom.mem_ker, map_mul, map_inv,
      T.tatePointHom_apply, T.tatePointHom_apply, he, mul_inv_cancel]
  obtain ⟨n, hn⟩ := (T.mem_qpowers_iff_val_eq).mp hk
  refine ⟨n, ?_⟩
  rw [← hn, Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc, inv_mul_cancel₀ v.ne_zero,
    mul_one]

include h2 in
theorem cuspPt_injective : Function.Injective (cuspPt hT hN h12) := by
  rintro ⟨e, a⟩ ⟨e', a'⟩ h
  simp only [cuspPt] at h
  split_ifs at h with h1 h1' h1'
  · simp only [Prod.mk.injEq] at h1 h1'
    exact Prod.ext (h1.1.trans h1'.1.symm) (Fin.ext (h1.2.trans h1'.2.symm))
  · obtain ⟨hX, hY⟩ := eq_of_pointClosedPoint_eq _ _ (Option.some_injective _ h)
    obtain ⟨n, hn⟩ := exists_zpow_of_coords_eq h12 h2
      (offOrbit_cuspElt hT hN a.2 h1) (offOrbit_cuspElt hT hN a'.2 h1') hX hY
    obtain ⟨he, ha⟩ := cuspElt_eq_of hT hN a.2 a'.2 hn
    exact Prod.ext he (Fin.ext ha)

open Classical in
/-- **The cusps of `Ÿ'_N` on `E_Q`**: the `2N` points of the kernel of `Ü ↦ Ü²`. -/
def cuspSet : Finset (ProjPoint T.tateCurve.toAffine) :=
  (Finset.univ : Finset (Fin 2 × Fin N)).image (cuspPt hT hN h12)

open Classical in
include h2 in
theorem card_cuspSet : (cuspSet hT hN h12).card = 2 * N := by
  rw [cuspSet, Finset.card_image_of_injective _ (cuspPt_injective hT hN h12 h2), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [CharZero K] in
theorem degProjPt_ptT {u : Kˣ} (hu : OffOrbit T u) : degProjPt _ (ptT h12 hu) = 1 :=
  degPt_pointClosedPoint (equation_iff_nonsingular.mp (tateEquation h12 hu))

open Classical in
theorem degProjPt_cuspSet : ∀ p ∈ cuspSet hT hN h12, degProjPt _ p = 1 := by
  intro p hp
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hp
  unfold cuspPt
  split_ifs
  · rfl
  · exact degProjPt_ptT h12 _

end Iut.EtaleTheta
