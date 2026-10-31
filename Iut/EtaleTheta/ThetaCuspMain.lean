/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCuspPoints
import Iut.EtaleTheta.ThetaCuspLevelFn
import Iut.EtaleTheta.ThetaCuspIsogeny
import Iut.EtaleTheta.CuspCount

/-!
# The orders of `f_N` at the cusps of `Ÿ'_N` (MR14, [EtTh] Prop. 1.4(i), finite level)

[EtTh] Prop. 1.4(i) (`The Etale Theta Function ….txt`, l.1322–1324): the zeros of `Θ̈` on `Ÿ` are
precisely the cusps, each of multiplicity `1`. At the level `Ÿ'_N` of route R-alg (`Q = s^N`,
`N` even, `Ÿ'_N = E_Q ∖ ker φ`, `φ(Ü) = Ü²`), the theta level function
`f_N = Θ̈_q/Θ̈_{q^N}^N ∈ K(E_Q)` has, at every cusp, order `1` (at `±s^a`, `0 < a < N`) or `1 - N`
(at `O` and `-1`): **always `≡ 1 mod N`**.

`thetaLevel_cusp_orders`: there are `f, R ∈ K(E_Q)` with the values `f_N(Ü)` resp. `X_q(Ü²)`
(`R = φ^* x_q`, so the cusps of `Ÿ'_N` are the poles of `R`) such that, if `R ≠ 0` and `f` is a unit
at every place where `R` is regular (both are proved on the étale side, where `R` is the coordinate
`τ` of the Galois datum and `f` is the unit `η_N` of `ThetaClassSystem.lean`), then every pole of
`R` lies in `cuspSet` and `f` has order `1` or `1 - N` there.

Proof: `R` is invariant under translation by `ker φ` (`ThetaCuspIsogeny.lean`), so it has the same
even order at all `2N` points of `cuspSet`; a degree count (`sum_pole_le`) shows that it has no
other poles; then `deg (div f) = 0` with the lower bounds of `ThetaCuspLevelFn.lean` forces the
orders (`cusp_orders_of_count`, `CuspCount.lean`).
-/

open Polynomial IsDedekindDomain

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K] [CharZero K]

omit [CharZero K] in
theorem ptT_congr {T : TateParameter K} {h12 : (12 : K) ≠ 0} [T.tateCurve.IsElliptic]
    {u v : Kˣ} (h : u = v) (hu : OffOrbit T u) (hv : OffOrbit T v) :
    ptT h12 hu = ptT h12 hv := by
  subst h; rfl

open Classical in
/-- **The orders of the theta level function at the cusps of `Ÿ'_N`** (see the module
docstring). -/
theorem thetaLevel_cusp_orders (t : TateParameter K) (h12 : (12 : K) ≠ 0)
    (h2 : ‖(2 : K)‖ = 1) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N) (hN2 : 2 ≤ N)
    (hev : Even N) (T : TateParameter K) (hT : T.q = s ^ N) [T.tateCurve.IsElliptic] :
    ∃ f R : TateField T,
      (∀ (u : Kˣ) (hu : OffOrbit T u), etaleTheta (tatePow t N hN) u ≠ 0 →
        HasTateValue T h12 f hu (thetaLevel t N hN u)) ∧
      (∀ (u : Kˣ) (hu : OffOrbit T u), OffOrbit t (u ^ 2) →
        HasTateValue T h12 R hu (t.X (u ^ 2))) ∧
      (R ≠ 0 → (∀ p, 0 ≤ divisorProj _ R p → divisorProj _ f p = 0) →
        ∀ p, divisorProj _ R p < 0 → p ∈ cuspSet hT hN h12 ∧
          ((p ≠ none ∧ p ≠ ptT h12 (offOrbit_neg_one T h2) ∧ divisorProj _ f p = 1) ∨
            ((p = none ∨ p = ptT h12 (offOrbit_neg_one T h2)) ∧
              divisorProj _ f p = 1 - N))) := by
  obtain ⟨P₁, Q₁, P₂, Q₂, -, -, -, -, hlev, -, -, hf0, hdegnum, -, hodd, -, hfP₀, hlow,
    hzero⟩ := exists_thetaLevel_cuspData t h12 h2 hs hN hev T hT
  obtain ⟨A₁, B₁, A₂, B₂, e₁, e₁', e₂, e₂', hR⟩ := exists_poly_isogenyX_deg t h12 hs hN T hT
  refine ⟨cuspF T P₁ Q₁ P₂ Q₂, algebraMap _ (TateField T) (polyXY T A₁ B₁) /
      algebraMap _ (TateField T) (polyXY T A₂ B₂),
    fun u hu hθ => hasTateValue_cuspF hlev hu hθ, fun u hu hu2 => hasTateValue_R hR hu hu2,
    fun hR0 hU => ?_⟩
  set R := algebraMap _ (TateField T) (polyXY T A₁ B₁) /
      algebraMap _ (TateField T) (polyXY T A₂ B₂) with hRdef
  have hnR : polyXY T A₁ B₁ ≠ 0 := by intro h; apply hR0; simp [hRdef, h]
  have hdR : polyXY T A₂ B₂ ≠ 0 := by intro h; apply hR0; simp [hRdef, h]
  have h4 : 2 * N * 2 = 4 * N := by ring
  have hdeg₁ : CoordinateRing.deg T.tateCurve.toAffine (polyXY T A₁ B₁) ≤ 4 * N := by
    rw [← h4]; exact deg_smul_basis_le_of_degree_lt e₁ e₁'
  have hdeg₂ : CoordinateRing.deg T.tateCurve.toAffine (polyXY T A₂ B₂) ≤ 4 * N := by
    rw [← h4]; exact deg_smul_basis_le_of_degree_lt e₂ e₂'
  have hdegnum' : CoordinateRing.deg T.tateCurve.toAffine (polyXY T P₁ Q₁) ≤ 4 * N := by
    omega
  have hm1 : cuspElt s 1 0 = -1 := by simp [cuspElt]
  have hP₀ : cuspPt hT hN h12 (1, ⟨0, hN⟩) = ptT h12 (offOrbit_neg_one T h2) := by
    simp only [cuspPt, Prod.mk.injEq, one_ne_zero, false_and, dite_false]
    exact ptT_congr hm1 _ _
  have hO : cuspPt hT hN h12 (0, ⟨0, hN⟩) = none := by simp [cuspPt]
  -- translation invariance of the orders of `R` on the cusp set
  have hRZ : ∀ p ∈ cuspSet hT hN h12, divisorProj _ R p = divisorProj _ R none := by
    intro p hp
    obtain ⟨⟨e, a⟩, -, rfl⟩ := Finset.mem_image.mp hp
    unfold cuspPt
    split_ifs with h
    · rfl
    set w := cuspElt s e a
    have hw : OffOrbit T w := offOrbit_cuspElt hT hN a.2 h
    have hw' : OffOrbit T w⁻¹ := offOrbit_inv T hw
    have hk : ∃ k : ℤ, ((w⁻¹ : Kˣ) : K) ^ 2 = (t.q : K) ^ k := by
      refine ⟨-(a : ℤ), ?_⟩
      have hsq : ((-1 : K) ^ (e : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      simp only [w, cuspElt, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_neg, Units.val_one, inv_pow, mul_pow, hsq, one_mul, zpow_neg, zpow_natCast]
      rw [← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, hs]
    have hinv := transT_R_eq (h12 := h12) hs hN hT h2 hR hw' hk
    change translateEndo (tateEquation h12 hw') R = R at hinv
    have key := divisorProj_translateEndo_pointClosedPoint (tateEquation h12 hw') hR0
    rw [hinv] at key
    rw [← key]
    congr 1
    refine congrArg some (HeightOneSpectrum.ext ?_)
    have hx : T.X w⁻¹ = T.X w := T.X_inv hw
    have hy : T.tateCurve.toAffine.negY (T.X w⁻¹) (T.Y w⁻¹) = T.Y w := by
      rw [T.Y_inv hw, hx]
      simp [WeierstrassCurve.Affine.negY, tateCurve_a₁, tateCurve_a₃]
    rw [pointClosedPoint_asIdeal, pointClosedPoint_asIdeal, hy, hx]
  have hReven : Even (divisorProj _ R none) := by
    rw [divisorProj_apply_none]
    exact ordInfty_even_of_negY (two_ne_zero_of_norm h2) hR0 (negT_R_eq hs hN hT h12 hR)
  refine cusp_orders_of_count hN2 hev hf0 hnR hdR hdeg₁ hdeg₂ rfl (cuspSet hT hN h12)
    (card_cuspSet hT hN h12 h2) (degProjPt_cuspSet hT hN h12)
    (ptT h12 (offOrbit_neg_one T h2))
    (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hO⟩)
    (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hP₀⟩) (Option.some_ne_none _) ?_ hRZ hReven
    (by rw [divisorProj_apply_none]; exact hodd) hfP₀
    (by rw [divisorProj_apply_none]; exact hlow) hU
  intro p hp hpO hpP₀
  obtain ⟨⟨e, a⟩, -, rfl⟩ := Finset.mem_image.mp hp
  have ha : 0 < (a : ℕ) := by
    rcases Nat.eq_zero_or_pos (a : ℕ) with h0 | h0
    · exfalso
      fin_cases e
      · exact hpO (by rw [← hO]; congr; exact Fin.ext h0)
      · exact hpP₀ (by rw [← hP₀]; congr; exact Fin.ext h0)
    · exact h0
  have hne : (e, (a : ℕ)) ≠ (0, 0) := by simp [ha.ne']
  have hε : (((-1) ^ (e : ℕ) : Kˣ) : K) ^ 2 = 1 := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, pow_mul]; simp
  have := hzero ((-1) ^ (e : ℕ)) hε a ha a.2 (offOrbit_cuspElt hT hN a.2 hne)
  unfold cuspPt
  rw [dif_neg hne]
  exact this

end Iut.EtaleTheta
