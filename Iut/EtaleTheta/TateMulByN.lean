/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaIsogeny
import CurvesJacobian.Cusp.EllipticMulByN
import TateCurvesTheta.TateCurve.GroupLaw

/-!
# `[m]^*` on the Tate curve: values at Tate points (MR14, G1 step 1)

For the Tate curve `E = E_q` over a complete nonarchimedean field `K` of characteristic `0` with
`‖2‖ = 1` (odd residue characteristic, as for the places of `V^bad_mod` in IUT I, Def. 3.1(b)),
`curves-jacobian`'s multiplication map `[m]^* : K[E] → K[E][1/ψ_m]`
(`CurvesJacobian.Cusp.mulByNHom`) is computed on values: the element `[m]^*a` of `K(E_q)` has
value `a(u^m)` at the Tate point of `u` (`hasTateValue_mulByNHom`). This uses the group law of
the Tate parametrisation (`tatePoint_mul`, which needs `‖2‖ = 1`) and the division-polynomial
formula for `m • P` (`nsmul_eq_some_omegaY_of_ΨSq_ne_zero`).

Consequence (`exists_levelField_mulByN`): for even `N`, the image of `[2N]^*` lies in the
function field `ψ^*K(E_Q) = K(x_Q∘ψ, y_Q∘ψ)` of `Ÿ'_N` which contains `F_N = f_N∘ψ`; this
identifies the value-defined `[2N]^*x_q`, `[2N]^*y_q` of `exists_levelField` with `cj`'s map.
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine CurvesJacobian.Cusp

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable {t : TateParameter K} {h12 : (12 : K) ≠ 0}

theorem evalTate_mkT {u : Kˣ} (hu : OffOrbit t u) (p : K[X][X]) :
    evalTate t h12 hu (mkT t p) = p.evalEval (t.X u) (t.Y u) := by
  rw [evalTate, mkT, CoordinateRing.mk, AdjoinRoot.lift_mk, eval₂_evalRingHom]

section Cover

variable (m : ℕ)

/-- Evaluation of `K[E][1/ψ_m]` at a Tate point where `ψ_m` does not vanish. -/
def evalCover {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) : coverRingN t.tateCurve m →+* K :=
  IsLocalization.Away.lift (psiN t.tateCurve m) (g := evalTate t h12 hu) (IsUnit.mk0 _ hψ)

theorem evalCover_algebraMap {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) (a : TateRing t) :
    evalCover m hu hψ (algebraMap _ _ a) = evalTate t h12 hu a :=
  IsLocalization.Away.lift_eq _ _ a

theorem evalCover_algebraMap_K {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) (c : K) :
    evalCover m hu hψ (algebraMap K _ c) = c := by
  rw [IsScalarTower.algebraMap_apply K (TateRing t), evalCover_algebraMap, evalTate_algebraMap]

theorem evalTate_aeval_xE {u : Kˣ} (hu : OffOrbit t u) (p : K[X]) :
    evalTate t h12 hu (aeval (xE t.tateCurve) p) = p.eval (t.X u) := by
  rw [← algebraMap_polynomial_eq_aeval_xE, AdjoinRoot.algebraMap_eq]
  exact evalTate_mk_C hu p

theorem evalCover_aeval {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) (p : K[X]) :
    evalCover m hu hψ (aeval (xBN t.tateCurve m) p) = p.eval (t.X u) := by
  rw [← algebraMap_aeval_xE, evalCover_algebraMap, evalTate_aeval_xE]

theorem evalCover_invPsiNB {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) :
    evalCover m hu hψ (invPsiNB t.tateCurve m) = (evalTate t h12 hu (psiN t.tateCurve m))⁻¹ := by
  have h := congrArg (evalCover m hu hψ) (psiNB_mul_invPsiNB t.tateCurve m)
  rw [map_mul, map_one, psiNB, evalCover_algebraMap] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Elements of `K[E][1/ψ_m]` have their evaluation as value. -/
theorem hasTateValue_cover [CharZero K] [NeZero m] {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) (b : coverRingN t.tateCurve m) :
    HasTateValue t h12 (algebraMap _ (TateField t) b) hu (evalCover m hu hψ b) := by
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (psiN t.tateCurve m)) b
  refine ⟨a, psiN t.tateCurve m ^ k, ?_, by rw [map_pow]; exact pow_ne_zero _ hψ, ?_⟩
  · rw [IsScalarTower.algebraMap_apply (TateRing t) (coverRingN t.tateCurve m) (TateField t) a,
      IsScalarTower.algebraMap_apply (TateRing t) (coverRingN t.tateCurve m) (TateField t),
      ← map_mul, IsLocalization.mk'_spec]
  · have := IsLocalization.mk'_spec (coverRingN t.tateCurve m) a
      (⟨psiN t.tateCurve m ^ k, k, rfl⟩ : Submonoid.powers (psiN t.tateCurve m))
    have h := congrArg (evalCover m hu hψ) this
    rw [map_mul, evalCover_algebraMap, evalCover_algebraMap] at h
    exact h

end Cover

section MulByN

variable [CharZero K]

/-- The point identity `P(u^m) = m • P(u)` and the division-polynomial formula: if
`ΨSq_m(X(u)) ≠ 0` then `u^m` is off the orbit and
`X(u^m) = Φ_m(X(u))/ΨSq_m(X(u))`, `Y(u^m) = ω_m(X(u), Y(u))`. -/
theorem tate_pow_coords (h2 : ‖(2 : K)‖ = 1) (h12 : (12 : K) ≠ 0) {m : ℕ} {u : Kˣ}
    (hu : OffOrbit t u)
    (hΨ : (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) ≠ 0) :
    OffOrbit t (u ^ m) ∧
      t.X (u ^ m) = (t.tateCurve.Φ (m : ℤ)).eval (t.X u) / (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) ∧
      t.Y (u ^ m) = t.tateCurve.toAffine.omegaY (t.X u) (t.Y u) (m : ℤ) := by
  classical
  have hmem : ∀ v : Kˣ, (∀ n : ℤ, (t.q : K) ^ n * (v : K) ≠ 1) →
      t.tateCurve.toAffine.Equation (t.X v) (t.Y v) := fun v hv => t.tatePoint_mem' h12 hv
  have tame : TameResidueChar K := ⟨h2, h12⟩
  haveI : t.tateCurve.toAffine.IsElliptic := t.tateCurve_isElliptic h12
  have hpow : t.tatePoint hmem tame (u ^ m) = m • t.tatePoint hmem tame u := by
    have := map_pow (t.tatePointHom hmem tame) u m
    rw [tatePointHom_apply, tatePointHom_apply] at this
    rw [← toAdd_ofAdd (t.tatePoint hmem tame (u ^ m)), this, toAdd_pow, toAdd_ofAdd]
  have hnot : u ∉ t.qpowers := fun h => (t.mem_qpowers_iff u).mp h |>.elim fun n hn => hu n hn
  rw [t.tatePoint_of_notMem hmem tame hnot] at hpow
  obtain ⟨h', hP⟩ := nsmul_eq_some_omegaY_of_ΨSq_ne_zero (W := t.tateCurve.toAffine)
    (two_ne_zero) (WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (hmem u (t.qzpow_mul_ne_one_of_notMem hnot))) hΨ
  rw [hP] at hpow
  have hnot' : u ^ m ∉ t.qpowers := by
    intro h
    rw [t.tatePoint_of_mem hmem tame h] at hpow
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hpow.symm
  rw [t.tatePoint_of_notMem hmem tame hnot', WeierstrassCurve.Affine.Point.some.injEq] at hpow
  exact ⟨t.qzpow_mul_ne_one_of_notMem hnot', hpow⟩

variable (m : ℕ) [NeZero m] [t.tateCurve.IsElliptic]

/-- **Values of `[m]^*`**: at the Tate point of `u` with `ψ_m(u) ≠ 0`, the element `[m]^*a` of
`K(E_q)` has the value `a(u^m)`. -/
theorem hasTateValue_mulByNHom (h2 : ‖(2 : K)‖ = 1) {u : Kˣ} (hu : OffOrbit t u)
    (hψ : evalTate t h12 hu (psiN t.tateCurve m) ≠ 0) :
    ∃ hum : OffOrbit t (u ^ m), ∀ a : TateRing t,
      HasTateValue t h12 (algebraMap _ (TateField t) (mulByNHom t.tateCurve m a)) hu
        (evalTate t h12 hum a) := by
  have hE : t.tateCurve.toAffine.Equation (t.X u) (t.Y u) := t.tatePoint_mem' h12 hu
  have hψe : evalTate t h12 hu (psiN t.tateCurve m) =
      (t.tateCurve.ψ (m : ℤ)).evalEval (t.X u) (t.Y u) :=
    evalTate_mkT hu _
  have hΨ : (t.tateCurve.ΨSq (m : ℤ)).eval (t.X u) ≠ 0 := by
    rw [← ψ_sq_evalEval hE, ← hψe]; exact pow_ne_zero _ hψ
  obtain ⟨hum, hX, hY⟩ := tate_pow_coords h2 h12 hu hΨ
  refine ⟨hum, fun a => ?_⟩
  suffices e : (evalCover m hu hψ).comp (mulByNHom t.tateCurve m) = evalTate t h12 hum by
    rw [← e]; exact hasTateValue_cover m hu hψ _
  refine AdjoinRoot.ringHom_ext ?_ ?_
  · refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · change evalCover m hu hψ (mulByNHom t.tateCurve m (algebraMap K (TateRing t) c)) =
        evalTate t h12 hum (algebraMap K (TateRing t) c)
      rw [mulByNHom_algebraMap, evalTate_algebraMap, IsScalarTower.algebraMap_apply K (TateRing t),
        evalCover_algebraMap, evalTate_algebraMap]
    · change evalCover m hu hψ (mulByNHom t.tateCurve m (xE t.tateCurve)) =
        evalTate t h12 hum (mkT t (C X))
      rw [mulByNHom_x, evalTate_mk_C, eval_X, hX, xNB, map_mul, map_pow, evalCover_aeval,
        evalCover_invPsiNB, hψe, ← ψ_sq_evalEval hE]
      field_simp
  · change evalCover m hu hψ (mulByNHom t.tateCurve m (yE t.tateCurve)) =
        evalTate t h12 hum (mkT t X)
    have hε : evalTate t h12 hu (epsN t.tateCurve m) = if Even (m : ℤ) then 1 else
        2 * t.Y u + t.tateCurve.a₁ * t.X u + t.tateCurve.a₃ := by
      rw [epsN]
      split_ifs
      · exact map_one _
      · rw [psiE_eq', map_add, map_add, map_mul, map_mul, map_ofNat, evalTate_algebraMap,
          evalTate_algebraMap]
        rw [show yE t.tateCurve = mkT t X from rfl, show xE t.tateCurve = mkT t (C X) from rfl,
          evalTate_mk_Y, evalTate_mk_C, eval_X]
    rw [mulByNHom_y, evalTate_mk_Y, hY, yNB, omegaY]
    simp only [map_mul, map_sub, map_add, map_pow, evalCover_algebraMap_K, evalCover_aeval,
      evalCover_invPsiNB, evalCover_algebraMap, psiNB, hε, hψe]
    have hψ' : (t.tateCurve.ψ (m : ℤ)).evalEval (t.X u) (t.Y u) ≠ 0 := hψe ▸ hψ
    field_simp

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `[m]^*` lands in an intermediate field as soon as `[m]^*x` and `[m]^*y` do. -/
theorem mulByNHom_mem_of_xy {S : IntermediateField K (TateField t)}
    (hx : algebraMap _ (TateField t) (mulByNHom t.tateCurve m (xE t.tateCurve)) ∈ S)
    (hy : algebraMap _ (TateField t) (mulByNHom t.tateCurve m (yE t.tateCurve)) ∈ S)
    (a : TateRing t) : algebraMap _ (TateField t) (mulByNHom t.tateCurve m a) ∈ S := by
  let f : TateRing t →ₐ[K] TateField t :=
    (IsScalarTower.toAlgHom K (coverRingN t.tateCurve m) (TateField t)).comp
      (mulByNAlgHom t.tateCurve m)
  have hf : ∀ b, f b = algebraMap _ (TateField t) (mulByNHom t.tateCurve m b) := fun _ => rfl
  have haeval : ∀ p : K[X], f (aeval (xE t.tateCurve) p) ∈ S := fun p => by
    rw [← Polynomial.aeval_algHom_apply]
    induction p using Polynomial.induction_on with
    | C c => simp only [aeval_C]; exact S.algebraMap_mem c
    | add p q hp hq => simp only [map_add]; exact add_mem hp hq
    | monomial n c _ =>
      simpa [map_mul] using mul_mem (S.algebraMap_mem c) (pow_mem ((hf _).symm ▸ hx) (n + 1))
  obtain ⟨p, q, rfl⟩ := CoordinateRing.exists_smul_basis_eq a
  rw [← hf, Algebra.smul_def, Algebra.smul_def, mul_one, map_add, map_mul,
    algebraMap_polynomial_eq_aeval_xE, algebraMap_polynomial_eq_aeval_xE]
  exact add_mem (haeval p) (mul_mem (haeval q) ((hf _).symm ▸ hy))

omit [NeZero m] [t.tateCurve.IsElliptic] in
/-- **G1, step 1: `[2N]^*` of `curves-jacobian` factors through `ψ^*K(E_Q)`.** For even `N`, the
function field `K(x_Q∘ψ, y_Q∘ψ)` of `Ÿ'_N` inside `K(E_q)` (`ψ(u) = u^N`, `Q = s^N`, `s² = q`)
contains `F_N = f_N∘ψ` and the image of `cj`'s multiplication map `[2N]^*`. -/
theorem exists_levelField_mulByN (h2 : ‖(2 : K)‖ = 1) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
    (hN : 0 < N) (T : TateParameter K) (hT : T.q = s ^ N) (hev : Even N) :
    haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
    haveI : NeZero (2 * N) := ⟨by omega⟩
    ∃ (gX gY F : TateField t) (D : TateRing t), D ≠ 0 ∧
      F ∈ IntermediateField.adjoin K ({gX, gY} : Set (TateField t)) ∧
      (∀ a : TateRing t, algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) ∈
        IntermediateField.adjoin K ({gX, gY} : Set (TateField t))) ∧
      ∀ (u : Kˣ) (hu : OffOrbit t u),
        (evalTate t h12 hu D ≠ 0 ↔ T.theta (-(u ^ N)) ≠ 0) ∧
        (T.theta (-(u ^ N)) ≠ 0 →
          HasTateValue t h12 gX hu (T.X (u ^ N)) ∧ HasTateValue t h12 gY hu (T.Y (u ^ N)) ∧
          (etaleTheta (tatePow t N hN) (u ^ N) ≠ 0 →
            HasTateValue t h12 F hu (thetaLevel t N hN (u ^ N)))) := by
  haveI : t.tateCurve.IsElliptic := t.tateCurve_isElliptic h12
  haveI : NeZero (2 * N) := ⟨by omega⟩
  obtain ⟨gX, gY, F, x₂, y₂, D, hD, hF, hx₂, hy₂, hspec⟩ :=
    exists_levelField t hs hN T hT h12 hev
  have hD₀ : D * psiN t.tateCurve (2 * N) ≠ 0 := mul_ne_zero hD (psiN_ne_zero_of_neZero _ _)
  -- the value-defined `x₂, y₂` are `cj`'s `[2N]^*x`, `[2N]^*y`
  have key : ∀ (a : TateRing t) (g : TateField t),
      (∀ (u : Kˣ) (hu : OffOrbit t u) (hum : OffOrbit t (u ^ (2 * N))),
        T.theta (-(u ^ N)) ≠ 0 → HasTateValue t h12 g hu (evalTate t h12 hum a)) →
      g = algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) a) := by
    intro a g hg
    classical
    refine eq_of_hasTateValue (h12 := h12) hD₀
      (G := fun u => if hum : OffOrbit t (u ^ (2 * N)) then evalTate t h12 hum a else 0)
      (fun u hu h0 => ?_) (fun u hu h0 => ?_)
    all_goals
      rw [map_mul] at h0
      obtain ⟨hum, hval⟩ := hasTateValue_mulByNHom (h12 := h12) (2 * N) h2 hu
        (right_ne_zero_of_mul h0)
      simp only [dif_pos hum]
    · exact hg u hu hum ((hspec u hu).1.mp (left_ne_zero_of_mul h0))
    · exact hval a
  have hθ : ∀ (u : Kˣ) (hu : OffOrbit t u) (hum : OffOrbit t (u ^ (2 * N))),
      T.theta (-(u ^ N)) ≠ 0 →
      HasTateValue t h12 x₂ hu (t.X (u ^ (2 * N))) ∧
        HasTateValue t h12 y₂ hu (t.Y (u ^ (2 * N))) := fun u hu hum h0 =>
    ((hspec u hu).2 h0).2.2.2 (theta_neg_ne_zero t hum)
  have ex : x₂ = algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) (xE t.tateCurve)) :=
    key _ _ fun u hu hum h0 => (hθ u hu hum h0).1.congr
      (by rw [show xE t.tateCurve = mkT t (C X) from rfl, evalTate_mk_C, eval_X])
  have ey : y₂ = algebraMap _ (TateField t) (mulByNHom t.tateCurve (2 * N) (yE t.tateCurve)) :=
    key _ _ fun u hu hum h0 => (hθ u hu hum h0).2.congr
      (by rw [show yE t.tateCurve = mkT t X from rfl, evalTate_mk_Y])
  refine ⟨gX, gY, F, D, hD, hF, mulByNHom_mem_of_xy (2 * N) (ex ▸ hx₂) (ey ▸ hy₂),
    fun u hu => ⟨(hspec u hu).1, fun h0 => ?_⟩⟩
  obtain ⟨vX, vY, vF, -⟩ := (hspec u hu).2 h0
  exact ⟨vX, vY, vF⟩

end MulByN

end Iut.EtaleTheta
