/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Global
import Iut.Arakelov.QPilot

/-!
# The wall's global realified Frobenioid degree (roadmap-v2 M1a/M3)

The wall formalisation (`Iut/Wall/`, README) uses "the degree of the pilot objects in the global
realified Frobenioid" through the value-group BPSs `Wall.qVal`, `Wall.thetaVal` (whose pilots
are `|log q|` and `s·|log q|`, `Wall.degTheta_pilot`) and through the log-volumes of the `q`- and
`Θ`-pilot regions (IUT III, Proposition 3.9(iii); `Iut/Arakelov/QPilot.lean`). Here these
numbers are realized as **Frobenioid degrees of objects of the global realified Frobenioid**
`C^⊩` of `K = D.Kt` (`Iut/Frobenioid/Global.lean`):

* `qPilotObj D = (pt, div(q-pilot))` (IUT III, Definition 3.8(i): the `q`-pilot object);
  **`degreeNorm_qPilotObj`**: its normalized degree is `|log q|`
  `= (qVal D.bpsDegrees).pilot` (`degreeNorm_qPilotObj_eq_pilot`), and
  **`logVol_qRegion_eq_neg_degreeNorm`**: `log-vol(q-pilot region) = −deg(q-pilot object)`;
* `thetaPilotObj D = (pt, (1/ℓ*)·Σ_{j=1}^{ℓ*} div(q^{j²}))` (the `Θ`-pilot object, an
  ℝ-divisor, which is why the *realified* Frobenioid is needed); **`degreeNorm_thetaPilotObj`**:
  its degree is `s·|log q|` with `s = (1² + ⋯ + ℓ*²)/ℓ*` (`D.wallS`), equal to the degree of the
  Θ-pilot value-group BPS (`degreeNorm_thetaPilotObj_eq_degTheta`), and
  **`logVol_lgp_eq_neg_degreeNorm`**: `log-vol(LGP·𝒪) = −deg(Θ-pilot object)`;
* the **`ℝ_{>0}`-scalings** `scale c` of `C^⊩` (IUT III, Remark 3.5.1(ii)/IUT I, Example
  3.5: realified Frobenioids carry a natural `ℝ_{>0}`-action) multiply degrees by `c`
  (`degree_scale`); **`scale_thetaPilotObj`**: `scale (1/s)` carries the Θ-pilot object
  *exactly* to the `q`-pilot object, and **`nonempty_iso_scale_iff`**: `scale c (Θ-pilot)` is
  isomorphic to the `q`-pilot object iff `c = 1/s`. In particular
  **`isEmpty_iso_thetaPilot_qPilot`**: the Θ-pilot and `q`-pilot objects are *not* isomorphic in
  `C^⊩` (the Frobenioid-theoretic form of `InitialThetaData.hexagon_not_commutes`: the Θ-link,
  which identifies the two pilot objects, cannot be realized inside one global realified
  Frobenioid, only up to the scaling `1/s`).
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov Wall ArithLineBundle'

universe u

/-! ### Divisors of powers -/

lemma ord_pow {K : Type u} [Field K] [NumberField K] (L : ArithLineBundle K) (m : ℕ)
    (w : FinitePlace K) : (L.pow m).ord w = m * L.ord w := by
  have h := L.finDeg_pow m w
  rw [ArithLineBundle.finDeg_eq_ord, ArithLineBundle.finDeg_eq_ord, ← mul_assoc] at h
  have hl : Real.log (primeNorm w) ≠ 0 := (Real.log_pos (one_lt_primeNorm w)).ne'
  exact_mod_cast mul_right_cancel₀ hl h

lemma toDiv_pow {K : Type u} [Field K] [NumberField K] (L : ArithLineBundle K) (m : ℕ) :
    toDiv (L.pow m) = (m : ℝ) • toDiv L := by
  refine Prod.ext (Finsupp.ext fun w => ?_) (funext fun v => ?_)
  · simp [ord_pow]
  · simp only [toDiv_snd_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    rw [show (L.pow m).inf v = L.inf v ^ m from rfl, Real.log_pow]
    ring

/-! ### Scalings of the global realified Frobenioid -/

namespace GlobalRealified

variable {K : Type u} [Field K] [NumberField K]

/-- **The `ℝ_{>0}`-scaling** `c` of the global realified Frobenioid: `(A, α) ↦ (A, c·α)`,
`(n, f, Z, u) ↦ (n, f, c·Z, c·u)`. -/
noncomputable def scale (c : ℝ) (hc : 0 < c) : GlobalRealified K ⥤ GlobalRealified K where
  obj X := ⟨X.base, c • X.α⟩
  map {X Y} φ :=
    { deg := φ.deg
      base := φ.base
      div := c • φ.div
      div_mem := ⟨fun w => by simpa using mul_nonneg hc.le (φ.div_mem.1 w),
        fun v => by simpa using mul_nonneg hc.le (φ.div_mem.2 v)⟩
      u := c • φ.u
      rel := by
        have h := congrArg (c • ·) φ.rel
        simp only [smul_add] at h
        change (φ.deg : ℕ) • (c • X.α) + c • φ.div = c • Y.α + c • (φ.u : ArithDiv K)
        rw [smul_comm]
        exact h }
  map_id X := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · change c • (0 : ArithDiv K) = 0
      simp
    · exact Subtype.ext (by change c • (0 : ArithDiv K) = 0; simp)
  map_comp φ ψ := by
    refine Model.hom_ext rfl rfl ?_ ?_
    · change c • (ψ.div + (ψ.deg : ℕ) • φ.div) = c • ψ.div + (ψ.deg : ℕ) • (c • φ.div)
      rw [smul_add, smul_comm]
    · refine Subtype.ext ?_
      change c • ((ψ.u : ArithDiv K) + (ψ.deg : ℕ) • (φ.u : ArithDiv K)) =
        c • (ψ.u : ArithDiv K) + (ψ.deg : ℕ) • (c • (φ.u : ArithDiv K))
      rw [smul_add, smul_comm]

@[simp] lemma scale_obj_α (c : ℝ) (hc : 0 < c) (X : GlobalRealified K) :
    ((scale c hc).obj X).α = c • X.α := rfl

/-- **Scalings multiply degrees**: `deg(c·X) = c·deg(X)`. -/
theorem degree_scale (c : ℝ) (hc : 0 < c) (X : GlobalRealified K) :
    ((scale c hc).obj X).degree = c * X.degree := by
  change degArith K (c • X.α) = c * degArith K X.α
  rw [map_smul, smul_eq_mul]

theorem degreeNorm_scale (c : ℝ) (hc : 0 < c) (X : GlobalRealified K) :
    ((scale c hc).obj X).degreeNorm = c * X.degreeNorm := by
  rw [degreeNorm, degreeNorm, degree_scale, mul_div_assoc]

lemma degreeNorm_mk (x : ArithDiv K) :
    GlobalRealified.degreeNorm (⟨pt, x⟩ : GlobalRealified K) =
      degArith K x / Module.finrank ℚ K := rfl

end GlobalRealified

open GlobalRealified

/-! ### The pilot objects -/

variable (D : InitialThetaData.{0})

/-- **The `q`-pilot object** of the global realified Frobenioid of `K = D.Kt` (IUT III,
Definition 3.8(i)). -/
noncomputable def qPilotObj : GlobalRealified D.Kt := ofBundle (qPilotBundle D)

/-- **The `Θ`-pilot object**: the ℝ-divisor `(1/ℓ*)·Σ_{j=1}^{ℓ*} div(q^{j²})` (the capsule average
of the divisors of the theta values, IUT III, Proposition 3.4 and Corollary 3.12). -/
noncomputable def thetaPilotObj : GlobalRealified D.Kt :=
  ⟨pt, ((nC D : ℝ))⁻¹ • ∑ i : Fin (nC D), toDiv (thetaBundle D (i.1 + 1))⟩

/-- **The degree of the `q`-pilot object is `|log q|`.** -/
theorem degreeNorm_qPilotObj : (qPilotObj D).degreeNorm = D.qPilot.absLogQ := by
  rw [qPilotObj, degreeNorm_ofBundle, degNorm_qPilotBundle]

/-- The degree of the `q`-pilot object is the pilot of the `q`-pilot value-group BPS. -/
theorem degreeNorm_qPilotObj_eq_pilot :
    (qPilotObj D).degreeNorm = (qVal D.bpsDegrees).pilot := by
  rw [degreeNorm_qPilotObj, InitialThetaData.pilot_qVal]

/-- **IUT III, Proposition 3.9(iii) for the `q`-pilot object**: `log-vol(q-pilot region) =
−deg(q-pilot object)` (`= (qPilot D).lhs`, the left-hand side of the Corollary 3.12 variant). -/
theorem logVol_qRegion_eq_neg_degreeNorm :
    logVol D (qRegion D) = -(qPilotObj D).degreeNorm := by
  rw [(logVol_qRegion_eq_neg_degNorm D).1, qPilotObj, degreeNorm_ofBundle]

lemma nC_pos : 0 < nC D := by
  have := D.two_le_ellStar
  change 0 < (D.ℓ - 1) / 2
  omega

lemma degreeNorm_thetaPilotObj_sum :
    (thetaPilotObj D).degreeNorm =
      ((nC D : ℝ))⁻¹ * ∑ i : Fin (nC D), (thetaBundle D (i.1 + 1)).degNorm := by
  rw [thetaPilotObj, degreeNorm_mk, map_smul, map_sum, smul_eq_mul, mul_div_assoc,
    Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [degArith_toDiv, ArithLineBundle.degNorm]

/-- **The degree of the `Θ`-pilot object is `s·|log q|`**, `s = (1² + ⋯ + ℓ*²)/ℓ*`. -/
theorem degreeNorm_thetaPilotObj :
    (thetaPilotObj D).degreeNorm = D.wallS * D.qPilot.absLogQ := by
  rw [degreeNorm_thetaPilotObj_sum]
  simp only [degNorm_thetaBundle]
  rw [← Finset.sum_mul, InitialThetaData.wallS, sFactor, Fin.sum_univ_eq_sum_range
    (fun j => ((j + 1 : ℕ) : ℝ) ^ 2)]
  push_cast
  ring

/-- The degree of the `Θ`-pilot object is the degree of the pilot of the Θ-pilot value-group BPS
(`Wall.degTheta_pilot`). -/
theorem degreeNorm_thetaPilotObj_eq_degTheta :
    (thetaPilotObj D).degreeNorm =
      degTheta D.bpsDegrees D.wallS_ne_zero (InitialThetaData.thetaValD D).pilot := by
  rw [degreeNorm_thetaPilotObj, degTheta_pilot, ← qVal_pilot, InitialThetaData.pilot_qVal]

/-- **IUT III, Proposition 3.9(iii) for the `Θ`-pilot object**:
`log-vol(LGP·𝒪) = −deg(Θ-pilot object)`. -/
theorem logVol_lgp_eq_neg_degreeNorm :
    logVol D (lgp D (integralRegion D)) = -(thetaPilotObj D).degreeNorm := by
  rw [(logVol_lgp_integral_eq_degNorm D).1, degreeNorm_thetaPilotObj_sum]
  ring

/-! ### The Θ-pilot and `q`-pilot objects differ by the scaling `1/s` -/

lemma thetaBundle_toDiv (j : ℕ) :
    toDiv (thetaBundle D j) = ((j ^ 2 : ℕ) : ℝ) • toDiv (qPilotBundle D) := by
  rw [← toDiv_pow]
  refine toDiv_congr _ _ (fun w => ?_) (fun v => ?_)
  · change ‖D.qroot w ^ (j ^ 2)‖ = ‖(D.qroot w ^ 1) ^ (j ^ 2)‖
    rw [pow_one]
  · change (1 : ℝ) = 1 ^ (j ^ 2)
    rw [one_pow]

lemma thetaPilotObj_α : (thetaPilotObj D).α = D.wallS • (qPilotObj D).α := by
  change ((nC D : ℝ))⁻¹ • ∑ i : Fin (nC D), toDiv (thetaBundle D (i.1 + 1)) =
    D.wallS • toDiv (qPilotBundle D)
  simp only [thetaBundle_toDiv, ← Finset.sum_smul, smul_smul]
  congr 1
  rw [InitialThetaData.wallS, sFactor, Fin.sum_univ_eq_sum_range
    (fun j => (((j + 1) ^ 2 : ℕ) : ℝ))]
  push_cast
  ring

lemma wallS_pos : 0 < D.wallS := zero_lt_one.trans D.one_lt_wallS

/-- **The scaling `1/s` carries the `Θ`-pilot object to the `q`-pilot object** (on the nose). -/
theorem scale_thetaPilotObj :
    (scale (D.wallS)⁻¹ (inv_pos.mpr (wallS_pos D))).obj (thetaPilotObj D) = qPilotObj D := by
  change (⟨pt, (D.wallS)⁻¹ • (thetaPilotObj D).α⟩ : GlobalRealified D.Kt) = ⟨pt, _⟩
  rw [thetaPilotObj_α, smul_smul, inv_mul_cancel₀ (wallS_pos D).ne', one_smul]
  rfl

lemma absLogQ_pos : 0 < D.qPilot.absLogQ := by
  have := D.lhs_neg
  rw [QPilotData.lhs] at this
  linarith

/-- **The scalings carrying the `Θ`-pilot object to (an object isomorphic to) the `q`-pilot
object are exactly `c = 1/s`.** -/
theorem nonempty_iso_scale_iff (c : ℝ) (hc : 0 < c) :
    Nonempty ((scale c hc).obj (thetaPilotObj D) ≅ qPilotObj D) ↔ c = (D.wallS)⁻¹ := by
  constructor
  · rintro ⟨e⟩
    have h := congrArg (· / (Module.finrank ℚ D.Kt : ℝ)) (degree_eq_of_iso e)
    change ((scale c hc).obj (thetaPilotObj D)).degreeNorm = (qPilotObj D).degreeNorm at h
    rw [degreeNorm_scale, degreeNorm_thetaPilotObj, degreeNorm_qPilotObj] at h
    have hq := (absLogQ_pos D).ne'
    have hs := (wallS_pos D).ne'
    field_simp at h
    exact eq_inv_of_mul_eq_one_left (by linarith [h])
  · rintro rfl
    rw [scale_thetaPilotObj]
    exact ⟨Iso.refl _⟩

/-- **The `Θ`-pilot and `q`-pilot objects are not isomorphic** in the global realified
Frobenioid (`s ≠ 1`): the Frobenioid form of `InitialThetaData.hexagon_not_commutes`. -/
theorem isEmpty_iso_thetaPilot_qPilot : IsEmpty (thetaPilotObj D ≅ qPilotObj D) := by
  refine ⟨fun e => ?_⟩
  have h := (nonempty_iso_scale_iff D 1 one_pos).mp ⟨(eqToIso (by
    change (⟨pt, (1 : ℝ) • (thetaPilotObj D).α⟩ : GlobalRealified D.Kt) = thetaPilotObj D
    rw [one_smul])) ≪≫ e⟩
  have := D.one_lt_wallS
  rw [eq_comm, inv_eq_one] at h
  linarith

end Frobenioid

end Iut
