/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.EllTateAn

/-!
# The scalings fixing `K(E_t)` and `K(X')` inside `Mero K` (MR18 T7c)

[EtTh] = S. Mochizuki, *The étale theta function and its Frobenioid-theoretic manifestations*
(text `~/iut-scratch/wall/txt/The Etale Theta Function …txt`, cited by line).

`TateMero`/`EllTateAn` embed the function field of the Tate curve `E_t` into the meromorphic
functions on `Ÿ_∞ = 𝔾_m^an` (`tateFieldHom`: `x ↦ x(Ü²)`, `y ↦ y(Ü²)`) and show that every
deck transformation `Ü ↦ c·Ü`, `c ∈ Deck t` (`c² ∈ q^ℤ`), fixes it, and that `Ü ↦ s^k·Ü`
fixes the Kummer function `√(x - e)` (`kumM`). This file proves the converses, so that the
two groups are exactly the scaling automorphisms of `𝔾_m^an` over `E_t` and over
`X' = E_t(√(x - e))`:

* `X_mul_eq_of_scale_xU`, `Y_mul_eq_of_scale_yU`: if `U ↦ C·U` fixes `x(U)` (`y(U)`), then
  `X(C·u) = X(u)` (`Y(C·u) = Y(u)`) at the Tate points;
* **`mem_qpowers_of_scale_xU_yU`**: if `U ↦ C·U` fixes `x(U)` and `y(U)` then `C ∈ q^ℤ`
  (tate-curves-theta `class_eq_or_inv_of_X_eq`; the inverse class is excluded by `y`, since
  `2y + x ≠ 0` in `K[E_t]`, `Y_inv`);
* **`mem_deck_of_scale_xM_yM`**, **`scale_comp_tateFieldHom_iff`**: `Ü ↦ c·Ü` fixes `K(E_t)`
  (equivalently `x(Ü²)` and `y(Ü²)`) iff `c ∈ Deck t`: **`Deck t = Aut(𝔾_m^an / E_t)` among the
  scalings**;
* `kumM_ne_zero`; **`mem_zpowers_of_scale_kumM`**, **`scale_fix_X'_iff`**: `Ü ↦ c·Ü` fixes
  `K(E_t)` and `√(x - e)` iff `c ∈ s^ℤ`: **`s^ℤ = Aut(𝔾_m^an / X')` among the scalings**
  (`Deck t = s^ℤ × {±1}`, `eq_or_eq_neg_of_cusp`, and `Ü ↦ -Ü` negates `√(x - e)`).

These are statements about scalings only; that every automorphism of `𝔾_m^an` over `E_t` is a
scaling (the analytic covering theory of `𝔾_m^an → E_t`) is not formalised.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace Iut.Frobenioid.BAn

open TateCurvesTheta TateParameter Polynomial Iut.EtaleTheta

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  (t : TateParameter K)

/-! ### Values of a scaling-invariant quotient -/

lemma Mero.const_two : Mero.const (2 : K) = 2 := by
  simp only [Mero.const, map_ofNat]

/-- If `U ↦ C·U` fixes `a/b`, then `a(C·u)·b(u) = a(u)·b(C·u)`. -/
lemma Mero.apply_of_scale_div {C : Kˣ} {a b : Entire K} (hb : b ≠ 0)
    (h : Mero.scale C (Mero.ofE a / Mero.ofE b) = Mero.ofE a / Mero.ofE b) (u : Kˣ) :
    (a : Kˣ → K) (C * u) * (b : Kˣ → K) u = (a : Kˣ → K) u * (b : Kˣ → K) (C * u) := by
  rw [Mero.scale_div, div_eq_div_iff (Mero.ofE_ne_zero (Mero.entire_scale_ne_zero C hb))
    (Mero.ofE_ne_zero hb), ← Mero.ofE_mul, ← Mero.ofE_mul] at h
  have e := congrArg (fun f : Entire K => (f : Kˣ → K) u) (Mero.ofE_injective h)
  simp only [Entire.coe_mul_apply, Entire.coe_scale] at e
  exact e

/-- If `U ↦ C·U` fixes `x(U)`, then `X(C·u) = X(u)` at the Tate points. -/
lemma X_mul_eq_of_scale_xU {C : Kˣ} (h : Mero.scale C (xU t) = xU t) {u : Kˣ}
    (hu : OffOrbit t u) (hCu : OffOrbit t (C * u)) : t.X (C * u) = t.X u := by
  rw [xU, ← Mero.ofE_pow] at h
  have e := Mero.apply_of_scale_div (pow_ne_zero 2 (thetaE_ne_zero t)) h u
  rw [Entire.coe_pow_apply, Entire.coe_pow_apply, xThetaE_apply t hu, xThetaE_apply t hCu,
    thetaE_apply, thetaE_apply] at e
  have h0 : t.theta (-(C * u)) ^ 2 * t.theta (-u) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (t.theta_neg_ne_zero hCu)) (pow_ne_zero _ (t.theta_neg_ne_zero hu))
  have e' : (t.X (C * u) - t.X u) * (t.theta (-(C * u)) ^ 2 * t.theta (-u) ^ 2) = 0 := by
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right h0)

/-- If `U ↦ C·U` fixes `y(U)`, then `Y(C·u) = Y(u)` at the Tate points. -/
lemma Y_mul_eq_of_scale_yU {C : Kˣ} (h : Mero.scale C (yU t) = yU t) {u : Kˣ}
    (hu : OffOrbit t u) (hCu : OffOrbit t (C * u)) : t.Y (C * u) = t.Y u := by
  rw [yU, ← Mero.ofE_pow] at h
  have e := Mero.apply_of_scale_div (pow_ne_zero 3 (thetaE_ne_zero t)) h u
  rw [Entire.coe_pow_apply, Entire.coe_pow_apply, yThetaE_apply t hu, yThetaE_apply t hCu,
    thetaE_apply, thetaE_apply] at e
  have h0 : t.theta (-(C * u)) ^ 3 * t.theta (-u) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (t.theta_neg_ne_zero hCu)) (pow_ne_zero _ (t.theta_neg_ne_zero hu))
  have e' : (t.Y (C * u) - t.Y u) * (t.theta (-(C * u)) ^ 3 * t.theta (-u) ^ 3) = 0 := by
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e').resolve_right h0)

/-- `Y(q^k·v) = Y(v)`. -/
lemma Y_zpow_mul (k : ℤ) (v : Kˣ) : t.Y (t.q ^ k * v) = t.Y v := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ k ih => rw [zpow_add_one, mul_comm (t.q ^ (k : ℤ)) t.q, mul_assoc, t.Y_q_smul, ih]
  | pred k ih =>
    rw [← ih, ← t.Y_q_smul (t.q ^ (-(k : ℤ) - 1) * v), ← mul_assoc, ← zpow_one_add]
    congr 3
    ring

/-- `θ(-v) = 0` on the orbit `q^ℤ`. -/
lemma theta_neg_eq_zero_of_not_offOrbit {v : Kˣ} (hv : ¬ OffOrbit t v) : t.theta (-v) = 0 := by
  simp only [OffOrbit, not_forall, not_not] at hv
  obtain ⟨n, hn⟩ := hv
  refine (t.theta_eq_zero_iff _).mpr ⟨-n, ?_⟩
  rw [Units.val_neg, zpow_neg, neg_inj]
  have hq : (t.q : K) ^ n ≠ 0 := zpow_ne_zero _ t.q.ne_zero
  field_simp
  linear_combination hn

/-- `2y + x ≠ 0` in `K[E_t]`. -/
lemma two_y_add_x_ne_zero (h12 : (12 : K) ≠ 0) :
    (2 : TateRing t) * mkT t Polynomial.X + mkT t (C Polynomial.X) ≠ 0 := by
  intro h
  have h2 : (2 : K) ≠ 0 := fun h2 => h12 (by linear_combination 6 * h2)
  have e : (Polynomial.X : K[X]) • (1 : TateRing t) + (C 2 : K[X]) • mkT t Polynomial.X = 0 := by
    rw [WeierstrassCurve.Affine.CoordinateRing.smul, WeierstrassCurve.Affine.CoordinateRing.smul,
      mul_one, ← h, add_comm]
    congr 1
  have := (WeierstrassCurve.Affine.CoordinateRing.smul_basis_eq_zero e).2
  exact h2 (Polynomial.C_eq_zero.mp this)

/-! ### `C ∈ q^ℤ` from the invariance of `x(U)`, `y(U)` -/

/-- **If `U ↦ C·U` fixes `x(U)` and `y(U)`, then `C ∈ q^ℤ`.** -/
theorem mem_qpowers_of_scale_xU_yU (h12 : (12 : K) ≠ 0) {C : Kˣ}
    (hx : Mero.scale C (xU t) = xU t) (hy : Mero.scale C (yU t) = yU t) :
    ∃ k : ℤ, (C : K) = (t.q : K) ^ k := by
  by_contra hC
  -- at every Tate point `u` with `C·u` a Tate point, `u` is `2`-torsion
  have htor : ∀ u : Kˣ, OffOrbit t u → OffOrbit t (C * u) → 2 * t.Y u + t.X u = 0 := by
    intro u hu hCu
    rcases t.class_eq_or_inv_of_X_eq hCu hu (X_mul_eq_of_scale_xU t hx hu hCu) with
      ⟨k, hk⟩ | ⟨k, hk⟩
    · refine absurd ⟨k, ?_⟩ hC
      rw [Units.val_mul] at hk
      exact mul_right_cancel₀ u.ne_zero hk
    · have hCu' : C * u = t.q ^ k * u⁻¹ := Units.ext (by
        rw [hk, Units.val_mul, Units.val_zpow_eq_zpow_val])
      have hY := Y_mul_eq_of_scale_yU t hy hu hCu
      rw [hCu', Y_zpow_mul, t.Y_inv hu] at hY
      linear_combination -hY
  -- hence `2y + x` vanishes in `Mero K`
  obtain ⟨k, H, eH, hH⟩ := ((HasVals.const (t := t) 2).mul (hasVals_yU t)).add (hasVals_xU t)
  have hH0 : H * Entire.scale C (thetaE t) = 0 := by
    refine Entire.eq_zero_of_offOrbit t fun u hu => ?_
    rw [Entire.coe_mul_apply, Entire.coe_scale]
    by_cases hCu : OffOrbit t (C * u)
    · rw [hH u hu]; simp only [htor u hu hCu, mul_zero, zero_mul]
    · rw [thetaE_apply, theta_neg_eq_zero_of_not_offOrbit t hCu, mul_zero]
  have hH1 : H = 0 :=
    (mul_eq_zero.mp hH0).resolve_right (Mero.entire_scale_ne_zero C (thetaE_ne_zero t))
  rw [hH1, Mero.ofE_zero] at eH
  have hf : Mero.const 2 * yU t + xU t = 0 :=
    (mul_eq_zero.mp eH).resolve_left (pow_ne_zero _ (ofE_thetaE_ne_zero t))
  refine two_y_add_x_ne_zero t h12 (tateRingHomU_injective t h12 ?_)
  rw [map_add, map_mul, map_ofNat, tateRingHomU_mk_Y, tateRingHomU_mk_C, eval₂_X, map_zero, ← hf]
  congr 1
  rw [Mero.const_two]

/-! ### `Deck t` and `s^ℤ` as stabilisers -/

/-- **If `Ü ↦ c·Ü` fixes `x(Ü²)` and `y(Ü²)`, then `c ∈ Deck t`.** -/
theorem mem_deck_of_scale_xM_yM (h12 : (12 : K) ≠ 0) {c : Kˣ}
    (hx : Mero.scale c (xM t) = xM t) (hy : Mero.scale c (yM t) = yM t) : c ∈ Deck t := by
  rw [xM, Mero.scale_sq] at hx
  rw [yM, Mero.scale_sq] at hy
  obtain ⟨k, hk⟩ := mem_qpowers_of_scale_xU_yU t h12 (Mero.sq_injective hx) (Mero.sq_injective hy)
  exact ⟨k, by rw [← hk, Units.val_pow_eq_pow_val]⟩

/-- **`Deck t` is the group of scalings fixing `K(E_t)`**: `Ü ↦ c·Ü` fixes the image of the
function field of `E_t` in `Mero K` iff `c ∈ Deck t` ([EtTh] Prop 1.4(ii), l.1325–1328). -/
theorem scale_comp_tateFieldHom_iff (h12 : (12 : K) ≠ 0) (c : Kˣ) :
    (Mero.scale c).comp (tateFieldHom t h12) = tateFieldHom t h12 ↔ c ∈ Deck t := by
  refine ⟨fun h => ?_, fun hc => scale_comp_tateFieldHom (t := t) h12 ⟨c, hc⟩⟩
  have hx := RingHom.congr_fun h (algebraMap (TateRing t) (TateField t) (mkT t (C Polynomial.X)))
  have hy := RingHom.congr_fun h (algebraMap (TateRing t) (TateField t) (mkT t Polynomial.X))
  simp only [RingHom.coe_comp, Function.comp_apply, tateFieldHom_algebraMap, tateRingHom_x,
    tateRingHom_y] at hx hy
  exact mem_deck_of_scale_xM_yM t h12 hx hy

lemma thetaSE_ne_zero (s : Kˣ) : thetaSE t s ≠ 0 := fun h => by
  obtain ⟨w, hw⟩ := offOrbit_exists t
  have e := thetaSE_apply t s (s * w)
  rw [h, Entire.coe_zero_apply, show (-s⁻¹ * (s * w) : Kˣ) = -w by
    ext; simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]; field_simp] at e
  exact t.theta_neg_ne_zero hw e.symm

/-- The Kummer function `√(x - e)` is nonzero. -/
lemma kumM_ne_zero (s : Kˣ) : kumM t s ≠ 0 := by
  rw [kumM]
  refine div_ne_zero (Mero.ofE_ne_zero fun h => thetaSE_ne_zero t s ?_)
    (Mero.ofE_ne_zero (kumDen_ne_zero t))
  exact Entire.sqHom_injective (h.trans (map_zero Entire.sqHom).symm)

/-- **A deck transformation fixing `√(x - e)` lies in `s^ℤ`** (`Deck t = ±s^ℤ` and `Ü ↦ -Ü`
negates `√(x - e)`). -/
theorem mem_zpowers_of_scale_kumM (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q)
    {c : Kˣ} (hc : c ∈ Deck t) (hk : Mero.scale c (kumM t s) = kumM t s) :
    c ∈ Subgroup.zpowers s := by
  obtain ⟨k, hck⟩ := hc
  rcases eq_or_eq_neg_of_cusp hs hck with h | h
  · exact ⟨k, h.symm⟩
  · exfalso
    have h2 : (2 : K) ≠ 0 := fun h2 => h12 (by linear_combination 6 * h2)
    have hneg : Mero.scale c (kumM t s) = -kumM t s := by
      rw [h, show (-(s ^ k) : Kˣ) = s ^ k * (-1) by rw [mul_neg_one], Mero.scale_mul_apply,
        scale_zpow_s_kumM t hs, scale_neg_one_kumM]
    have h0 : (2 : Mero K) * kumM t s = 0 := by linear_combination -(hneg.symm.trans hk)
    refine kumM_ne_zero t s ((mul_eq_zero.mp h0).resolve_left ?_)
    rw [← Mero.const_two]
    exact Mero.const_ne_zero h2

/-- **`s^ℤ` is the group of scalings fixing `K(X') = K(E_t)(√(x - e))`**: `Ü ↦ c·Ü` fixes the
image of `K(E_t)` and the Kummer function `√(x - e)` iff `c ∈ s^ℤ`. -/
theorem scale_fix_X'_iff (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : (s : K) ^ 2 = t.q) (c : Kˣ) :
    ((Mero.scale c).comp (tateFieldHom t h12) = tateFieldHom t h12 ∧
        Mero.scale c (kumM t s) = kumM t s) ↔ c ∈ Subgroup.zpowers s := by
  refine ⟨fun ⟨hE, hk⟩ => mem_zpowers_of_scale_kumM t h12 hs
    ((scale_comp_tateFieldHom_iff t h12 c).mp hE) hk, ?_⟩
  rintro ⟨k, rfl⟩
  refine ⟨(scale_comp_tateFieldHom_iff t h12 _).mpr ?_, scale_zpow_s_kumM t hs k⟩
  exact (Deck t).zpow_mem (Deck.gen t hs).2 k

end Iut.Frobenioid.BAn
