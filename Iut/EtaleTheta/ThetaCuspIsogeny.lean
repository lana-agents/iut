/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaCuspOrder

/-!
# Invariance of the element `X_q(Ü²)` of `K(E_Q)` (MR14)

For `R = (P₁ + y Q₁)/(P₂ + y Q₂) ∈ K(E_T)` with the values `X_q(u²)` of
`exists_poly_isogenyX_deg` (`T.q = s^N`, `s² = q`):

* `negT_R_eq`: `[-1]^* R = R` (`X_q(u⁻²) = X_q(u²)`);
* `transT_R_eq`: `R` is invariant under translation by the Tate point of `w` whenever
  `w² ∈ qᶻ` (`X_q(q^k u²) = X_q(u²)`).
-/

open Polynomial

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter WeierstrassCurve.Affine

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- `X(qⁿ·u) = X(u)` for `n : ℤ`. -/
theorem X_zpow_mul (t : TateParameter K) (n : ℤ) (u : Kˣ) : t.X (t.q ^ n * u) = t.X u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ n ih => rw [zpow_add_one, mul_comm _ t.q, mul_assoc, t.X_q_smul, ih]
  | pred n ih =>
    rw [← ih, show t.q ^ (-(n : ℤ)) * u = t.q * (t.q ^ (-(n : ℤ) - 1) * u) by
      rw [← mul_assoc, ← zpow_one_add]; ring_nf, t.X_q_smul]

/-- The polynomial whose roots are the `X_T`-values of the `u` with `u² ∈ qᶻ` (`T.q = s^N`,
`s² = q`): the values `X_T(±s^a)`, `0 ≤ a < N`. -/
def badPoly (T : TateParameter K) (s : Kˣ) (N : ℕ) : K[X] :=
  ∏ a ∈ Finset.range N,
    (Polynomial.X - C (T.X (s ^ a))) * (Polynomial.X - C (T.X (-(s ^ a))))

section Bad

variable {t : TateParameter K} {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ} (hN : 0 < N)
  {T : TateParameter K} (hT : T.q = s ^ N)

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem badPoly_ne_zero : badPoly T s N ≠ 0 :=
  (monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).mul (monic_X_sub_C _)).ne_zero

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hN hT in
/-- If `u² ∈ qᶻ` then `X_T(u)` is a root of `badPoly`. -/
theorem badPoly_eval_eq_zero {u : Kˣ} (hu : ¬ OffOrbit t (u ^ 2)) :
    (badPoly T s N).eval (T.X u) = 0 := by
  simp only [OffOrbit, not_forall, not_not] at hu
  obtain ⟨n, hn⟩ := hu
  have hx : (((s ^ n * u : Kˣ) : K)) ^ 2 = 1 := by
    rw [← hn, ← hs]
    push_cast
    rw [mul_pow, ← zpow_natCast ((s : K) ^ n) 2, ← zpow_mul, ← zpow_natCast (s : K) 2, ← zpow_mul,
      mul_comm n]
  obtain ⟨ε, hε, hεu⟩ : ∃ ε : Kˣ, (ε = 1 ∨ ε = -1) ∧ u = ε * s ^ (-n) := by
    refine ⟨s ^ n * u, ?_, by
      rw [mul_comm (s ^ n) u, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]⟩
    rcases (mul_self_eq_one_iff (a := ((s ^ n * u : Kˣ) : K))).mp (by rw [← sq]; exact hx) with
      h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  set a := (-n % N).toNat with ha
  have ha' : ((a : ℕ) : ℤ) = -n % N := Int.toNat_of_nonneg (Int.emod_nonneg _ hN'.ne')
  have haN : a < N := by
    have := Int.emod_lt_of_pos (-n) hN'
    omega
  have hu' : u = T.q ^ (-n / N) * (ε * s ^ a) := by
    have e : s ^ (-n) = s ^ a * T.q ^ (-n / N) := by
      rw [hT, ← zpow_natCast s a, ha', ← zpow_natCast s N, ← zpow_mul, ← zpow_add,
        Int.emod_add_mul_ediv]
    rw [hεu, e]
    ac_rfl
  rw [hu', X_zpow_mul, badPoly, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr haN) ?_
  rcases hε with rfl | rfl
  · simp
  · simp

end Bad

section Main

variable {t T : TateParameter K} {s : Kˣ} {N : ℕ} {h12 : (12 : K) ≠ 0} {P₁ Q₁ P₂ Q₂ : K[X]}

theorem mkT_C_ne_zero (h12 : (12 : K) ≠ 0) {p : K[X]}
    (hp : p ≠ 0) : mkT T (C p) ≠ 0 := by
  intro h
  apply hp
  exact (poly_eq_zero_of_eval T h12 p 0 fun u hu => by
    have := congrArg (evalTate T h12 hu) h
    rw [evalTate_mk_C, map_zero] at this
    simp [this]).1

/-- The value of `R = (P₁ + y Q₁)/(P₂ + y Q₂)` at `u` (with `u² ∉ qᶻ`) is `X_q(u²)`. -/
theorem hasTateValue_R
    (hR : ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)))
    {u : Kˣ} (hu : OffOrbit T u) (hu2 : OffOrbit t (u ^ 2)) :
    HasTateValue T h12 (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) hu (t.X (u ^ 2)) := by
  obtain ⟨hd, he⟩ := hR u hu (theta_neg_ne_zero t hu2)
  refine ((HasTateValue.ofRing hu _).div (HasTateValue.ofRing hu _)
    (by rwa [evalTate_polyXY])).congr ?_
  rw [evalTate_polyXY, evalTate_polyXY, he]

variable (hs : s ^ 2 = t.q) (hN : 0 < N) (hT : T.q = s ^ N)

include hs hN hT in
/-- **`[-1]^*` fixes `R = X_q(Ü²)`.** -/
theorem negT_R_eq (h12 : (12 : K) ≠ 0)
    (hR : ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v))) :
    negT T (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
    algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂) := by
  have good : ∀ (u : Kˣ) (hu : OffOrbit T u),
      evalTate T h12 hu (mkT T (C (badPoly T s N))) ≠ 0 → OffOrbit t (u ^ 2) := by
    intro u hu h0
    by_contra h
    exact h0 (by rw [evalTate_mk_C]; exact badPoly_eval_eq_zero hs hN hT h)
  refine eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 badPoly_ne_zero)
    (G := fun u => t.X (u ^ 2)) (fun u hu h0 => ?_) (fun u hu h0 => hasTateValue_R hR hu
      (good u hu h0))
  have hu2 := good u hu h0
  have hi : OffOrbit t (u⁻¹ ^ 2) := by rw [inv_pow]; exact offOrbit_inv t hu2
  exact hasTateValue_negY hu ((hasTateValue_R hR (offOrbit_inv T hu) hi).congr
    (by rw [inv_pow, t.X_inv hu2]))

include hs hN hT in
/-- **Translation by a Tate point `w` with `w² ∈ qᶻ` fixes `R = X_q(Ü²)`.** -/
theorem transT_R_eq (h2 : ‖(2 : K)‖ = 1)
    (hR : ∀ v : Kˣ, OffOrbit T v → t.theta (-(v ^ 2)) ≠ 0 →
      P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v) ≠ 0 ∧
      t.X (v ^ 2) = (P₁.eval (T.X v) + T.Y v * Q₁.eval (T.X v)) /
        (P₂.eval (T.X v) + T.Y v * Q₂.eval (T.X v)))
    {w : Kˣ} (hw : OffOrbit T w) (hk : ∃ k : ℤ, (w : K) ^ 2 = (t.q : K) ^ k) :
    transT h12 hw (algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂)) =
    algebraMap _ (TateField T) (polyXY T P₁ Q₁) /
      algebraMap _ (TateField T) (polyXY T P₂ Q₂) := by
  obtain ⟨k, hk⟩ := hk
  have hq : (t.q : K) ≠ 0 := t.q.ne_zero
  have hD : badPoly T s N * (Polynomial.X - C (T.X w)) ≠ 0 :=
    mul_ne_zero badPoly_ne_zero (X_sub_C_ne_zero _)
  have good : ∀ (u : Kˣ) (hu : OffOrbit T u),
      evalTate T h12 hu (mkT T (C (badPoly T s N * (Polynomial.X - C (T.X w))))) ≠ 0 →
      OffOrbit t (u ^ 2) ∧ T.X u ≠ T.X w := by
    intro u hu h0
    rw [evalTate_mk_C, eval_mul, eval_sub, eval_X, eval_C] at h0
    obtain ⟨h0a, h0b⟩ := mul_ne_zero_iff.mp h0
    refine ⟨?_, sub_ne_zero.mp h0b⟩
    by_contra h
    exact h0a (badPoly_eval_eq_zero hs hN hT h)
  refine eq_of_hasTateValue (h12 := h12) (mkT_C_ne_zero h12 hD)
    (G := fun u => t.X (u ^ 2)) (fun u hu h0 => ?_) (fun u hu h0 => hasTateValue_R hR hu
      (good u hu h0).1)
  obtain ⟨hu2, hx⟩ := good u hu h0
  have huw : OffOrbit T (u * w) := by
    intro n hn
    apply hx
    have e : u = T.q ^ (-n) * w⁻¹ := by
      apply Units.ext
      push_cast at hn ⊢
      have hw0 : (w : K) ≠ 0 := w.ne_zero
      have hT0 : (T.q : K) ≠ 0 := T.q.ne_zero
      rw [zpow_neg]
      field_simp
      linear_combination hn
    rw [e, X_zpow_mul, T.X_inv hw]
  have huw2 : OffOrbit t ((u * w) ^ 2) := by
    intro n hn
    apply hu2 (n + k)
    push_cast at hn ⊢
    rw [zpow_add₀ hq, ← hn, mul_pow, hk]
    ring
  have e2 : (u * w) ^ 2 = t.q ^ k * u ^ 2 :=
    Units.ext (by push_cast; rw [mul_pow, hk]; ring)
  exact hasTateValue_trans h2 hu hw huw hx _ _
    ((hasTateValue_R hR huw huw2).congr (by rw [e2, X_zpow_mul]))

end Main

end Iut.EtaleTheta
