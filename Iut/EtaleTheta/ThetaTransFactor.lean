/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaIsogeny

/-!
# The translation factor of `Θ̈_{q^N}` inside `K(E_q)` (MR14, translation formula (F2))

Let `s² = q`, `Q = s^N` (the lattice `Q^ℤ` of `T`), `ε² = 1`, `w = ε·s^a`. For `k ≥ 1` the
function

`H_w(u) = u^{-2ak} · Θ̈_{q^N}(u^N)^k / Θ̈_{q^N}(w·u^N)^k`

is an element of the function field `K(E_q)` (`exists_transFactor`). The proof runs the weight
family engine of `ThetaPullback.lean`:

* `scaleCoef`, `isWeightFamily_scaleCoef`: if `c` is a weight-`k` family with multiplier `A`,
  then `m ↦ c_m w^m` (the family of `U ↦ G(wU)`) is a weight-`k` family with multiplier
  `A·w^{-k}`;
* `c = cpow (oddShift (tatePow t N hN) 1) k`, the family of `U^{-k}·Θ̈_{q^N}(U)^k`, has weight
  `2k` and multiplier `(-Q^2)^{-k}` for `Q^ℤ` (`isWeightFamily_thetaPow`);
* the numerator `u^{-kN}·(u^N)^{-k}Θ̈_{q^N}(u^N)^k` and the denominator
  `u^{-(kN-2ak)}·(w u^N)^{-k}Θ̈_{q^N}(w u^N)^k` are weight-`4kN` families for `q^ℤ`
  (`isWeightFamily_pull`) with the multiplier `q^{-4kN}` of `θ(-u)^{4kN}`
  (`transMult_num`, `transMult_den`: the extra factor `w^{-4k} = q^{-2ak}` of the
  denominator is compensated by the shift `2ak`);
* `exists_hasTateValue_of_weight` turns the quotient into an element of `K(E_q)`, which takes
  the value `w^k·H_w(u)`; a point `u` of norm one with `u^{2N} ≠ 1` shows that the denominator
  is nonzero (`etaleTheta_trans_ne_zero`).
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]

/-! ### Scaling of Laurent families -/

/-- The Laurent family of `U ↦ G(w·U)`. -/
def scaleCoef (c : ℤ → K) (w : Kˣ) (m : ℤ) : K := c m * (w : K) ^ m

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem scaleCoef_term (c : ℤ → K) (w u : Kˣ) (m : ℤ) :
    scaleCoef c w m * (u : K) ^ m = c m * ((w * u : Kˣ) : K) ^ m := by
  rw [scaleCoef, Units.val_mul, mul_zpow, mul_assoc]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem tsum_scaleCoef (c : ℤ → K) (w u : Kˣ) :
    (∑' m : ℤ, scaleCoef c w m * (u : K) ^ m) = ∑' m : ℤ, c m * ((w * u : Kˣ) : K) ^ m :=
  tsum_congr (scaleCoef_term c w u)

omit [CompleteSpace K] [IsUltrametricDist K] in
/-- **Scaling a theta family**: if `c` is a weight-`k` family with multiplier `A`, then the
family `m ↦ c_m w^m` of `U ↦ G(wU)` is a weight-`k` family with multiplier `A·w^{-k}`. -/
theorem isWeightFamily_scaleCoef {T : TateParameter K} {k : ℕ} {A : Kˣ} {c : ℤ → K}
    (hc : T.IsWeightFamily k A c) (w : Kˣ) :
    T.IsWeightFamily k (A * (w ^ k)⁻¹) (scaleCoef c w) := by
  refine ⟨fun u => (hc.summable (w * u)).congr fun m => (scaleCoef_term c w u m).symm,
    fun n => ?_⟩
  have hw : (w : K) ≠ 0 := w.ne_zero
  have h := hc.step n
  simp only [scaleCoef, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  rw [zpow_add₀ hw, zpow_natCast, ← mul_assoc ((T.q : K) ^ n), ← h]
  calc (A : K) * ((w : K) ^ k)⁻¹ * (c (n + k) * ((w : K) ^ n * (w : K) ^ k))
      = (A : K) * c (n + k) * (w : K) ^ n * ((w : K) ^ k * ((w : K) ^ k)⁻¹) := by ring
    _ = (A : K) * c (n + k) * (w : K) ^ n := by
      rw [mul_inv_cancel₀ (pow_ne_zero _ hw), mul_one]

/-! ### Multiplier identities -/

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem neg_mult_sq (x : Kˣ) (k : ℕ) : ((x * (-1))⁻¹ ^ k) ^ 2 = (x ^ (2 * k))⁻¹ := by
  rw [← pow_mul, mul_comm k 2, inv_pow, mul_pow, (even_two_mul k).neg_one_pow, mul_one]

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem multθ_pow_four_mul (t : TateParameter K) (k N : ℕ) :
    multθ t ^ (2 * (2 * k) * N) = (t.q ^ (2 * (2 * k) * N))⁻¹ := by
  unfold multθ
  rw [inv_pow, mul_pow, Even.neg_one_pow ⟨2 * k * N, by ring⟩, mul_one]

theorem inv_mul_inv_cancel_aux {G : Type*} [CommGroup G] (x y z : G) :
    (x * y⁻¹)⁻¹ * (z * y⁻¹) = x⁻¹ * z := by
  rw [mul_inv, inv_inv, mul_comm z, ← mul_assoc, mul_inv_cancel_right]

variable (t : TateParameter K) (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) {N : ℕ}
  (hN : 0 < N) (T : TateParameter K) (hT : T.q = s ^ N)

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hT in
/-- The multiplier of the numerator family: `q^{-kN}·(-Q²)^{-2k}·Q^{-2k} = q^{-4kN}`. -/
theorem transMult_num (k : ℕ) :
    (t.q ^ ((k * N : ℕ) : ℤ))⁻¹ * ((T.q ^ 2 * (-1))⁻¹ ^ k) ^ 2 * (T.q ^ (2 * k))⁻¹ =
      multθ t ^ (2 * (2 * k) * N) := by
  rw [multθ_pow_four_mul, neg_mult_sq, pow_mul T.q 2 k, isogeny_lattice t hs T hT,
    zpow_natCast, ← pow_mul, ← pow_mul, ← mul_inv, ← mul_inv, ← pow_add, ← pow_add]
  congr 2
  ring

omit [CompleteSpace K] [IsUltrametricDist K] in
include hs hT in
/-- The multiplier of the denominator family: the extra factor `w^{-4k} = q^{-2ak}` of
`w = ε·s^a` is compensated by the shift `q^{2ak}`. -/
theorem transMult_den (k : ℕ) {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) (a : ℕ) :
    (t.q ^ (((k * N : ℕ) : ℤ) - ((2 * a * k : ℕ) : ℤ)))⁻¹ *
        ((T.q ^ 2 * (-1))⁻¹ ^ k * ((ε * s ^ a) ^ (2 * k))⁻¹) ^ 2 * (T.q ^ (2 * k))⁻¹ =
      multθ t ^ (2 * (2 * k) * N) := by
  have hε' : ε ^ 2 = 1 := Units.ext (by simpa using hε)
  have hw2 : (ε * s ^ a) ^ 2 = t.q ^ a := by
    rw [mul_pow, hε', one_mul, ← pow_mul, mul_comm a 2, pow_mul, hs]
  have hw4 : ((ε * s ^ a) ^ (2 * k)) ^ 2 = t.q ^ (2 * a * k) := by
    rw [← pow_mul, mul_comm (2 * k) 2, pow_mul (ε * s ^ a) 2 (2 * k), hw2, ← pow_mul]
    congr 1
    ring
  rw [← transMult_num t hs T hT k, zpow_sub, mul_pow ((T.q ^ 2 * (-1))⁻¹ ^ k) _ 2,
    inv_pow ((ε * s ^ a) ^ (2 * k)) 2, hw4, zpow_natCast t.q (2 * a * k),
    inv_mul_inv_cancel_aux]

/-! ### The families of `Θ̈_{q^N}(U)^k` and of the numerator and denominator -/

include hs hT in
/-- `U^{-k}·Θ̈_{q^N}(U)^k` is a weight-`2k` family for the lattice `Q^ℤ` with multiplier
`(-Q²)^{-k}`. -/
theorem isWeightFamily_thetaPow (k : ℕ) :
    T.IsWeightFamily (2 * k) ((T.q ^ 2 * (-1))⁻¹ ^ k) (cpow (oddShift (tatePow t N hN) 1) k) := by
  have hs' : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  have h1 := isWeightFamily_oddShift (tatePow t N hN) hs' 1 T (by rw [hT, pow_one])
  rw [pow_one] at h1
  exact isWeightFamily_cpow T h1 k

include hs hT in
theorem tsum_thetaPow (k : ℕ) (U : Kˣ) :
    (∑' m : ℤ, cpow (oddShift (tatePow t N hN) 1) k m * (U : K) ^ m) =
      (U : K) ^ (-(k : ℤ)) * etaleTheta (tatePow t N hN) U ^ k := by
  have hs' : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  have h1 := isWeightFamily_oddShift (tatePow t N hN) hs' 1 T (by rw [hT, pow_one])
  rw [tsum_cpow T h1 U k, (hasSum_oddShift _ 1 U).tsum_eq, mul_pow]
  congr 1
  rw [Nat.cast_one, ← zpow_natCast, ← zpow_mul, neg_one_mul]

include hs hT in
theorem tsum_transNum (k : ℕ) (u : Kˣ) :
    (∑' m : ℤ, pullCoef (cpow (oddShift (tatePow t N hN) 1) k) N ((k * N : ℕ) : ℤ) m *
        (u : K) ^ m) =
      (u : K) ^ (-((k * N : ℕ) : ℤ)) * (((u ^ N : Kˣ) : K) ^ (-(k : ℤ)) *
        etaleTheta (tatePow t N hN) (u ^ N) ^ k) := by
  rw [(hasSum_pullCoef (isWeightFamily_thetaPow t hs hN T hT k) hN _ u).tsum_eq,
    tsum_thetaPow t hs hN T hT k]

include hs hT in
theorem tsum_transDen (k : ℕ) (w : Kˣ) (b : ℤ) (u : Kˣ) :
    (∑' m : ℤ, pullCoef (scaleCoef (cpow (oddShift (tatePow t N hN) 1) k) w) N b m *
        (u : K) ^ m) =
      (u : K) ^ (-b) * (((w * u ^ N : Kˣ) : K) ^ (-(k : ℤ)) *
        etaleTheta (tatePow t N hN) (w * u ^ N) ^ k) := by
  rw [(hasSum_pullCoef (isWeightFamily_scaleCoef (isWeightFamily_thetaPow t hs hN T hT k) w)
    hN b u).tsum_eq, tsum_scaleCoef, tsum_thetaPow t hs hN T hT k]

/-! ### A good point -/

include hs in
/-- For `|u| = 1` and `u^{2N} ≠ 1`, `Θ̈_{q^N}(ε·s^a·u^N) ≠ 0`: its square `q^a·u^{2N}` is not a
power of `q^N`. -/
theorem etaleTheta_trans_ne_zero {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) (a : ℕ) {u : Kˣ}
    (hn : ‖(u : K)‖ = 1) (h1 : (u : K) ^ (2 * N) ≠ 1) :
    etaleTheta (tatePow t N hN) (ε * s ^ a * u ^ N) ≠ 0 := by
  rw [Ne, etaleTheta_eq_zero_iff]
  rintro ⟨j, hj⟩
  apply h1
  have hq2 : (s : K) ^ 2 = (t.q : K) := by rw [← hs, Units.val_pow_eq_pow_val]
  have hsq : ((ε * s ^ a * u ^ N : Kˣ) : K) ^ 2 = (t.q : K) ^ a * (u : K) ^ (2 * N) := by
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    rw [mul_pow, mul_pow, hε, one_mul, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm N 2,
      pow_mul (s : K) 2 a, hq2]
  have hj' : (t.q : K) ^ (a : ℤ) * (u : K) ^ (2 * N) = (t.q : K) ^ ((N : ℤ) * j) := by
    rw [zpow_natCast, ← hsq, hj, tatePow_q, Units.val_pow_eq_pow_val, zpow_mul, zpow_natCast]
  refine eq_one_of_q_zpow_mul (T := t) (k := (a : ℤ) - (N : ℤ) * j)
    (by rw [norm_pow, hn, one_pow]) ?_
  rw [zpow_sub₀ t.q.ne_zero, div_mul_eq_mul_div, hj', div_self (zpow_ne_zero _ t.q.ne_zero)]

/-! ### The translation factor -/

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem transValue_eq {ε : Kˣ} (a k : ℕ) (u : Kˣ) {Θ₁ Θ₂ : K} (hΘ : Θ₂ ≠ 0) :
    (((ε * s ^ a : Kˣ) : K) ^ k)⁻¹ *
        ((u : K) ^ (-((k * N : ℕ) : ℤ)) * (((u ^ N : Kˣ) : K) ^ (-(k : ℤ)) * Θ₁ ^ k) /
          ((u : K) ^ (-(((k * N : ℕ) : ℤ) - ((2 * a * k : ℕ) : ℤ))) *
            (((ε * s ^ a * u ^ N : Kˣ) : K) ^ (-(k : ℤ)) * Θ₂ ^ k))) =
      (u : K) ^ (-((2 * a * k : ℕ) : ℤ)) * Θ₁ ^ k / Θ₂ ^ k := by
  have hu0 : (u : K) ≠ 0 := u.ne_zero
  have hε0 : (ε : K) ≠ 0 := ε.ne_zero
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, zpow_neg, zpow_sub₀ hu0, zpow_natCast]
  field_simp
  ring

include hs hT in
/-- **The translation factor `H_w ∈ K(E_q)`** ((F2), `w = ε·s^a`, `ε² = 1`, `k ≥ 1`): there are
`H ∈ K(E_q)` and `0 ≠ D ∈ K[E_q]` such that wherever `D(u) ≠ 0`, `Θ̈_{q^N}(w·u^N) ≠ 0` and
`H(u) = u^{-2ak}·Θ̈_{q^N}(u^N)^k / Θ̈_{q^N}(w·u^N)^k`. -/
theorem exists_transFactor (k : ℕ) (hk : 0 < k) {ε : Kˣ} (hε : (ε : K) ^ 2 = 1) (a : ℕ) :
    ∃ (H : TateField t) (D : TateRing t), D ≠ 0 ∧ ∀ (u : Kˣ) (hu : OffOrbit t u),
      evalTate t h12 hu D ≠ 0 →
        etaleTheta (tatePow t N hN) (ε * s ^ a * u ^ N) ≠ 0 ∧
        HasTateValue t h12 H hu ((u : K) ^ (-((2 * a * k : ℕ) : ℤ)) *
          etaleTheta (tatePow t N hN) (u ^ N) ^ k /
            etaleTheta (tatePow t N hN) (ε * s ^ a * u ^ N) ^ k) := by
  have hc := isWeightFamily_thetaPow t hs hN T hT k
  have h₁ := isWeightFamily_pull t hs hN T hT hc ((k * N : ℕ) : ℤ)
  rw [transMult_num t hs T hT k] at h₁
  have h₂ := isWeightFamily_pull t hs hN T hT (isWeightFamily_scaleCoef hc (ε * s ^ a))
    (((k * N : ℕ) : ℤ) - ((2 * a * k : ℕ) : ℤ))
  rw [transMult_den t hs T hT k hε a] at h₂
  obtain ⟨n, d, h⟩ := exists_hasTateValue_of_weight (h12 := h12)
    (Nat.mul_pos (Nat.mul_pos two_pos (Nat.mul_pos two_pos hk)) hN) h₁ h₂
  refine ⟨algebraMap K (TateField t) (((ε * s ^ a : Kˣ) : K) ^ k)⁻¹ *
      (algebraMap _ (TateField t) n / algebraMap _ (TateField t) d), d, ?_, fun u hu hD => ?_⟩
  · -- a good point
    obtain ⟨u₀, hn₀, h1₀⟩ := exists_good_unit t hN
    have hu₀ : OffOrbit t u₀ := offOrbit_of_norm hn₀ fun h => h1₀ (by rw [h, one_pow])
    have hΘ₀ := etaleTheta_trans_ne_zero t hs hN hε a hn₀ h1₀
    obtain ⟨-, e₂, -⟩ := h u₀ hu₀
    intro hd0
    rw [hd0, map_zero, zero_mul, tsum_transDen t hs hN T hT k] at e₂
    exact hΘ₀ ((pow_eq_zero_iff hk.ne').mp ((mul_eq_zero.mp ((mul_eq_zero.mp e₂).resolve_left
      (zpow_ne_zero _ u₀.ne_zero))).resolve_left (zpow_ne_zero _ (Units.ne_zero _))))
  · obtain ⟨-, e₂, hv⟩ := h u hu
    have hθ : t.theta (-u) ^ (2 * (2 * k) * N) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero t hu)
    have hF₂ : (∑' m : ℤ, pullCoef (scaleCoef (cpow (oddShift (tatePow t N hN) 1) k)
        (ε * s ^ a)) N (((k * N : ℕ) : ℤ) - ((2 * a * k : ℕ) : ℤ)) m * (u : K) ^ m) ≠ 0 := by
      rw [e₂]; exact mul_ne_zero hD hθ
    have hΘ : etaleTheta (tatePow t N hN) (ε * s ^ a * u ^ N) ≠ 0 := by
      intro h0
      apply hF₂
      rw [tsum_transDen t hs hN T hT k, h0, zero_pow hk.ne', mul_zero, mul_zero]
    refine ⟨hΘ, ((HasTateValue.const hu _).mul (hv hF₂)).congr ?_⟩
    rw [tsum_transNum t hs hN T hT k u, tsum_transDen t hs hN T hT k]
    exact transValue_eq a k u hΘ

end Iut.EtaleTheta
