/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.EtaleTheta.ThetaLevel
import Iut.EtaleTheta.TateElliptic

/-!
# The theta level functions are rational on `E_Q` (MR14, task G2c)

Let `s² = q` and `Q = s^N` with `N` even. The theta level function
`f_N(Ü) = Θ̈_q(Ü) / Θ̈_{q^N}(Ü)^N` (`ThetaLevel.lean`) is `Q`-periodic. Here we show that it is
a **rational function on the Tate curve `E_Q`**: there are polynomials `P₁, Q₁, P₂, Q₂` with

`f_N(Ü) = (P₁(X_Q) + Y_Q·Q₁(X_Q)) / (P₂(X_Q) + Y_Q·Q₂(X_Q))`

where `X_Q, Y_Q` are the Tate coordinates of the parameter `Q` (`thetaLevel_eq_div`).

Both `Ü^{-N}·Θ̈_q(Ü)` and `Ü^{-N}·Θ̈_{q^N}(Ü)^N` are weight-`2N` theta families for the lattice
`Q^ℤ` with multiplier `(-1)^N Q^{-2N}` (`isWeightFamily_oddShift`, `isWeightFamily_oddShiftPow`;
[EtTh], Prop. 1.4(ii), `etaleTheta_zpow_sqrt_mul`); for even `N` this is the multiplier of
`θ_Q(-Ü)^{2N}`, so Tate's theorem for theta functions (`exists_poly_of_isWeightFamily`) applies
to both. Even `N` are cofinal, which suffices for the inverse limit over `N` defining the étale
theta class (MR14 plan, route R-alg).
-/

noncomputable section

namespace Iut.EtaleTheta

open TateCurvesTheta TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- The Laurent coefficients of `Θ̈_q(Ü) = ∑ₙ (-1)ⁿ q^{n(n+1)/2} Ü^{2n+1}` in `Ü`. -/
def oddCoef (m : ℤ) : K :=
  if m % 2 = 1 then (-1 : K) ^ (m / 2) * (t.q : K) ^ thetaExp (m / 2) else 0

theorem hasSum_oddCoef (U : Kˣ) :
    HasSum (fun m : ℤ => oddCoef t m * (U : K) ^ m) (etaleTheta t U) := by
  have hinj : Function.Injective fun n : ℤ => 2 * n + 1 := by
    intro a b h
    simp only at h
    omega
  rw [← hinj.hasSum_iff]
  · convert hasSum_etaleTheta t U using 1
    funext n
    simp only [Function.comp_apply, oddCoef]
    rw [if_pos (by omega), show (2 * n + 1) / 2 = n by omega]
  · intro m hm
    have : m % 2 ≠ 1 := fun h => hm ⟨m / 2, show 2 * (m / 2) + 1 = m by omega⟩
    simp [oddCoef, this]

/-- The coefficients of `Ü^{-N}·Θ̈_q(Ü)`. -/
def oddShift (N : ℕ) (m : ℤ) : K := oddCoef t (m + N)

theorem hasSum_oddShift (N : ℕ) (U : Kˣ) :
    HasSum (fun m : ℤ => oddShift t N m * (U : K) ^ m)
      ((U : K) ^ (-(N : ℤ)) * etaleTheta t U) := by
  have h := (hasSum_oddCoef t U).mul_left ((U : K) ^ (-(N : ℤ)))
  rw [← (Equiv.addRight (N : ℤ)).hasSum_iff] at h
  have e : (fun m : ℤ => oddShift t N m * (U : K) ^ m) =
      (fun i => (U : K) ^ (-(N : ℤ)) * (oddCoef t i * (U : K) ^ i)) ∘ Equiv.addRight (N : ℤ) := by
    funext m
    simp only [Function.comp_apply, Equiv.coe_addRight, oddShift]
    rw [zpow_add₀ U.ne_zero, zpow_neg, zpow_natCast]
    field_simp
  rw [e]
  exact h

/-- **`Ü^{-N}·Θ̈_q(Ü)` is a weight-`2N` theta family for the lattice `Q^ℤ`, `Q = s^N`**, with
multiplier `(-1)^N Q^{-2N}` ([EtTh], Prop. 1.4(ii) with `a = N`). -/
theorem isWeightFamily_oddShift {s : Kˣ} (hs : s ^ 2 = t.q) (N : ℕ) (T : TateParameter K)
    (hT : T.q = s ^ N) : T.IsWeightFamily (2 * N) ((T.q ^ 2 * (-1))⁻¹ ^ N) (oddShift t N) := by
  refine IsWeightFamily.of_tsum_q_smul (fun u => (hasSum_oddShift t N u).summable) fun u => ?_
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  have hQu : (T.q : K) * (u : K) = ((s ^ (N : ℤ) * u : Kˣ) : K) := by
    rw [hT, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, zpow_natCast]
  rw [(hasSum_oddShift t N u).tsum_eq, hQu, (hasSum_oddShift t N _).tsum_eq,
    etaleTheta_zpow_sqrt_mul t hs, thetaFactor]
  simp only [hT, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val, Units.val_neg, Units.val_one]
  rw [show (-(N : ℤ) ^ 2) = -((N * N : ℕ) : ℤ) by push_cast; ring,
    show (-2 * (N : ℤ)) = -((2 * N : ℕ) : ℤ) by push_cast; ring]
  simp only [zpow_neg, zpow_natCast]
  field_simp
  have hX : (s : K) ^ (N ^ 2 * 2) * (s : K)⁻¹ ^ (N ^ 2 * 2) = 1 := by
    rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs0)]
  linear_combination (-(etaleTheta t u * (u : K) ^ N * (-1) ^ N)) * hX

omit [CompleteSpace K] [IsUltrametricDist K] in
theorem multθ_pow_two_mul {N : ℕ} (hN : Even N) (T : TateParameter K) :
    multθ T ^ (2 * N) = (T.q ^ 2 * (-1))⁻¹ ^ N := by
  obtain ⟨M, rfl⟩ := hN
  ext
  simp only [multθ, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul,
    Units.val_neg, Units.val_one]
  rw [show 2 * (M + M) = 4 * M by ring, show M + M = 2 * M by ring, pow_mul, pow_mul]
  have hq : (T.q : K) ≠ 0 := T.q.ne_zero
  field_simp

/-- **`Ü^{-N}·Θ̈_{q^N}(Ü)^N` is a weight-`2N` theta family for the lattice `Q^ℤ`** (the `N`-th
convolution power of the family of `Ü^{-1}·Θ̈_{q^N}(Ü)`). -/
theorem isWeightFamily_oddShiftPow {s : Kˣ} (hs : s ^ 2 = t.q) (N : ℕ) (hN : 0 < N)
    (T : TateParameter K) (hT : T.q = s ^ N) :
    T.IsWeightFamily (2 * N) ((T.q ^ 2 * (-1))⁻¹ ^ N)
      (cpow (oddShift (tatePow t N hN) 1) N) := by
  have hs' : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  have h1 := isWeightFamily_oddShift (tatePow t N hN) hs' 1 T (by rw [hT, pow_one])
  rw [pow_one] at h1
  exact isWeightFamily_cpow T h1 N

theorem tsum_oddShiftPow (N : ℕ) (hN : 0 < N) (T : TateParameter K) {s : Kˣ}
    (hs : s ^ 2 = t.q) (hT : T.q = s ^ N) (U : Kˣ) :
    (∑' m : ℤ, cpow (oddShift (tatePow t N hN) 1) N m * (U : K) ^ m) =
      (U : K) ^ (-(N : ℤ)) * etaleTheta (tatePow t N hN) U ^ N := by
  have hs' : (s ^ N) ^ 2 = (tatePow t N hN).q := by
    rw [tatePow_q, ← hs, ← pow_mul, ← pow_mul, mul_comm]
  have h1 := isWeightFamily_oddShift (tatePow t N hN) hs' 1 T (by rw [hT, pow_one])
  rw [tsum_cpow T h1 U N, (hasSum_oddShift _ 1 U).tsum_eq, mul_pow]
  congr 1
  rw [Nat.cast_one, ← zpow_natCast, ← zpow_mul, neg_one_mul]

/-- **Numerator and denominator of `f_N` in Tate coordinates of `E_Q`** (`N` even, `Q = s^N`):
`Θ̈_q(Ü) = (P₁(X_Q) + Y_Q·Q₁(X_Q))·Ü^N·θ_Q(-Ü)^{2N}` and
`Θ̈_{q^N}(Ü)^N = (P₂(X_Q) + Y_Q·Q₂(X_Q))·Ü^N·θ_Q(-Ü)^{2N}` off the period orbit `Q^ℤ`. -/
theorem exists_poly_thetaLevel (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) (N : ℕ)
    (hN : 0 < N) (hev : Even N) (T : TateParameter K) (hT : T.q = s ^ N) :
    ∃ P₁ Q₁ P₂ Q₂ : Polynomial K, ∀ u : Kˣ, OffOrbit T u →
      etaleTheta t u = (P₁.eval (T.X u) + T.Y u * Q₁.eval (T.X u)) * (u : K) ^ N *
          T.theta (-u) ^ (2 * N) ∧
        etaleTheta (tatePow t N hN) u ^ N =
          (P₂.eval (T.X u) + T.Y u * Q₂.eval (T.X u)) * (u : K) ^ N * T.theta (-u) ^ (2 * N) := by
  have h2N : 0 < 2 * N := by omega
  have hA := multθ_pow_two_mul hev T
  obtain ⟨P₁, Q₁, h₁⟩ := exists_poly_of_isWeightFamily T h12 h2N
    (hA ▸ isWeightFamily_oddShift t hs N T hT)
  obtain ⟨P₂, Q₂, h₂⟩ := exists_poly_of_isWeightFamily T h12 h2N
    (hA ▸ isWeightFamily_oddShiftPow t hs N hN T hT)
  refine ⟨P₁, Q₁, P₂, Q₂, fun u hu => ⟨?_, ?_⟩⟩
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

/-- **G2c: `f_N` is a rational function on `E_Q`** (`N` even, `Q = s^N`): off the period orbit
`Q^ℤ`, `f_N(Ü) = (P₁(X_Q) + Y_Q·Q₁(X_Q)) / (P₂(X_Q) + Y_Q·Q₂(X_Q))`, and the denominator
vanishes exactly where `Θ̈_{q^N}` does. -/
theorem thetaLevel_eq_div (h12 : (12 : K) ≠ 0) {s : Kˣ} (hs : s ^ 2 = t.q) (N : ℕ)
    (hN : 0 < N) (hev : Even N) (T : TateParameter K) (hT : T.q = s ^ N) :
    ∃ P₁ Q₁ P₂ Q₂ : Polynomial K, ∀ u : Kˣ, OffOrbit T u →
      thetaLevel t N hN u = (P₁.eval (T.X u) + T.Y u * Q₁.eval (T.X u)) /
          (P₂.eval (T.X u) + T.Y u * Q₂.eval (T.X u)) ∧
        (P₂.eval (T.X u) + T.Y u * Q₂.eval (T.X u) = 0 ↔
          etaleTheta (tatePow t N hN) u = 0) := by
  obtain ⟨P₁, Q₁, P₂, Q₂, h⟩ := exists_poly_thetaLevel t h12 hs N hN hev T hT
  refine ⟨P₁, Q₁, P₂, Q₂, fun u hu => ?_⟩
  obtain ⟨e₁, e₂⟩ := h u hu
  have hθ : T.theta (-u) ^ (2 * N) ≠ 0 := pow_ne_zero _ (theta_neg_ne_zero T hu)
  have hu0 : (u : K) ^ N ≠ 0 := pow_ne_zero _ u.ne_zero
  refine ⟨?_, ?_⟩
  · rw [thetaLevel, e₁, e₂, mul_assoc, mul_assoc, mul_div_mul_right _ _ (mul_ne_zero hu0 hθ)]
  · constructor
    · intro h0
      have : etaleTheta (tatePow t N hN) u ^ N = 0 := by rw [e₂, h0]; ring
      exact (pow_eq_zero_iff hN.ne').mp this
    · intro h0
      have := e₂
      rw [h0, zero_pow hN.ne'] at this
      exact (mul_eq_zero.mp ((mul_eq_zero.mp this.symm).resolve_right hθ)).resolve_right hu0

end Iut.EtaleTheta
