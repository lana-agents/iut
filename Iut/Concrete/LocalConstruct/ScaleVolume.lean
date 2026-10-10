/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.TensorIntegral

/-!
# The log-volume of elementary scalings (IUT IV, Proposition 1.4)

For a nonarchimedean packet `T = ⊗_j K_{w_j}` at `p`, all of whose places lie over `p`, and
`y_j ∈ K_{w_j}^×`, the normalized log-volume of the scaled integral structure is
`μ^log((∏_j incl_j(y_j))·(R_I)^∼) = −(∑_j ord_p(y_j))·log p`
(`componentVol_prod_incl_smul_integral`); this is the volume computation behind the estimates
of IUT IV, Proposition 1.4 for the corrected indeterminacy automorphisms.

The proof: the units of `T` scale the Haar measure by the distributive Haar character
`χ : Tˣ →* ℝ≥0` (`MeasureTheory.distribHaarChar`, from the uniqueness of Haar measures), so
`κ(a) := μ^log(a·(R_I)^∼) = log χ(a)/[T : ℚ_p]` is a homomorphism `Tˣ → ℝ`
(`componentVol_units_smul_integral`); `κ(p) = −log p` (from `componentVol_prime_preimage'`),
and `κ(u) = 0` when `u·(R_I)^∼ = (R_I)^∼`. The power trick `z^N = p^M·u` of
`prod_incl_pow_eq`, with `M = N·∑_j ord_p(y_j)` and `u·(R_I)^∼ = (R_I)^∼`
(`prod_incl_smul_integral_eq`), gives `N·κ(z) = −M·log p`.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise NNReal

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (p : Nat.Primes) (c : ι → Place K)

/-- **The modulus of the units of a packet**: the distributive Haar character
`χ(a) = μ(a·S)/μ(S)` of `Tˣ` acting on `T` by multiplication. -/
noncomputable abbrev unitModulus : (Tensor K (.finite p) c)ˣ →* ℝ≥0 :=
  distribHaarChar (Tensor K (.finite p) c)

variable {p c}

/-- `μ(a·S) = χ(a)·μ(S)` for every unit `a` and every set `S`. -/
lemma haar_units_smul (a : (Tensor K (.finite p) c)ˣ) (S : Set (Tensor K (.finite p) c)) :
    haar (.finite p) c ((a : Tensor K (.finite p) c) • S) =
      unitModulus p c a * haar (.finite p) c S :=
  (distribHaarChar_mul (haar (.finite p) c) a S).symm

/-- `μ^log(a·(R_I)^∼) = log χ(a)/[T : ℚ_p]` for every unit `a`. -/
theorem componentVol_units_smul_integral (a : (Tensor K (.finite p) c)ˣ) :
    componentVol (.finite p) c ((a : Tensor K (.finite p) c) • integral p c) =
      Real.log (unitModulus p c a) / Module.finrank ℚ_[p] (Tensor K (.finite p) c) := by
  have hI : integral p c = integralAt (.finite p) c := rfl
  unfold componentVol
  rw [hI, haar_units_smul, ENNReal.toReal_mul, ENNReal.coe_toReal, mul_div_assoc,
    div_self toReal_haar_integralAt_pos.ne', mul_one]

/-- The log-modulus `log χ` is additive. -/
lemma log_unitModulus_mul (a b : (Tensor K (.finite p) c)ˣ) :
    Real.log (unitModulus p c (a * b)) =
      Real.log (unitModulus p c a) + Real.log (unitModulus p c b) := by
  rw [map_mul, NNReal.coe_mul, Real.log_mul (NNReal.coe_pos.mpr distribHaarChar_pos).ne'
    (NNReal.coe_pos.mpr distribHaarChar_pos).ne']

/-- `log χ(a^n) = n·log χ(a)`. -/
lemma log_unitModulus_zpow (a : (Tensor K (.finite p) c)ˣ) (n : ℤ) :
    Real.log (unitModulus p c (a ^ n)) = n * Real.log (unitModulus p c a) := by
  have hinv : ∀ x : (Tensor K (.finite p) c)ˣ, unitModulus p c x⁻¹ = (unitModulus p c x)⁻¹ :=
    fun x => eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
  rw [map_zpow' _ hinv, NNReal.coe_zpow, Real.log_zpow]

/-- A unit preserving `(R_I)^∼` has log-modulus `0`. -/
lemma log_unitModulus_eq_zero_of_smul_eq (a : (Tensor K (.finite p) c)ˣ)
    (ha : (a : Tensor K (.finite p) c) • integral p c = integral p c) :
    Real.log (unitModulus p c a) = 0 := by
  have h := haar_units_smul a (integral p c)
  rw [ha] at h
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, eq_comm] at h'
  have h'' : (unitModulus p c a : ℝ) = 1 :=
    (mul_eq_right₀ (toReal_haar_integralAt_pos (vQ := .finite p) (c := c)).ne').mp h'
  rw [h'', Real.log_one]

/-- `log χ(p) = −[T : ℚ_p]·log p`. -/
lemma log_unitModulus_primeUnit (hc : ∀ j, IsOver K p (c j)) :
    Real.log (unitModulus p c (primeUnit p c)) =
      -(Module.finrank ℚ_[p] (Tensor K (.finite p) c) : ℝ) * Real.log p := by
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] (Tensor K (.finite p) c) := by
    exact_mod_cast finrank_tensor_finite_pos p hc
  have hpre : (fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹'
      (((primeUnit p c : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) • integral p c) =
      integralAt (.finite p) c := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul, val_primeUnit]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rwa [(isUnit_natCast_prime_tensor p c).mul_left_cancel hxy] at hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hunit : IsUnit ((primeUnit p c : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) :=
    (primeUnit p c).isUnit
  have h := componentVol_prime_preimage' p hc
    (((primeUnit p c : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) • integral p c)
    (measurableSet_smul_integralAt (vQ := .finite p) _)
    (haar_smul_integralAt_pos (vQ := .finite p) hunit).ne'
    (haar_smul_integralAt_lt_top (vQ := .finite p) _).ne
  rw [hpre, componentVol_integral, componentVol_units_smul_integral] at h
  have h2 : Real.log (unitModulus p c (primeUnit p c)) /
      Module.finrank ℚ_[p] (Tensor K (.finite p) c) = -Real.log p := by linarith
  rw [div_eq_iff hd.ne'] at h2
  rw [h2]
  ring

/-- **The log-volume of elementary scalings** (IUT IV, Proposition 1.4): for `y_j ∈ K_{w_j}^×`,
`μ^log((∏_j incl_j(y_j))·(R_I)^∼) = −(∑_j ord_p(y_j))·log p`. -/
theorem componentVol_prod_incl_smul_integral (hc : ∀ j, IsOver K p (c j))
    (w : ι → FinitePlace K) (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j))
    (hy : ∀ j, y j ≠ 0) :
    componentVol (.finite p) c ((∏ j, incl p c j (w j) (h j) (y j)) • integral p c) =
      -(∑ j, ordp K (w j) (y j)) * Real.log p := by
  obtain ⟨N, hN, M, hM, u, hu0, hu, hpow⟩ := prod_incl_pow_eq hc w h y hy
  set Z := (isUnit_prod_incl (p := p) (c := c) w h y hy).unit
  set U := (isUnit_prod_incl (p := p) (c := c) w h u hu0).unit
  have hU : (U : Tensor K (.finite p) c) • integral p c = integral p c := by
    rw [IsUnit.unit_spec]
    exact prod_incl_smul_integral_eq hc w h u hu0 (by simp [hu])
  have hZU : Z ^ N = primeUnit p c ^ M * U := by
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mul]
    exact hpow
  have hlog : Real.log (unitModulus p c (Z ^ N)) =
      Real.log (unitModulus p c (primeUnit p c ^ M * U)) := by rw [hZU]
  rw [log_unitModulus_mul, log_unitModulus_eq_zero_of_smul_eq U hU, add_zero,
    log_unitModulus_zpow, log_unitModulus_primeUnit hc, ← zpow_natCast,
    log_unitModulus_zpow, hM] at hlog
  have hd : (0 : ℝ) < Module.finrank ℚ_[p] (Tensor K (.finite p) c) := by
    exact_mod_cast finrank_tensor_finite_pos p hc
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : (∏ j, incl p c j (w j) (h j) (y j)) = (Z : Tensor K (.finite p) c) := rfl
  rw [hz, componentVol_units_smul_integral, div_eq_iff hd.ne']
  push_cast at hlog
  have : (N : ℝ) * Real.log (unitModulus p c Z) =
      N * (-(∑ j, ordp K (w j) (y j)) * Real.log p *
        Module.finrank ℚ_[p] (Tensor K (.finite p) c)) := by
    rw [hlog]; ring
  exact mul_left_cancel₀ hN'.ne' this

end LocalConstruct

end Iut
