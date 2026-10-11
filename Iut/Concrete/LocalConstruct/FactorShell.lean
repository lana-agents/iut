/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.LogShell
import PadicLogVolume.LogLattice

/-!
# The log-shell of a completion between two scaled rings of integers (IUT IV, Prop. 1.2(i))

For a finite place `w` of `K` of residue characteristic `p` and ramification index `e`, the
log-shell `𝓘_w = (2p)⁻¹·log_p(𝓞_w^×)` of the completion `K_w` satisfies

`(2p)⁻¹·p^{a}·𝓞_w ⊆ 𝓘_w ⊆ (2p)⁻¹·p^{-b}·𝓞_w`

with Mochizuki's exponents `a = logLatticeA p e`, `b = logLatticeB p e`
(`LogLattice.lean`). This file realizes `p^{a}` and `p^{-b}` by explicit elements `ϖ_a`, `ϖ_b`
of `K_w` (powers of a uniformizer and of `p`) with `ord_p ϖ_a = a`, `ord_p ϖ_b = −b`, and
records the norm–valuation dictionary `‖x‖ = ‖p‖^{ord_p x}` and the discreteness of `K_w`
needed to apply the bounds of `LogLattice.lean`.
-/

namespace Iut

open PadicLogVolume

namespace LocalConstruct

open NumberField IsDedekindDomain WithZero
open scoped WithZero

universe u

variable {K : Type u} [Field K] [NumberField K] (w : FinitePlace K)

/-- `p` as an element of `K_w`. -/
local notation "pw" => ((residueChar w : ℕ) : completionAt K w)

lemma ordp_residueChar : ordp K w pw = 1 := by
  have := ordp_p w
  rwa [map_natCast] at this

lemma residueChar_ne_zero' : pw ≠ 0 := by
  have h := ordp_residueChar w
  intro h0
  rw [h0] at h
  simp [ordp] at h

lemma norm_residueChar_pos : 0 < ‖pw‖ := norm_pos_iff.mpr (residueChar_ne_zero' w)

lemma norm_residueChar_lt_one : ‖pw‖ < 1 := by
  have h := ordp_residueChar w
  have hp : (residueChar w).Prime := residueChar_prime w
  have hlog : 0 < Real.log (residueChar w) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hd : (0 : ℝ) < localDeg K w := by exact_mod_cast localDeg_pos w
  unfold ordp at h
  have : Real.log ‖pw‖ < 0 := by
    have h' : -Real.log ‖pw‖ = localDeg K w * Real.log (residueChar w) := by
      field_simp at h; linarith
    nlinarith [mul_pos hd hlog]
  exact (Real.log_neg_iff (norm_residueChar_pos w)).mp this

/-- **`‖x‖ = ‖p‖^{ord_p x}`** for `x ≠ 0`. -/
lemma norm_eq_rpow_ordp {x : completionAt K w} (hx : x ≠ 0) :
    ‖x‖ = ‖pw‖ ^ ordp K w x := by
  have hp : (residueChar w).Prime := residueChar_prime w
  have hlog : 0 < Real.log (residueChar w) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hd : (0 : ℝ) < localDeg K w := by exact_mod_cast localDeg_pos w
  have hpw : Real.log ‖pw‖ = -(localDeg K w * Real.log (residueChar w)) := by
    have h := ordp_residueChar w
    unfold ordp at h
    field_simp at h
    linarith
  rw [Real.rpow_def_of_pos (norm_residueChar_pos w), hpw]
  unfold ordp
  rw [show -(↑(localDeg K w) * Real.log ↑(residueChar w)) *
      (-Real.log ‖x‖ / (↑(localDeg K w) * Real.log ↑(residueChar w))) = Real.log ‖x‖ by
    field_simp]
  exact (Real.exp_log (norm_pos_iff.mpr hx)).symm

/-- There is a uniformizer: an element of valuation `exp (−1)`. -/
lemma exists_valued_eq_exp_neg_one :
    ∃ π : completionAt K w, Valued.v π = exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀⟩ := w.maximalIdeal.valuation_exists_uniformizer' (K := K)
  refine ⟨(π₀ : completionAt K w), ?_⟩
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ₀]

/-- **A uniformizer** of `K_w`: `ord_p π = 1/e`. -/
noncomputable def unif : completionAt K w := (exists_valued_eq_exp_neg_one w).choose

lemma valued_unif : Valued.v (unif w) = exp (-1 : ℤ) := (exists_valued_eq_exp_neg_one w).choose_spec

lemma unif_ne_zero : unif w ≠ 0 := by
  intro h
  have := valued_unif w
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

lemma ordp_unif : ordp K w (unif w) = (ramIdx K w : ℝ)⁻¹ := by
  rw [ordp_eq_of_valued w _ _ (valued_unif w)]
  simp [div_eq_inv_mul]

/-- **Discreteness**: `‖x‖ < 1 → ‖x‖ ≤ ‖p‖^{1/e}`. -/
lemma norm_le_rpow_of_norm_lt_one {x : completionAt K w} (hx : ‖x‖ < 1) :
    ‖x‖ ≤ ‖pw‖ ^ ((ramIdx K w : ℝ)⁻¹) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [norm_zero]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  set m : ℤ := log (Valued.v x)
  have hm : Valued.v x = exp m := (exp_log hv0).symm
  have hv1 : Valued.v x < 1 := Valued.toNormedField.norm_lt_one_iff.mp hx
  have hm1 : m ≤ -1 := by
    rw [hm, ← exp_zero, exp_lt_exp] at hv1
    omega
  have he : (0 : ℝ) < ramIdx K w := by exact_mod_cast ramIdx_pos' w
  rw [norm_eq_rpow_ordp w hx0, ordp_eq_of_valued w x m hm]
  refine Real.rpow_le_rpow_of_exponent_ge (norm_residueChar_pos w)
    (norm_residueChar_lt_one w).le ?_
  rw [div_eq_mul_inv]
  have : (1 : ℝ) ≤ -(m : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ -m)
  nlinarith [inv_pos.mpr he]

/-! ### The exponents `a`, `b` -/

/-- `e·a ∈ ℕ` realized: the element `ϖ_a` of `K_w` with `ord_p ϖ_a = a`. -/
noncomputable def varpiA : completionAt K w :=
  if residueChar w = 2 then pw ^ 2 else
    unif w ^ (⌈(ramIdx K w : ℝ) / ((residueChar w : ℝ) - 2)⌉).toNat

lemma varpiA_ne_zero : varpiA w ≠ 0 := by
  unfold varpiA
  split_ifs
  · exact pow_ne_zero _ (residueChar_ne_zero' w)
  · exact pow_ne_zero _ (unif_ne_zero w)

lemma ordp_varpiA : ordp K w (varpiA w) = logLatticeA (residueChar w) (ramIdx K w) := by
  unfold varpiA logLatticeA
  split_ifs with h
  · rw [ordp_pow', ordp_residueChar]; norm_num
  · rw [ordp_pow', ordp_unif]
    have hp : (residueChar w).Prime := residueChar_prime w
    have hp3 : (3 : ℝ) ≤ residueChar w := by
      have := hp.two_le
      have : residueChar w ≠ 2 := h
      exact_mod_cast (by omega : 3 ≤ residueChar w)
    have hnn : (0 : ℝ) ≤ (ramIdx K w : ℝ) / ((residueChar w : ℝ) - 2) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    have hc : ((⌈(ramIdx K w : ℝ) / ((residueChar w : ℝ) - 2)⌉.toNat : ℕ) : ℝ) =
        ((⌈(ramIdx K w : ℝ) / ((residueChar w : ℝ) - 2)⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hnn)
    rw [hc, mul_comm]

/-- The element `ϖ_b = π·p^{-N}` with `ord_p ϖ_b = −b`. -/
noncomputable def varpiB : completionAt K w :=
  unif w * (pw ^ (⌊Real.log ((residueChar w : ℝ) * ramIdx K w / ((residueChar w : ℝ) - 1)) /
    Real.log (residueChar w)⌋.toNat))⁻¹

lemma varpiB_ne_zero : varpiB w ≠ 0 :=
  mul_ne_zero (unif_ne_zero w) (inv_ne_zero (pow_ne_zero _ (residueChar_ne_zero' w)))

lemma ordp_varpiB : ordp K w (varpiB w) = -logLatticeB (residueChar w) (ramIdx K w) := by
  have hp : (residueChar w).Prime := residueChar_prime w
  have he := ramIdx_pos' w
  obtain ⟨N, hN, -⟩ := exists_floor_logLattice_eq hp.two_le he
  unfold varpiB logLatticeB
  rw [hN, Int.toNat_natCast]
  have hpN : pw ^ N ≠ 0 := pow_ne_zero _ (residueChar_ne_zero' w)
  rw [ordp_mul w _ _ (unif_ne_zero w) (inv_ne_zero hpN), ordp_unif]
  have hinv : ordp K w (pw ^ N)⁻¹ = -(N : ℝ) := by
    have h2 : ordp K w (pw ^ N) = N := by rw [ordp_pow', ordp_residueChar, mul_one]
    have h3 : ordp K w (pw ^ N)⁻¹ = -ordp K w (pw ^ N) := by
      unfold ordp; rw [norm_inv, Real.log_inv]; ring
    rw [h3, h2]
  rw [hinv]
  push_cast
  ring

lemma norm_eq_rpow_of_ordp {x : completionAt K w} (hx : x ≠ 0) {t : ℝ} (ht : ordp K w x = t) :
    ‖x‖ = ‖pw‖ ^ t := by rw [norm_eq_rpow_ordp w hx, ht]

/-! ### The sandwich -/

/-- **`(2p)⁻¹·ϖ_a·𝓞_w ⊆ 𝓘_w`** (IUT IV, Proposition 1.2(i), first inclusion). -/
theorem mul_mem_logShell_of_norm_le_one {r : completionAt K w} (hr : ‖r‖ ≤ 1) :
    (2 * pw)⁻¹ * (varpiA w * r) ∈ PadicLogVolume.logShell (completionAt K w) (residueChar w) := by
  have hp : (residueChar w).Prime := residueChar_prime w
  have hpk : ‖((residueChar w : ℕ) : completionAt K w)‖ < 1 := norm_residueChar_lt_one w
  refine mem_logShell_of_norm_le hp hpk (ramIdx_pos' w) ?_
  rw [norm_mul, norm_eq_rpow_of_ordp w (varpiA_ne_zero w) (ordp_varpiA w)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (norm_nonneg _) _) hr

/-- **`𝓘_w ⊆ (2p)⁻¹·ϖ_b·𝓞_w`** (IUT IV, Proposition 1.2(i), second inclusion). -/
theorem norm_div_le_one_of_mem_logShell {y : completionAt K w}
    (hy : y ∈ PadicLogVolume.logShell (completionAt K w) (residueChar w)) :
    ‖y / ((2 * pw)⁻¹ * varpiB w)‖ ≤ 1 := by
  have hp : (residueChar w).Prime := residueChar_prime w
  have hpk : ‖((residueChar w : ℕ) : completionAt K w)‖ < 1 := norm_residueChar_lt_one w
  have h := norm_le_of_mem_logShell hp hpk (ramIdx_pos' w)
    (fun x hx => norm_le_rpow_of_norm_lt_one w hx) hy
  have h2p : (2 * pw) ≠ 0 := mul_ne_zero two_ne_zero (residueChar_ne_zero' w)
  have hB := norm_eq_rpow_of_ordp w (varpiB_ne_zero w) (ordp_varpiB w)
  have hBpos : 0 < ‖varpiB w‖ := norm_pos_iff.mpr (varpiB_ne_zero w)
  rw [norm_div, norm_mul, norm_inv, div_le_one (mul_pos (inv_pos.mpr (norm_pos_iff.mpr h2p))
    hBpos), hB]
  rw [← hB] at h ⊢
  rw [inv_mul_eq_div, le_div_iff₀ (norm_pos_iff.mpr h2p)]
  linarith [mul_comm ‖2 * pw‖ ‖y‖]

end LocalConstruct

end Iut
