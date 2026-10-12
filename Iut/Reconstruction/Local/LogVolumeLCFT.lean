/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Reconstruction.Local.LogVolume
import Iut.Reconstruction.Local.LogShell

/-!
# The log-volume of `Iut.logShell` is `logShellConst` (roadmap P17, M3d)

[AbsTopIII], Proposition 5.8 (iii): for a finite extension `k/ℚ_p` (residue degree `f`,
ramification index `e`, `d = [k : ℚ_p] = e f`, `#μ_{p^∞}(k) = p^m`) the log-shell
`𝓘_k = (2p)⁻¹ log 𝒪_k^×` (`Iut.logShell k p`) has volume

`μ(𝓘_k) = p^{−(f+m)} · (p*)^d · μ(𝒪_k)`   (`measure_logShell_eq`),

i.e. normalised log-volume `log(μ(𝓘_k)/μ(𝒪_k)) / d = (log p / e) · logShellConst p f e m`
(`logVolume_logShell_eq`). Here `k` carries both structures used in the project: a valuation
`Valued k ℤᵐ⁰` (the framework of `Iut.logShell`, `Iut/Concrete`) and the `ℚ_p`-algebra
structure of `local-class-field-theory` (with its norm `PadicField.nrm`, used for `e`, `f`, `q`,
`m`), and the two norms are assumed to have the same unit ball (`hball`; both unit balls are the
integral closure of `ℤ_p`).

From `card_mul_measure_logShell` (`#T · μ(𝓘_k) = [U : D] · μ(𝒪_k)`) it remains to compute:

* `[U : D] = q^{v(2p) − 1}` (`index_deepUnits_eq_pow`): the principal units and the deep units
  are the unit-filtration groups `U^{(1)}`, `U^{(v(2p))}` (`principalUnitsEquiv`,
  `map_deepUnits`), whose relative index is `relIndex_unitFilt`;
* `q^{v(2p)} = (p*)^d` (`q_pow_v_two_mul_p`);
* `#T = p^m` (`card_logKer`): the kernel of `log` on `U^{(1)}` is the group of `p`-power roots
  of unity (a `p`-power root of unity is a principal unit, and an element of `ker log` has a
  `p`-power lying in `D`, where `log` is injective).
-/

namespace Iut.Reconstruction

open MeasureTheory PadicLogVolume PadicField IsLocalRing
open scoped Valued

set_option linter.unusedSectionVars false

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]
variable {k : Type*} [Field k] [Valued k (WithZero (Multiplicative ℤ))]
  [Valuation.RankOne (Valued.v : Valuation k (WithZero (Multiplicative ℤ)))]
  [Algebra ℚ_[p] k] [FiniteDimensional ℚ_[p] k]

section Compare

variable (hball : ∀ x : k, ‖x‖ ≤ 1 ↔ nrm p k x ≤ 1)
include hball

theorem norm_le_norm_iff (x y : k) : ‖x‖ ≤ ‖y‖ ↔ nrm p k x ≤ nrm p k y := by
  by_cases hy : y = 0
  · subst hy
    rw [norm_zero, map_zero, norm_le_zero_iff]
    constructor
    · rintro rfl; rw [map_zero]
    · intro h
      exact nrm_eq_zero_iff.1 (le_antisymm h (nrm_nonneg _))
  · have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hy'' : 0 < nrm p k y := nrm_pos_iff.2 hy
    have h := hball (x / y)
    rw [norm_div, nrm_div, div_le_one hy', div_le_one hy''] at h
    exact h

theorem norm_lt_norm_iff (x y : k) : ‖x‖ < ‖y‖ ↔ nrm p k x < nrm p k y := by
  rw [← not_le, ← not_le, norm_le_norm_iff hball]

theorem norm_lt_one_iff' (x : k) : ‖x‖ < 1 ↔ nrm p k x < 1 := by
  have := norm_lt_norm_iff hball x 1
  rwa [norm_one, nrm_one] at this

end Compare

section Units

variable [CompleteSpace k] [CharZero k] (hball : ∀ x : k, ‖x‖ ≤ 1 ↔ nrm p k x ≤ 1)
include hball

omit [CompleteSpace k] in
theorem nrm_eq_one_of_principal (u : principalUnits k) : nrm p k ((u : kˣ) : k) = 1 := by
  have h1 := norm_eq_one_of_norm_sub_one_lt (norm_sub_one_lt u)
  apply le_antisymm
  · have := (norm_le_norm_iff hball ((u : kˣ) : k) 1).1 (by rw [h1, norm_one])
    rwa [nrm_one] at this
  · have := (norm_le_norm_iff hball 1 ((u : kˣ) : k)).1 (by rw [h1, norm_one])
    rwa [nrm_one] at this

/-- The principal units of the valued field `k` as units of `𝒪 p k`. -/
def toIntUnits : principalUnits k →* (𝒪 p k)ˣ where
  toFun u := unitOfNrm ((u : kˣ) : k) (nrm_eq_one_of_principal hball u)
  map_one' := Units.ext (Integers.ext (by simp [coe_unitOfNrm]))
  map_mul' x y := Units.ext (Integers.ext (by simp [coe_unitOfNrm]))

omit [CompleteSpace k] in
theorem coe_toIntUnits (u : principalUnits k) :
    (((toIntUnits hball u : (𝒪 p k)ˣ) : 𝒪 p k) : k) = ((u : kˣ) : k) := rfl

omit [CompleteSpace k] in
theorem toIntUnits_injective : Function.Injective (toIntUnits hball) := by
  intro x y h
  have := congrArg (fun w : (𝒪 p k)ˣ => ((w : 𝒪 p k) : k)) h
  simp only [coe_toIntUnits] at this
  exact Subtype.ext (Units.ext this)

omit [CompleteSpace k] in
theorem mem_unitFilt_one_iff (w : (𝒪 p k)ˣ) :
    w ∈ unitFilt p k 1 ↔ ‖((w : 𝒪 p k) : k) - 1‖ < 1 := by
  rw [mem_unitFilt, pow_one, Integers.mem_maximalIdeal_iff, norm_lt_one_iff' hball]
  simp

theorem range_toIntUnits : (toIntUnits hball).range = unitFilt p k 1 := by
  ext w
  rw [MonoidHom.mem_range, mem_unitFilt_one_iff hball]
  constructor
  · rintro ⟨u, rfl⟩
    rw [coe_toIntUnits]
    exact norm_sub_one_lt u
  · intro hw
    have hw0 : ((w : 𝒪 p k) : k) ≠ 0 := ne_zero_of_norm_sub_one_lt hw
    refine ⟨⟨Units.mk0 _ hw0, hw⟩, Units.ext (Integers.ext ?_)⟩
    rfl

variable (p k) in
/-- `v(2p)` as a natural number. -/
def vTwoP : ℕ := (v p ((2 * (p : k)) : k)).toNat

omit hball in
theorem v_two_mul_p : v p ((2 * (p : k)) : k) =
    ((if p = 2 then 2 * e p ℚ_[p] k else e p ℚ_[p] k : ℕ) : ℤ) := by
  have hp0 : (p : k) ≠ 0 := by
      exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have h20 : (2 : k) ≠ 0 := by
      exact two_ne_zero
  rw [v_mul h20 hp0, v_natCast_p_eq]
  split_ifs with h2
  · subst h2
    have : (2 : k) = ((2 : ℕ) : k) := by norm_num
    rw [this, v_natCast_p_eq]
    push_cast
    ring
  · have hcop : p.Coprime 2 := (Nat.coprime_primes hp.out Nat.prime_two).2 h2
    have hn := nrm_natCast_eq_one (K := k) hcop
    have : v p ((2 : ℕ) : k) = 0 := (nrm_eq_one_iff_v_eq_zero (by simp [h20])).1 hn
    push_cast at this
    rw [this, zero_add]

omit hball in
theorem one_le_vTwoP : 1 ≤ vTwoP p k := by
  have he := e_pos' p k
  unfold vTwoP
  rw [v_two_mul_p, Int.toNat_natCast]
  split_ifs <;> omega

omit hball in
/-- `q^{v(2p)} = (p*)^d`. -/
theorem q_pow_vTwoP : q p k ^ vTwoP p k = pStar p ^ Module.finrank ℚ_[p] k := by
  unfold vTwoP pStar
  rw [v_two_mul_p, Int.toNat_natCast]
  split_ifs with h2
  · subst h2
    rw [pow_mul', q_pow_e, ← pow_mul, mul_comm, pow_mul]
    norm_num
  · rw [q_pow_e]

theorem mem_deepUnits_iff (u : principalUnits k) :
    u ∈ deepUnits k p ↔ toIntUnits hball u ∈ unitFilt p k (vTwoP p k) := by
  change ‖((u : kˣ) : k) - 1‖ ≤ ‖2 * (p : k)‖ ↔ _
  rw [norm_le_norm_iff hball, mem_unitFilt, Integers.mem_maximalIdeal_pow_iff]
  have h2p : (2 * (p : k)) ≠ 0 := two_mul_p_ne_zero hp.out
  have hv0 : 0 ≤ v p ((2 * (p : k)) : k) := by rw [v_two_mul_p]; positivity
  have hcoe : (((toIntUnits hball u : 𝒪 p k) - 1 : 𝒪 p k) : k) = ((u : kˣ) : k) - 1 := by
    rw [Integers.coe_sub, coe_toIntUnits, Integers.coe_one]
  rw [hcoe]
  by_cases hu : ((u : kˣ) : k) - 1 = 0
  · simp only [hu, map_zero]
    constructor
    · intro _; left; exact Integers.ext (by rw [hcoe, hu]; rfl)
    · intro _; exact nrm_nonneg _
  · rw [nrm_le_iff_v_le hu h2p]
    have hne : (toIntUnits hball u : 𝒪 p k) - 1 ≠ 0 := by
      intro h
      apply hu
      rw [← hcoe, h]
      rfl
    unfold vTwoP
    rw [Int.toNat_of_nonneg hv0]
    exact ⟨fun h => Or.inr h, fun h => h.resolve_left hne⟩

theorem deepUnits_eq_comap :
    deepUnits k p = (unitFilt p k (vTwoP p k)).comap (toIntUnits hball) := by
  ext u
  rw [Subgroup.mem_comap, mem_deepUnits_iff hball]

/-- **`[U : D] = q^{v(2p) - 1}`.** -/
theorem index_deepUnits_eq_pow :
    (deepUnits k p).index = q p k ^ (vTwoP p k - 1) := by
  rw [deepUnits_eq_comap hball, Subgroup.index_comap, range_toIntUnits hball,
    relIndex_unitFilt one_ne_zero (one_le_vTwoP (p := p) (k := k))]

theorem norm_p_lt_one : ‖(p : k)‖ < 1 := by
  rw [norm_lt_one_iff' hball, show (p : k) = algebraMap ℚ_[p] k (p : ℚ_[p]) by simp,
    nrm_algebraMap, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

omit hball in
/-- A `p`-power root of unity of `𝒪` is a principal unit. -/
theorem mem_unitFilt_one_of_pow_eq_one {w : (𝒪 p k)ˣ} {J : ℕ} (h : w ^ p ^ J = 1) :
    w ∈ unitFilt p k 1 := by
  have hcop : Nat.Coprime (p ^ J) (q p k - 1) := (p_coprime_q_sub_one (p := p) (K := k)).pow_left J
  have hab := Nat.gcd_eq_gcd_ab (p ^ J) (q p k - 1)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hab
  have hw : w = (w ^ (p ^ J)) ^ (Nat.gcdA (p ^ J) (q p k - 1)) *
      (w ^ (q p k - 1)) ^ (Nat.gcdB (p ^ J) (q p k - 1)) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hab, zpow_one]
  rw [hw, h, one_zpow, one_mul]
  exact zpow_mem (pow_q_sub_one_mem_unitFilt w) _

theorem range_toIntUnits_le' : (toIntUnits hball).range = unitFilt p k 1 :=
  range_toIntUnits hball

/-- **Every element of `ker log` is a `p`-power root of unity.** -/
theorem exists_pow_eq_one_of_mem_logKer {u : principalUnits k}
    (hu : u ∈ logKer hp.out (norm_p_lt_one hball)) : ∃ j : ℕ, u ^ p ^ j = 1 := by
  set j := vTwoP p k
  refine ⟨j, ?_⟩
  have h1 : toIntUnits hball u ∈ unitFilt p k 1 := by
    rw [← range_toIntUnits hball]; exact ⟨u, rfl⟩
  have h2 := pow_p_pow_mem_unitFilt h1 j
  have h3 : mSeq (e p ℚ_[p] k) j ≥ j := (succ_le_mSeq (e_pos' p k) j).trans' (Nat.le_succ j)
  have hD : u ^ p ^ j ∈ deepUnits k p := by
    rw [deepUnits_eq_comap hball, Subgroup.mem_comap, map_pow]
    exact unitFilt_anti h3 h2
  have hT : u ^ p ^ j ∈ logKer hp.out (norm_p_lt_one hball) := pow_mem hu _
  exact (Subgroup.disjoint_def.1 (disjoint_deepUnits_logKer hp.out (norm_p_lt_one hball))) hD hT

omit hball in
/-- An index `J` with `#μ_{p^J}(k) = #μ_{p^∞}(k)`. -/
theorem exists_muCard_eq_muPInf : ∃ J, muCard p k J = muPInf p k := by
  have hne : (Set.range (muCard p k)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  exact Nat.sSup_mem hne bddAbove_muCard

theorem logKer_eq_comap {J : ℕ} (hJ : muCard p k J = muPInf p k) :
    logKer hp.out (norm_p_lt_one hball) =
      (powMonoidHom (p ^ J) : (𝒪 p k)ˣ →* (𝒪 p k)ˣ).ker.comap (toIntUnits hball) := by
  ext u
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, powMonoidHom_apply]
  constructor
  · intro hu
    obtain ⟨j, hj⟩ := exists_pow_eq_one_of_mem_logKer hball hu
    set K' := (powMonoidHom (p ^ (j + J)) : (𝒪 p k)ˣ →* (𝒪 p k)ˣ).ker
    set KJ := (powMonoidHom (p ^ J) : (𝒪 p k)ˣ →* (𝒪 p k)ˣ).ker
    have hle : KJ ≤ K' := by
      intro w hw
      rw [MonoidHom.mem_ker, powMonoidHom_apply] at hw ⊢
      rw [pow_add, pow_mul', hw, one_pow]
    haveI : Finite K' := Nat.finite_of_card_ne_zero (muCard_pos (p := p) (K := k) (j + J)).ne'
    have hcard : Nat.card K' ≤ Nat.card KJ := by
      change muCard p k (j + J) ≤ muCard p k J
      rw [hJ]
      exact le_ciSup bddAbove_muCard (j + J)
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    have hmem : toIntUnits hball u ∈ K' := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply, pow_add, pow_mul, ← map_pow, hj, map_one,
        one_pow]
    rw [← heq] at hmem
    exact hmem
  · intro hu
    have h1 : u ^ p ^ J = 1 := by
      apply toIntUnits_injective hball
      rw [map_pow, hu, map_one]
    change Multiplicative.ofAdd (padicLog ((u : kˣ) : k)) = 1
    rw [padicLog_eq_zero_of_pow_eq_one hp.out (norm_p_lt_one hball) (norm_sub_one_lt u)
      (pow_ne_zero J hp.out.ne_zero) (by
        have := congrArg (fun w : principalUnits k => ((w : kˣ) : k)) h1
        simpa using this)]
    rfl

/-- **`#ker(log|_U) = #μ_{p^∞}(k) = p^m`.** -/
theorem card_logKer :
    Nat.card (logKer hp.out (norm_p_lt_one hball)) = p ^ mExp p k := by
  obtain ⟨J, hJ⟩ := exists_muCard_eq_muPInf (p := p) (k := k)
  set P := (powMonoidHom (p ^ J) : (𝒪 p k)ˣ →* (𝒪 p k)ˣ).ker
  have hP : P ≤ (toIntUnits hball).range := by
    rw [range_toIntUnits hball]
    intro w hw
    exact mem_unitFilt_one_of_pow_eq_one ((MonoidHom.mem_ker).1 hw)
  rw [logKer_eq_comap hball hJ, ← muPInf_eq_pow, ← hJ]
  have e1 := Subgroup.equivMapOfInjective (P.comap (toIntUnits hball)) (toIntUnits hball)
    (toIntUnits_injective hball)
  rw [Subgroup.map_comap_eq, inf_of_le_right hP] at e1
  exact Nat.card_congr e1.toEquiv

variable [ProperSpace k] [MeasurableSpace k] [BorelSpace k]

/-- **[AbsTopIII], Proposition 5.8 (iii): the volume of the log-shell**,
`p^{f+m} · μ(𝓘_k) = (p*)^d · μ(𝒪_k)`. -/
theorem measure_logShell_eq (μ : Measure k) [μ.IsAddLeftInvariant] :
    (p : ENNReal) ^ (f p ℚ_[p] k + mExp p k) * μ (logShell k p) =
      (pStar p : ENNReal) ^ Module.finrank ℚ_[p] k * μ (Metric.closedBall 0 1) := by
  have h := card_mul_measure_logShell hp.out (norm_p_lt_one hball) μ
  rw [card_logKer hball, index_deepUnits_eq_pow hball] at h
  have hq : (q p k : ENNReal) = (p : ENNReal) ^ f p ℚ_[p] k := by
    rw [q_eq_p_pow_f]; push_cast; rfl
  have hn := one_le_vTwoP (p := p) (k := k)
  have hqn : (q p k : ENNReal) * (q p k : ENNReal) ^ (vTwoP p k - 1) =
      (pStar p : ENNReal) ^ Module.finrank ℚ_[p] k := by
    rw [← pow_succ', Nat.sub_add_cancel hn]
    exact_mod_cast q_pow_vTwoP (p := p) (k := k)
  rw [pow_add, mul_assoc, ← hq, ← hqn, mul_assoc]
  push_cast at h
  rw [h]

/-- **The normalised log-volume of `Iut.logShell` is given by `logShellConst`**:
`log(μ(𝓘_k)/μ(𝒪_k)) / [k : ℚ_p] = (log p / e) · logShellConst p f e m`. -/
theorem logVolume_logShell_eq (μ : Measure k) [μ.IsAddLeftInvariant]
    (h0 : μ (Metric.closedBall 0 1) ≠ 0) (hfin : μ (Metric.closedBall 0 1) ≠ ⊤) :
    Real.log ((μ (logShell k p)).toReal / (μ (Metric.closedBall 0 1)).toReal) /
        Module.finrank ℚ_[p] k =
      logShellConst p (f p ℚ_[p] k) (e p ℚ_[p] k) (mExp p k) * Real.log p / e p ℚ_[p] k := by
  have h := measure_logShell_eq hball μ
  set A := μ (logShell k p)
  set B := μ (Metric.closedBall (0 : k) 1)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hB : 0 < B.toReal := ENNReal.toReal_pos h0 hfin
  have hAfin : A ≠ ⊤ := by
    intro hA
    rw [hA, ENNReal.mul_top (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))] at h
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) hfin h.symm
  have hR := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hR
  have hps : (0 : ℝ) < pStar p := by
    unfold pStar; split_ifs <;> positivity
  have hratio : A.toReal / B.toReal =
      (pStar p : ℝ) ^ Module.finrank ℚ_[p] k / (p : ℝ) ^ (f p ℚ_[p] k + mExp p k) := by
    rw [div_eq_div_iff hB.ne' (pow_pos hp0 _).ne']
    linarith
  have hf : 0 < f p ℚ_[p] k := f_pos
  have he : 0 < e p ℚ_[p] k := e_pos' p k
  have hd : Module.finrank ℚ_[p] k = e p ℚ_[p] k * f p ℚ_[p] k := (e_mul_f).symm
  have hL := logShellConst_mul (p := p) (f := f p ℚ_[p] k) (e := e p ℚ_[p] k)
    (m := mExp p k) hp.out.one_lt hf
  rw [hratio, Real.log_div (pow_pos hps _).ne' (pow_pos hp0 _).ne', Real.log_pow,
    Real.log_pow, hd]
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hf' : (f p ℚ_[p] k : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he' : (e p ℚ_[p] k : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  field_simp
  push_cast at hL ⊢
  linear_combination (-(e p ℚ_[p] k : ℝ)) * hL

end Units

end

end Iut.Reconstruction
