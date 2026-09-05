/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Volume

/-!
# The admissible class of the holomorphic hull (taxis #4, #278)

The **admissible regions** of a packet (IUT III, Remark 3.9.5(i)) are the nonempty,
relatively compact, measurable regions of positive finite Haar measure (`admissible`, the
field `LocalTheory.admissible`). This file proves `admissible_nonempty`,
`admissible_relCompact`, `integral_admissible`, `smul_integral_admissible`, and restates
the scaling law of the log-volume for admissible regions.

## Least hull regions

At the archimedean place the hull regions are the real radial scalings `t·B_I` (`t > 0`)
of the product of unit balls, and the least one containing an admissible region `U` is
`t·B_I` with `t = sup_{x ∈ U} ‖x‖_π`, the supremum of the projective norm over `U`
(`exists_leastHull_infinite`, the field `LocalTheory.exists_leastHull_infinite`); it is
positive because a region of positive Haar measure is not contained in `{0}`. The radial
scalings are monotone in `t` (`smul_integralAt_infinite_mono`).

## Least hull regions at a prime

At a prime, the existence of a *least* hull region `a·(R_I)^∼` (`a` a unit) containing an
admissible region is proved in `Hull.lean` (`exists_leastHull_finite`), through the
decomposition of the packet `⊗_j K_{c j}` into the product of its residue fields
(`ResidueField.lean`), for which `(R_I)^∼` is the product of the rings of integers and the
hull regions are the products of closed balls, whose least upper bound is computed
componentwise. For the order `R_I = ⊗_{ℤ_p} 𝓞_{c j}` (as opposed to its normalization)
least hull regions need not exist at all, since `R_I` is in general only an order in the
ring of integers of the packet.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

variable (vQ : RationalPlace) (c : ι → Place K)

/-- **The admissible class** of the holomorphic hull: nonempty, relatively compact,
measurable regions of positive finite Haar measure (`LocalTheory.admissible`). -/
def admissible : Set (Set (Tensor K vQ c)) :=
  {S | S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧ 0 < haar vQ c S ∧ haar vQ c S < ⊤}

variable {vQ c}

lemma mem_admissible {S : Set (Tensor K vQ c)} :
    S ∈ admissible vQ c ↔
      S.Nonempty ∧ IsCompact (closure S) ∧ MeasurableSet S ∧ 0 < haar vQ c S ∧ haar vQ c S < ⊤ :=
  Iff.rfl

/-- Admissible regions are nonempty (`LocalTheory.admissible_nonempty`). -/
lemma admissible_nonempty {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) : U.Nonempty :=
  hU.1

/-- Admissible regions are relatively compact (`LocalTheory.admissible_relCompact`). -/
lemma admissible_relCompact {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    IsCompact (closure U) :=
  hU.2.1

lemma admissible_measurableSet {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    MeasurableSet U :=
  hU.2.2.1

lemma admissible_haar_pos {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    0 < haar vQ c U :=
  hU.2.2.2.1

lemma admissible_haar_lt_top {U : Set (Tensor K vQ c)} (hU : U ∈ admissible vQ c) :
    haar vQ c U < ⊤ :=
  hU.2.2.2.2

/-- Scaled integral structures are admissible (`LocalTheory.smul_integral_admissible`). -/
lemma smul_integral_admissible (a : Tensor K vQ c) (ha : IsUnit a) :
    a • integralAt vQ c ∈ admissible vQ c :=
  ⟨(integralAt_nonempty vQ c).smul_set,
    by rw [(isCompact_smul_integralAt a).isClosed.closure_eq]; exact isCompact_smul_integralAt a,
    measurableSet_smul_integralAt a, haar_smul_integralAt_pos ha, haar_smul_integralAt_lt_top a⟩

/-- The integral structure is admissible (`LocalTheory.integral_admissible`). -/
lemma integral_admissible : integralAt vQ c ∈ admissible vQ c := by
  simpa using smul_integral_admissible (vQ := vQ) (c := c) 1 isUnit_one

/-- The scaling law of the log-volume at `p` for admissible regions. -/
theorem componentVol_prime_preimage_of_admissible (p : Nat.Primes) (hc : ∀ j, IsOver K p (c j))
    {U : Set (Tensor K (.finite p) c)} (hU : U ∈ admissible (.finite p) c) :
    componentVol (.finite p) c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      componentVol (.finite p) c U + Real.log p :=
  componentVol_prime_preimage' p hc U (admissible_measurableSet hU) (admissible_haar_pos hU).ne'
    (admissible_haar_lt_top hU).ne

/-! ### Least real radial scalings of `B_I` -/

variable (c)

/-- `x ∈ t·B_I ↔ ‖x‖_π ≤ t`, for `t > 0`. -/
lemma mem_algebraMap_smul_archIntegral {t : ℝ} (ht : 0 < t) {x : Tensor K .infinite c} :
    x ∈ algebraMap ℝ (Tensor K .infinite c) t • archIntegral c ↔ archNorm c x ≤ t := by
  rw [algebraMap_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    calc archNorm c (t • y) ≤ |t| * archNorm c y := archNorm_smul_le c t y
      _ ≤ t * 1 := by
          rw [abs_of_pos ht]
          exact mul_le_mul_of_nonneg_left hy ht.le
      _ = t := mul_one t
  · intro hx
    refine ⟨t⁻¹ • x, ?_, smul_inv_smul₀ ht.ne' x⟩
    change archNorm c (t⁻¹ • x) ≤ 1
    calc archNorm c (t⁻¹ • x) ≤ |t⁻¹| * archNorm c x := archNorm_smul_le c _ x
      _ ≤ t⁻¹ * t := by
          rw [abs_of_pos (inv_pos.mpr ht)]
          exact mul_le_mul_of_nonneg_left hx (inv_pos.mpr ht).le
      _ = 1 := inv_mul_cancel₀ ht.ne'

/-- **Radial monotonicity of `B_I`**: `t·B_I ⊆ t'·B_I` for `0 < t ≤ t'`
(`LocalTheory.smul_integral_infinite_mono`). -/
theorem smul_integralAt_infinite_mono (t t' : ℝ) (ht : 0 < t) (htt' : t ≤ t') :
    algebraMap ℝ (Tensor K .infinite c) t • integralAt .infinite c ⊆
      algebraMap ℝ (Tensor K .infinite c) t' • integralAt .infinite c := by
  rw [integralAt_infinite]
  intro x hx
  exact (mem_algebraMap_smul_archIntegral c (ht.trans_le htt')).mpr
    (((mem_algebraMap_smul_archIntegral c ht).mp hx).trans htt')

/-- **Existence of least hull regions at the archimedean place**
(`LocalTheory.exists_leastHull_infinite`): an admissible region `U` is contained in the
least radial scaling `t·B_I`, with `t = sup_{x ∈ U} ‖x‖_π > 0`. -/
theorem exists_leastHull_infinite {U : Set (Tensor K .infinite c)}
    (hU : U ∈ admissible .infinite c) :
    ∃ t : ℝ, 0 < t ∧ U ⊆ algebraMap ℝ (Tensor K .infinite c) t • integralAt .infinite c ∧
      ∀ t' : ℝ, 0 < t' →
        U ⊆ algebraMap ℝ (Tensor K .infinite c) t' • integralAt .infinite c → t ≤ t' := by
  rw [integralAt_infinite]
  have hbdd : BddAbove (archNorm c '' U) :=
    ((admissible_relCompact hU).image (continuous_archNorm c)).bddAbove.mono
      (Set.image_mono subset_closure)
  have hne : (archNorm c '' U).Nonempty := (admissible_nonempty hU).image _
  have hle : ∀ x ∈ U, archNorm c x ≤ sSup (archNorm c '' U) := fun x hx =>
    le_csSup hbdd ⟨x, hx, rfl⟩
  have ht0 : 0 ≤ sSup (archNorm c '' U) := by
    obtain ⟨x, hx⟩ := admissible_nonempty hU
    exact (archNorm_nonneg c x).trans (hle x hx)
  have htpos : 0 < sSup (archNorm c '' U) := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    exfalso
    have hsub : U ⊆ {0} := by
      intro x hx
      have h0 : archNorm c x = 0 :=
        le_antisymm ((hle x hx).trans h.symm.le) (archNorm_nonneg c x)
      obtain ⟨C, -, hC⟩ := exists_norm_le_archNorm c
      have hx0 : ‖x‖ ≤ 0 := by
        have := hC x
        rwa [h0, mul_zero] at this
      exact norm_le_zero_iff.mp hx0
    haveI : Nontrivial (Tensor K .infinite c) :=
      Module.nontrivial_of_finrank_pos (finrank_tensor_infinite_pos (c := c))
    exact absurd (admissible_haar_pos hU) (not_lt.mpr ((measure_mono hsub).trans
      (measure_singleton (0 : Tensor K .infinite c)).le))
  refine ⟨_, htpos, fun x hx => ?_, fun t' ht' hUt' => ?_⟩
  · exact (mem_algebraMap_smul_archIntegral c htpos).mpr (hle x hx)
  · refine csSup_le hne ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_algebraMap_smul_archIntegral c ht').mp (hUt' hx)

end LocalConstruct

end Iut
