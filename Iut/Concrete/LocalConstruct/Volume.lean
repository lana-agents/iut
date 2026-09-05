/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.MaximalOrder
import Iut.Concrete.LocalConstruct.Archimedean
import Iut.Concrete.LocalConstruct.Haar

/-!
# The normalized Haar log-volume of the tensor packets (taxis #4, #278)

This file constructs the fields `LocalTheory.integral` (uniformly in the rational place,
`integralAt`) and `LocalTheory.componentVol` of `Iut.LocalTheory K`, and proves
`componentVol_integral`, `componentVol_mono`, `componentVol_arch_scale`, and the
nonarchimedean scaling law `componentVol_prime_preimage'` (see the remark below).

The **normalized log-volume** of a region `S` of the packet `T = ⊗_j K_{c j}` is
`μ^log(S) := log(μ(S)/μ(I)) / [T : ℚ_p]` (resp. `/ [T : ℝ]`), where `μ` is a Haar measure
on `T` and `I` the integral structure (`(R_I)^∼` at a prime, `B_I` at `∞`): the normalization
`μ^log(I) = 0` is built in, and dividing by the degree makes multiplication by `p` (which
scales `μ` by `p^{[T : ℚ_p]}`) shift `μ^log` by `log p`, and scaling by `t > 0` at `∞`
shift it by `log t` (IUT III, Proposition 3.9(i),(ii)).

## Remark on `LocalTheory.componentVol_prime_preimage`

The field `componentVol_prime_preimage` of `LocalTheory` is stated for *every* set `U`;
for `U = ∅` it reads `μ^log(∅) = μ^log(∅) + log p`, which is false for any real-valued
`μ^log`. The correct statement — proved here as `componentVol_prime_preimage'` — is for
sets of positive finite Haar measure (e.g. admissible regions), in a packet all of whose
places lie over `p`.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory NumberField
open scoped Pointwise TensorProduct

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Measurable structure -/

noncomputable instance instMeasurableSpaceBaseField (vQ : RationalPlace) :
    MeasurableSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (MeasurableSpace ℚ_[p])
  | .infinite => inferInstanceAs (MeasurableSpace ℝ)

instance instBorelSpaceBaseField (vQ : RationalPlace) : BorelSpace (baseField vQ) :=
  match vQ with
  | .finite p => inferInstanceAs (BorelSpace ℚ_[p])
  | .infinite => inferInstanceAs (BorelSpace ℝ)

variable {ι : Type} [Fintype ι]

/-- The Borel σ-algebra of a packet. -/
noncomputable instance instMeasurableSpaceTensor (vQ : RationalPlace) (c : ι → Place K) :
    MeasurableSpace (Tensor K vQ c) := borel _

instance instBorelSpaceTensor (vQ : RationalPlace) (c : ι → Place K) :
    BorelSpace (Tensor K vQ c) := ⟨rfl⟩

noncomputable instance (p : Nat.Primes) (c : ι → Place K) :
    MeasurableSpace (Tensor K (.finite p) c) := instMeasurableSpaceTensor (.finite p) c

instance (p : Nat.Primes) (c : ι → Place K) : BorelSpace (Tensor K (.finite p) c) :=
  instBorelSpaceTensor (.finite p) c

noncomputable instance (c : ι → Place K) : MeasurableSpace (Tensor K .infinite c) :=
  instMeasurableSpaceTensor .infinite c

instance (c : ι → Place K) : BorelSpace (Tensor K .infinite c) := instBorelSpaceTensor .infinite c

/-- **A Haar measure on the packet.** -/
noncomputable def haar (vQ : RationalPlace) (c : ι → Place K) : Measure (Tensor K vQ c) :=
  Measure.addHaar

instance (vQ : RationalPlace) (c : ι → Place K) : (haar vQ c).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaar : Measure (Tensor K vQ c)).IsAddHaarMeasure

instance (p : Nat.Primes) (c : ι → Place K) : (haar (.finite p) c).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaar : Measure (Tensor K (.finite p) c)).IsAddHaarMeasure

instance (c : ι → Place K) : (haar .infinite c).IsAddHaarMeasure :=
  inferInstanceAs (Measure.addHaar : Measure (Tensor K .infinite c)).IsAddHaarMeasure

/-! ### The integral structure, uniformly in the rational place -/

/-- **The integral structure** of a packet (`LocalTheory.integral`): the maximal order
`(R_I)^∼` at a prime, `B_I` at the archimedean place. -/
noncomputable def integralAt : ∀ (vQ : RationalPlace) (c : ι → Place K), Set (Tensor K vQ c)
  | .finite p, c => integral p c
  | .infinite, c => archIntegral c

lemma integralAt_finite (p : Nat.Primes) (c : ι → Place K) :
    integralAt (.finite p) c = integral p c := rfl

lemma integralAt_infinite (c : ι → Place K) : integralAt .infinite c = archIntegral c := rfl

variable (vQ : RationalPlace) (c : ι → Place K)

/-- `1 ∈ I` (`LocalTheory.one_mem_integral`). -/
lemma one_mem_integralAt : (1 : Tensor K vQ c) ∈ integralAt vQ c := by
  cases vQ with
  | finite p => exact one_mem_integral p c
  | infinite => exact one_mem_archIntegral c

lemma isCompact_integralAt : IsCompact (integralAt vQ c) := by
  cases vQ with
  | finite p => exact isCompact_integral p c
  | infinite => exact isCompact_archIntegral c

lemma isClosed_integralAt : IsClosed (integralAt vQ c) := (isCompact_integralAt vQ c).isClosed

lemma measurableSet_integralAt : MeasurableSet (integralAt vQ c) :=
  (isClosed_integralAt vQ c).measurableSet

lemma integralAt_nonempty : (integralAt vQ c).Nonempty := ⟨1, one_mem_integralAt vQ c⟩

/-- The integral structure contains a nonempty open set. -/
lemma exists_isOpen_subset_integralAt :
    ∃ U : Set (Tensor K vQ c), IsOpen U ∧ U.Nonempty ∧ U ⊆ integralAt vQ c := by
  cases vQ with
  | finite p => exact ⟨integral p c, isOpen_integral p c, integral_nonempty p c, subset_rfl⟩
  | infinite =>
    obtain ⟨r, hr, hsub⟩ := exists_ball_subset_archIntegral c
    exact ⟨Metric.ball 0 r, Metric.isOpen_ball, ⟨0, Metric.mem_ball_self hr⟩, hsub⟩

/-! ### Units act by homeomorphisms -/

/-- Multiplication by a unit of the packet, as a homeomorphism. -/
noncomputable def mulUnitHomeomorph (a : (Tensor K vQ c)ˣ) : Tensor K vQ c ≃ₜ Tensor K vQ c where
  toFun x := a * x
  invFun x := ↑a⁻¹ * x
  left_inv x := Units.inv_mul_cancel_left a x
  right_inv x := Units.mul_inv_cancel_left a x
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

lemma smul_set_eq_image (a : Tensor K vQ c) (S : Set (Tensor K vQ c)) :
    a • S = (fun x => a * x) '' S := (Set.image_smul).symm

lemma smul_set_eq_image_unit (a : (Tensor K vQ c)ˣ) (S : Set (Tensor K vQ c)) :
    (a : Tensor K vQ c) • S = mulUnitHomeomorph vQ c a '' S := smul_set_eq_image vQ c _ S

variable {vQ c}

lemma isCompact_smul (a : Tensor K vQ c) {S : Set (Tensor K vQ c)}
    (hS : IsCompact S) : IsCompact (a • S) := by
  rw [smul_set_eq_image]
  exact hS.image (continuous_const.mul continuous_id)

lemma isOpen_smul_of_isUnit {a : Tensor K vQ c} (ha : IsUnit a) {S : Set (Tensor K vQ c)}
    (hS : IsOpen S) : IsOpen (a • S) := by
  obtain ⟨u, rfl⟩ := ha
  rw [smul_set_eq_image_unit]
  exact (mulUnitHomeomorph vQ c u).isOpenMap _ hS

lemma isCompact_smul_integralAt (a : Tensor K vQ c) :
    IsCompact (a • integralAt vQ c) :=
  isCompact_smul a (isCompact_integralAt vQ c)

lemma measurableSet_smul_integralAt (a : Tensor K vQ c) :
    MeasurableSet (a • integralAt vQ c) :=
  (isCompact_smul_integralAt a).isClosed.measurableSet

lemma haar_smul_integralAt_pos {a : Tensor K vQ c} (ha : IsUnit a) :
    0 < haar vQ c (a • integralAt vQ c) := by
  obtain ⟨U, hUo, hUne, hUsub⟩ := exists_isOpen_subset_integralAt vQ c
  refine lt_of_lt_of_le ((isOpen_smul_of_isUnit ha hUo).measure_pos _ ?_)
    (measure_mono (Set.smul_set_mono hUsub))
  obtain ⟨x, hx⟩ := hUne
  exact ⟨a • x, Set.smul_mem_smul_set hx⟩

lemma haar_smul_integralAt_lt_top (a : Tensor K vQ c) :
    haar vQ c (a • integralAt vQ c) < ⊤ :=
  (isCompact_smul_integralAt a).measure_lt_top

lemma haar_integralAt_pos : 0 < haar vQ c (integralAt vQ c) := by
  simpa using haar_smul_integralAt_pos (vQ := vQ) (c := c) isUnit_one

lemma haar_integralAt_lt_top : haar vQ c (integralAt vQ c) < ⊤ :=
  (isCompact_integralAt vQ c).measure_lt_top

lemma toReal_haar_integralAt_pos : 0 < (haar vQ c (integralAt vQ c)).toReal :=
  ENNReal.toReal_pos (haar_integralAt_pos).ne' (haar_integralAt_lt_top).ne

/-! ### The normalized log-volume -/

variable (vQ c) in
/-- **The normalized Haar log-volume** `μ^log(S) = log(μ(S)/μ(I)) / [T : ℚ_{v_ℚ}]`
(`LocalTheory.componentVol`). -/
noncomputable def componentVol (S : Set (Tensor K vQ c)) : ℝ :=
  Real.log ((haar vQ c S).toReal / (haar vQ c (integralAt vQ c)).toReal) /
    Module.finrank (baseField vQ) (Tensor K vQ c)

/-- `μ^log(I) = 0` (`LocalTheory.componentVol_integral`). -/
theorem componentVol_integral : componentVol vQ c (integralAt vQ c) = 0 := by
  unfold componentVol
  rw [div_self (toReal_haar_integralAt_pos).ne', Real.log_one, zero_div]

/-- **Monotonicity of the log-volume between hull regions** (`LocalTheory.componentVol_mono`). -/
theorem componentVol_mono (a b : Tensor K vQ c) (ha : IsUnit a) (_hb : IsUnit b)
    (h : a • integralAt vQ c ⊆ b • integralAt vQ c) :
    componentVol vQ c (a • integralAt vQ c) ≤ componentVol vQ c (b • integralAt vQ c) := by
  unfold componentVol
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  refine Real.log_le_log (div_pos (ENNReal.toReal_pos (haar_smul_integralAt_pos ha).ne'
    (haar_smul_integralAt_lt_top a).ne) (toReal_haar_integralAt_pos)) ?_
  refine div_le_div_of_nonneg_right ?_ (toReal_haar_integralAt_pos).le
  exact ENNReal.toReal_mono (haar_smul_integralAt_lt_top b).ne (measure_mono h)

/-! ### Dimensions -/

/-- The dimension of a packet is the number of elementary tensors of the chosen bases. -/
lemma finrank_tensor_eq_card :
    Module.finrank (baseField vQ) (Tensor K vQ c) = Fintype.card (PacketIndex vQ c) :=
  Module.finrank_eq_card_basis (packetBasis vQ c)

/-- Archimedean packets are nontrivial. -/
lemma finrank_tensor_infinite_pos :
    0 < Module.finrank (baseField .infinite) (Tensor K .infinite c) := by
  rw [finrank_tensor_eq_card, Fintype.card_pos_iff]
  exact ⟨fun j => ⟨0, Module.finrank_pos⟩⟩

/-- A packet at `p` all of whose places lie over `p` is nontrivial. -/
lemma finrank_tensor_finite_pos (p : Nat.Primes) (hc : ∀ j, IsOver K p (c j)) :
    0 < Module.finrank (baseField (.finite p)) (Tensor K (.finite p) c) := by
  rw [finrank_tensor_eq_card, Fintype.card_pos_iff]
  refine ⟨fun j => ⟨0, ?_⟩⟩
  haveI := nontrivial_factor p (c j) (hc j)
  exact Module.finrank_pos

/-! ### Archimedean scaling -/

lemma algebraMap_smul_set (t : ℝ) (S : Set (Tensor K .infinite c)) :
    algebraMap ℝ (Tensor K .infinite c) t • S = t • S := by
  ext x
  simp only [Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, Algebra.smul_def t y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (Algebra.smul_def t y).symm⟩

/-- **Archimedean radial scaling** `μ^log(t·B_I) = log t`
(`LocalTheory.componentVol_arch_scale`). -/
theorem componentVol_arch_scale (t : ℝ) (ht : 0 < t) :
    componentVol .infinite c (algebraMap ℝ (Tensor K .infinite c) t • integralAt .infinite c) =
      Real.log t := by
  rw [algebraMap_smul_set]
  unfold componentVol
  rw [Measure.addHaar_smul (haar .infinite c), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (pow_pos ht _), mul_div_assoc,
    div_self (toReal_haar_integralAt_pos).ne', mul_one]
  have hn : (Module.finrank (baseField .infinite) (Tensor K .infinite c) : ℝ) ≠ 0 := by
    exact_mod_cast (finrank_tensor_infinite_pos (c := c)).ne'
  rw [show Module.finrank ℝ (Tensor K .infinite c) =
    Module.finrank (baseField .infinite) (Tensor K .infinite c) from rfl, Real.log_pow,
    mul_div_cancel_left₀ _ hn]

/-! ### Nonarchimedean scaling -/

/-- Multiplication by `p` on a packet at `p` is the scalar action of `p ∈ ℚ_p`. -/
lemma natCast_mul_eq_smul (p : Nat.Primes) (x : Tensor K (.finite p) c) :
    ((p : ℕ) : Tensor K (.finite p) c) * x = ((p : ℕ) : ℚ_[p]) • x := by
  rw [Algebra.smul_def, map_natCast]

/-- **The scaling law of the log-volume at `p`**: `μ^log(p⁻¹·U) = μ^log(U) + log p` for
every measurable `U` of positive finite Haar measure, in a packet all of whose places lie over
`p` (the corrected form of `LocalTheory.componentVol_prime_preimage`, see the module
docstring). -/
theorem componentVol_prime_preimage' (p : Nat.Primes) (hc : ∀ j, IsOver K p (c j))
    (U : Set (Tensor K (.finite p) c)) (hU : MeasurableSet U)
    (h0 : haar (.finite p) c U ≠ 0) (hfin : haar (.finite p) c U ≠ ⊤) :
    componentVol (.finite p) c ((fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U) =
      componentVol (.finite p) c U + Real.log p := by
  have hpre : (fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹' U =
      (fun x => ((p : ℕ) : ℚ_[p]) • x) ⁻¹' U := by
    ext x
    simp only [Set.mem_preimage]
    rw [natCast_mul_eq_smul]
  have hscale := measure_preimage_smul_padic (p := (p : ℕ)) (haar (.finite p) c) hU
  set n := Module.finrank ℚ_[p] (Tensor K (.finite p) c) with hn
  have hn' : Module.finrank (baseField (.finite p)) (Tensor K (.finite p) c) = n := rfl
  have hnpos : (0 : ℝ) < n := by
    have := finrank_tensor_finite_pos p hc
    rw [hn'] at this
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : (p : ℕ).Prime).pos
  have hU0 : 0 < (haar (.finite p) c U).toReal := ENNReal.toReal_pos h0 hfin
  unfold componentVol
  rw [hpre, hscale, hn', ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    mul_div_assoc,
    Real.log_mul (pow_ne_zero _ hp0.ne') (div_pos hU0 toReal_haar_integralAt_pos).ne',
    Real.log_pow, add_div, mul_div_cancel_left₀ _ hnpos.ne', add_comm]

end LocalConstruct

end Iut
