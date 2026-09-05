/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Mathlib

/-!
# Haar measure on finite-dimensional `p`-adic vector spaces: the modulus of `p` (taxis #4)

Mathlib provides Haar measures on locally compact groups but no computation of the
modulus of scaling by `p` on `ℚ_p`. We prove:

* `Iut.LocalConstruct.measure_preimage_mul_padic`: for an additive Haar measure `μ` on
  `ℚ_p` and a measurable set `s`, `μ (p⁻¹·s) = p · μ s` — from the decomposition of the
  ball of radius `p` into `p` translates of `ℤ_p`;
* `Iut.LocalConstruct.measure_preimage_smul_padic`: for an additive Haar measure `μ` on a
  finite-dimensional `ℚ_p`-vector space `E` of dimension `n`, `μ (p⁻¹·s) = p^n · μ s` —
  by transport to `ℚ_p^n` and the product measure.

Here `p⁻¹·s` denotes the preimage `{x | p • x ∈ s}`. These are the inputs of the
normalization `μ^log(p⁻¹·U) = μ^log(U) + log p` of the log-volume (IUT III,
Proposition 3.9(i)).

`ℚ_p` receives its Borel σ-algebra as an instance here.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : MeasurableSpace ℚ_[p] := borel _

instance : BorelSpace ℚ_[p] := ⟨rfl⟩

instance : SecondCountableTopology ℚ_[p] :=
  haveI : TopologicalSpace.SeparableSpace ℚ_[p] :=
    ⟨⟨Set.range ((↑) : ℚ → ℚ_[p]), Set.countable_range _, Padic.denseRange_ratCast p⟩⟩
  UniformSpace.secondCountable_of_separable _

lemma padic_natCast_ne_zero : ((p : ℕ) : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Multiplication by `p` on `ℚ_p`, as a continuous linear automorphism. -/
noncomputable def mulPadic : ℚ_[p] ≃L[ℚ_[p]] ℚ_[p] :=
  (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] (p : ℚ_[p])
    (padic_natCast_ne_zero p)).toContinuousLinearEquiv

lemma mulPadic_apply (x : ℚ_[p]) : mulPadic p x = (p : ℚ_[p]) * x := rfl

/-! ### The ball of radius `p` as a union of `p` translates of `ℤ_p` -/

/-- The translate of the unit ball by `i / p`. -/
noncomputable def padicCoset (i : Fin p) : Set ℚ_[p] :=
  (fun x => -(((i : ℕ) : ℚ_[p]) / p) + x) ⁻¹' Metric.closedBall 0 1

lemma mem_padicCoset {i : Fin p} {x : ℚ_[p]} :
    x ∈ padicCoset p i ↔ ‖x - ((i : ℕ) : ℚ_[p]) / p‖ ≤ 1 := by
  simp only [padicCoset, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, neg_add_eq_sub]

lemma measurableSet_padicCoset (i : Fin p) : MeasurableSet (padicCoset p i) :=
  measurableSet_closedBall.preimage (by fun_prop)

lemma closedBall_eq_iUnion_padicCoset :
    Metric.closedBall (0 : ℚ_[p]) p = ⋃ i : Fin p, padicCoset p i := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpq := padic_natCast_ne_zero p
  ext x
  simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_iUnion, mem_padicCoset]
  constructor
  · intro hx
    have hpx : ‖(p : ℚ_[p]) * x‖ ≤ 1 := by
      rw [norm_mul, Padic.norm_p]
      calc (p : ℝ)⁻¹ * ‖x‖ ≤ (p : ℝ)⁻¹ * p := mul_le_mul_of_nonneg_left hx (by positivity)
        _ = 1 := inv_mul_cancel₀ hp0.ne'
    let z : ℤ_[p] := ⟨(p : ℚ_[p]) * x, hpx⟩
    refine ⟨⟨z.zmodRepr, z.zmodRepr_lt_p⟩, ?_⟩
    have hmem := z.sub_zmodRepr_mem
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    obtain ⟨y, hy⟩ := hmem
    have hy' : (p : ℚ_[p]) * x - (z.zmodRepr : ℚ_[p]) = (p : ℚ_[p]) * (y : ℚ_[p]) := by
      have := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hy
      simpa [z] using this
    have : x - (z.zmodRepr : ℚ_[p]) / p = (y : ℚ_[p]) := by
      field_simp
      linear_combination hy'
    rw [this]
    exact PadicInt.norm_le_one y
  · rintro ⟨i, hi⟩
    have hi' : ‖((i : ℕ) : ℚ_[p]) / p‖ ≤ p := by
      rw [norm_div, Padic.norm_p, div_inv_eq_mul]
      have hi1 : ‖((i : ℕ) : ℚ_[p])‖ ≤ 1 := by
        have := PadicInt.norm_le_one ((i : ℕ) : ℤ_[p])
        rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
      calc ‖((i : ℕ) : ℚ_[p])‖ * p ≤ 1 * p := mul_le_mul_of_nonneg_right hi1 hp0.le
        _ = p := one_mul _
    calc ‖x‖ = ‖(x - ((i : ℕ) : ℚ_[p]) / p) + ((i : ℕ) : ℚ_[p]) / p‖ := by ring_nf
      _ ≤ max ‖x - ((i : ℕ) : ℚ_[p]) / p‖ ‖((i : ℕ) : ℚ_[p]) / p‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ p := max_le (hi.trans (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)) hi'

lemma norm_sub_le_max' {x y : ℚ_[p]} : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [norm_neg])

lemma pairwise_disjoint_padicCoset :
    Pairwise fun i j : Fin p => Disjoint (padicCoset p i) (padicCoset p j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [mem_padicCoset] at hxi hxj
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpq := padic_natCast_ne_zero p
  set d : ℤ := ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) with hd
  have h1 : ‖(d : ℚ_[p]) / p‖ ≤ 1 := by
    have : (d : ℚ_[p]) / p = (x - ((j : ℕ) : ℚ_[p]) / p) - (x - ((i : ℕ) : ℚ_[p]) / p) := by
      rw [hd]
      push_cast
      ring
    rw [this]
    exact (norm_sub_le_max' p).trans (max_le hxj hxi)
  have h2 : ‖(d : ℚ_[p])‖ < 1 := by
    rw [norm_div, Padic.norm_p, div_inv_eq_mul] at h1
    have hinv : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    calc ‖(d : ℚ_[p])‖ = ‖(d : ℚ_[p])‖ * p * (p : ℝ)⁻¹ := (mul_inv_cancel_right₀ hp0.ne' _).symm
      _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < 1 := by rwa [one_mul]
  rw [Padic.norm_intCast_lt_one_iff] at h2
  have h3 : d = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h2 ?_
    rw [hd, abs_lt]
    constructor <;> omega
  exact hij (Fin.ext (by omega))

/-! ### The modulus of `p` on `ℚ_p` -/

variable {p}

/-- `μ(ball(0, p)) = p · μ(ℤ_p)` for an additive Haar measure `μ` on `ℚ_p`. -/
lemma measure_closedBall_padic (μ : Measure ℚ_[p]) [μ.IsAddLeftInvariant] :
    μ (Metric.closedBall (0 : ℚ_[p]) p) = p * μ (Metric.closedBall 0 1) := by
  rw [closedBall_eq_iUnion_padicCoset, measure_iUnion (pairwise_disjoint_padicCoset p)
    (measurableSet_padicCoset p)]
  have : ∀ i : Fin p, μ (padicCoset p i) = μ (Metric.closedBall 0 1) := fun i =>
    measure_preimage_add _ _ _
  simp [this]

/-- **The modulus of `p` on `ℚ_p`**: `μ(p⁻¹·s) = p · μ(s)`. -/
theorem measure_preimage_mul_padic (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] {s : Set ℚ_[p]}
    (hs : MeasurableSet s) : μ ((fun x => (p : ℚ_[p]) * x) ⁻¹' s) = p * μ s := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set f := mulPadic p
  have hf : ⇑f = fun x => (p : ℚ_[p]) * x := rfl
  have hmap := Measure.isAddLeftInvariant_eq_smul (μ.map f) μ
  set c := Measure.addHaarScalarFactor (μ.map f) μ
  have hB : MeasurableSet (Metric.closedBall (0 : ℚ_[p]) 1) := measurableSet_closedBall
  have hpre : (fun x => (p : ℚ_[p]) * x) ⁻¹' Metric.closedBall (0 : ℚ_[p]) 1 =
      Metric.closedBall 0 p := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, norm_mul, Padic.norm_p]
    rw [inv_mul_le_iff₀ hp0, mul_one]
  have hBpos : μ (Metric.closedBall (0 : ℚ_[p]) 1) ≠ 0 :=
    ((IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero).measure_pos μ
      ⟨0, by simp⟩).ne'
  have hBfin : μ (Metric.closedBall (0 : ℚ_[p]) 1) ≠ ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hc : (c : ENNReal) = p := by
    have h1 := congrArg (fun ν : Measure ℚ_[p] => ν (Metric.closedBall 0 1)) hmap
    simp only [Measure.smul_apply, ENNReal.smul_def] at h1
    rw [Measure.map_apply f.continuous.measurable hB, hf, hpre, measure_closedBall_padic μ] at h1
    exact ((ENNReal.mul_left_inj hBpos hBfin).mp h1).symm
  calc μ ((fun x => (p : ℚ_[p]) * x) ⁻¹' s) = (μ.map f) s := by
        rw [Measure.map_apply f.continuous.measurable hs, hf]
    _ = p * μ s := by rw [hmap, Measure.smul_apply, ENNReal.smul_def, hc, smul_eq_mul]

/-! ### The modulus of `p` on a finite-dimensional `ℚ_p`-vector space -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [MeasurableSpace E] [BorelSpace E]

/-- The modulus of `p` on `ℚ_p^n` (for the product Haar measure). -/
lemma pi_measure_preimage_smul_padic {n : Type*} [Fintype n] {s : Set (n → ℚ_[p])}
    (hs : MeasurableSet s) :
    Measure.pi (fun _ : n => (Measure.addHaar : Measure ℚ_[p])) ((fun x => (p : ℚ_[p]) • x) ⁻¹' s) =
      (p : ENNReal) ^ Fintype.card n *
        Measure.pi (fun _ : n => (Measure.addHaar : Measure ℚ_[p])) s := by
  set μ₁ : Measure ℚ_[p] := Measure.addHaar
  set π := Measure.pi fun _ : n => μ₁
  have hg : Measurable fun x : n → ℚ_[p] => (p : ℚ_[p]) • x := by fun_prop
  have hpn : ((p : ENNReal) ^ Fintype.card n) ≠ 0 := by
    have : (p : ENNReal) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    exact pow_ne_zero _ this
  have hpn' : ((p : ENNReal) ^ Fintype.card n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have key : π = ((p : ENNReal) ^ Fintype.card n)⁻¹ • π.map fun x => (p : ℚ_[p]) • x := by
    refine Measure.pi_eq fun t ht => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hg (MeasurableSet.pi Set.countable_univ
      fun i _ => ht i)]
    have : (fun x : n → ℚ_[p] => (p : ℚ_[p]) • x) ⁻¹' Set.pi Set.univ t =
        Set.pi Set.univ fun i => (fun y => (p : ℚ_[p]) * y) ⁻¹' t i := by
      ext x
      simp [Set.mem_pi, Pi.smul_apply, smul_eq_mul]
    rw [this, Measure.pi_pi]
    simp only [measure_preimage_mul_padic μ₁ (ht _)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← mul_assoc,
      ENNReal.inv_mul_cancel hpn hpn', one_mul]
  calc π ((fun x => (p : ℚ_[p]) • x) ⁻¹' s) = (π.map fun x => (p : ℚ_[p]) • x) s := by
        rw [Measure.map_apply hg hs]
    _ = (p : ENNReal) ^ Fintype.card n * π s := by
        conv_rhs => rw [key]
        rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hpn hpn', one_mul]

/-- **The modulus of `p` on a finite-dimensional `ℚ_p`-vector space** `E` of dimension `n`:
`μ(p⁻¹·s) = p^n · μ(s)` for every additive Haar measure `μ` and measurable `s`. -/
theorem measure_preimage_smul_padic (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E}
    (hs : MeasurableSet s) :
    μ ((fun x => (p : ℚ_[p]) • x) ⁻¹' s) = (p : ENNReal) ^ Module.finrank ℚ_[p] E * μ s := by
  haveI : SecondCountableTopology E :=
    (Module.finBasis ℚ_[p] E).equivFunL.toHomeomorph.isInducing.secondCountableTopology
  set e := (Module.finBasis ℚ_[p] E).equivFunL
  set ê := e.toHomeomorph.toMeasurableEquiv
  have hê : ⇑ê = ⇑e := rfl
  set ν := μ.map e
  set π := Measure.pi fun _ : Fin (Module.finrank ℚ_[p] E) => (Measure.addHaar : Measure ℚ_[p])
  set c := Measure.addHaarScalarFactor ν π
  have hν : ν = c • π := Measure.isAddLeftInvariant_eq_smul ν π
  have hmap : ∀ t : Set E, μ t = ν (e '' t) := by
    intro t
    have : μ t = (μ.map ê) (ê '' t) := by
      rw [MeasurableEquiv.map_apply, ê.injective.preimage_image]
    rw [this]
    rfl
  have himage : e '' ((fun x => (p : ℚ_[p]) • x) ⁻¹' s) =
      (fun x => (p : ℚ_[p]) • x) ⁻¹' (e '' s) := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(p : ℚ_[p]) • x, hx, by rw [map_smul]⟩
    · rintro ⟨x, hx, hxy⟩
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      have : (p : ℚ_[p]) • e.symm y = x := by
        apply e.injective
        rw [map_smul, e.apply_symm_apply, hxy]
      rw [this]
      exact hx
  have hs' : MeasurableSet (e '' s) := ê.measurableSet_image.mpr hs
  calc μ ((fun x => (p : ℚ_[p]) • x) ⁻¹' s)
      = ν (e '' ((fun x => (p : ℚ_[p]) • x) ⁻¹' s)) := hmap _
    _ = ν ((fun x => (p : ℚ_[p]) • x) ⁻¹' (e '' s)) := by rw [himage]
    _ = c • π ((fun x => (p : ℚ_[p]) • x) ⁻¹' (e '' s)) := by rw [hν, Measure.smul_apply]
    _ = c • ((p : ENNReal) ^ Module.finrank ℚ_[p] E * π (e '' s)) := by
        rw [pi_measure_preimage_smul_padic hs', Fintype.card_fin]
    _ = (p : ENNReal) ^ Module.finrank ℚ_[p] E * (c • π (e '' s)) := by
        simp only [ENNReal.smul_def, smul_eq_mul, mul_left_comm]
    _ = (p : ENNReal) ^ Module.finrank ℚ_[p] E * ν (e '' s) := by rw [hν, Measure.smul_apply]
    _ = (p : ENNReal) ^ Module.finrank ℚ_[p] E * μ s := by rw [hmap s]

end FiniteDimensional

end LocalConstruct

end Iut
