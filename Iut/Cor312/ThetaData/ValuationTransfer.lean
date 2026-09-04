/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Cor312.ThetaData.ReductionNorm
import Iut.Cor312.ThetaData.PlacesOver
import Mathlib.NumberTheory.RamificationInertia.Valuation

/-!
# Valuation transfer along places of an extension

For number fields `k ⊆ K` and finite places `w | v` (`Iut.FinitePlace.LiesOver w v`):

* **valuation transfer**: the `w`-adic valuation of `algebraMap k K x` is the `e`-th power
  of the `v`-adic valuation of `x` (Mathlib's
  `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`), so the conditions `≤ 1`, `< 1`,
  `= 1` transfer (`Iut.valuation_algebraMap_le_one_iff`, …), also for the norms on the
  completions (`Iut.norm_emb_algebraMap_le_one_iff`, …);
* **integral approximation**: an element of `K` which is `w`-integral is congruent modulo
  the maximal ideal to an element of `𝓞_K` (`Iut.exists_ringOfIntegers_sub_mem`);
* **residue degree one**: if `f(w/v) = 1`, the residue map `𝓞_k/v → 𝓞_K/w` is surjective
  (`Iut.exists_algebraMap_sub_mem_of_inertiaDeg_eq_one`);
* **two places above `v` in a quadratic extension** have `e = f = 1`
  (`Iut.inertiaDeg'_eq_one_of_ne`, `Iut.ramificationIdx'_eq_one_of_ne`), from the fundamental
  identity `∑ e f = [K : k]`.
-/

namespace Iut

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped WithZero

variable {k K : Type*} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]

/-! ## Valuation transfer -/

section Norm

variable {w : FinitePlace K}

/-- The norm on the completion `K_w` of the image of `y ∈ K`, in terms of the valuation. -/
lemma norm_emb_le_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ ≤ 1 ↔
      w.maximalIdeal.valuation K y ≤ 1 := by
  rw [norm_le_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

lemma norm_emb_lt_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ < 1 ↔
      w.maximalIdeal.valuation K y < 1 := by
  rw [norm_lt_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

lemma norm_emb_eq_one_iff (y : K) :
    ‖(FinitePlace.embedding w.maximalIdeal y : localCompletion w)‖ = 1 ↔
      w.maximalIdeal.valuation K y = 1 := by
  rw [norm_eq_one_iff_valued, FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation']

end Norm

section Transfer

variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

/-- The ramification index of `w` over `v` is nonzero. -/
lemma ramificationIdx'_ne_zero :
    v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal ≠ 0 := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ v.maximalIdeal.ne_bot

/-- `w(x) = v(x)^e` for `x ∈ k`, where `e` is the ramification index of `w` over `v`. -/
lemma valuation_algebraMap_eq_pow (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) =
      v.maximalIdeal.valuation k x ^
        v.maximalIdeal.asIdeal.ramificationIdx' w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  exact (valuation_liesOver K v.maximalIdeal w.maximalIdeal x).symm

lemma valuation_algebraMap_le_one_iff (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) ≤ 1 ↔ v.maximalIdeal.valuation k x ≤ 1 := by
  rw [valuation_algebraMap_eq_pow hwv]
  exact pow_le_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hwv)

lemma valuation_algebraMap_lt_one_iff (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) < 1 ↔ v.maximalIdeal.valuation k x < 1 := by
  rw [valuation_algebraMap_eq_pow hwv]
  exact pow_lt_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hwv)

lemma valuation_algebraMap_eq_one_iff (x : k) :
    w.maximalIdeal.valuation K (algebraMap k K x) = 1 ↔ v.maximalIdeal.valuation k x = 1 := by
  rw [valuation_algebraMap_eq_pow hwv]
  exact pow_eq_one_iff_of_nonneg zero_le (ramificationIdx'_ne_zero hwv)

lemma norm_emb_algebraMap_le_one_iff (x : k) :
    ‖(FinitePlace.embedding w.maximalIdeal (algebraMap k K x) : localCompletion w)‖ ≤ 1 ↔
      ‖(FinitePlace.embedding v.maximalIdeal x : localCompletion v)‖ ≤ 1 := by
  rw [norm_le_one_iff_valued, norm_le_one_iff_valued, FinitePlace.embedding_apply,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    valuedAdicCompletion_eq_valuation']
  exact valuation_algebraMap_le_one_iff hwv x

lemma norm_emb_algebraMap_lt_one_iff (x : k) :
    ‖(FinitePlace.embedding w.maximalIdeal (algebraMap k K x) : localCompletion w)‖ < 1 ↔
      ‖(FinitePlace.embedding v.maximalIdeal x : localCompletion v)‖ < 1 := by
  rw [norm_lt_one_iff_valued, norm_lt_one_iff_valued, FinitePlace.embedding_apply,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    valuedAdicCompletion_eq_valuation']
  exact valuation_algebraMap_lt_one_iff hwv x

lemma norm_emb_algebraMap_eq_one_iff (x : k) :
    ‖(FinitePlace.embedding w.maximalIdeal (algebraMap k K x) : localCompletion w)‖ = 1 ↔
      ‖(FinitePlace.embedding v.maximalIdeal x : localCompletion v)‖ = 1 := by
  rw [norm_eq_one_iff_valued, norm_eq_one_iff_valued, FinitePlace.embedding_apply,
    FinitePlace.embedding_apply, valuedAdicCompletion_eq_valuation',
    valuedAdicCompletion_eq_valuation']
  exact valuation_algebraMap_eq_one_iff hwv x

end Transfer

/-! ## Integral approximation -/

section Approx

variable (w : FinitePlace K)

/-- An element `x ∈ K` with `w(x) ≤ 1` is congruent modulo the maximal ideal to an element of
`𝓞_K`: there is `a ∈ 𝓞_K` with `w(x - a) < 1`. -/
lemma exists_ringOfIntegers_sub_mem (x : K) (hx : w.maximalIdeal.valuation K x ≤ 1) :
    ∃ a : 𝓞 K, w.maximalIdeal.valuation K (x - algebraMap (𝓞 K) K a) < 1 := by
  set P := w.maximalIdeal with hP
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb' : algebraMap (𝓞 K) K b ≠ 0 := by
    rw [ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact hb0
  have hvb : 0 < P.intValuation b := by
    rw [pos_iff_ne_zero]
    exact P.intValuation_ne_zero b hb0
  -- the `w`-adic order `m` of the denominator
  set m : ℕ := multiplicity P.asIdeal (Ideal.span {b}) with hm
  have hbm : P.intValuation b = WithZero.exp (-(m : ℤ)) :=
    intValuation_eq_exp_neg_multiplicity P hb0
  have hb_mem : b ∈ P.asIdeal ^ m := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, hbm]
  have hb_notMem : b ∉ P.asIdeal ^ (m + 1) := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, hbm, WithZero.exp_le_exp]
    omega
  have ha_mem : a ∈ P.asIdeal ^ m := by
    rw [← Ideal.dvd_span_singleton, ← intValuation_le_pow_iff_dvd, ← hbm]
    rw [map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, div_le_one₀ hvb] at hx
    exact hx
  obtain ⟨d, e, he, hde⟩ :=
    Ideal.exists_mul_add_mem_pow_succ P.ne_bot b a hb_mem hb_notMem ha_mem
  refine ⟨d, ?_⟩
  have hxd : algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b - algebraMap (𝓞 K) K d =
      algebraMap (𝓞 K) K e / algebraMap (𝓞 K) K b := by
    rw [eq_div_iff hb', sub_mul, div_mul_cancel₀ _ hb', ← hde, map_add, map_mul]
    ring
  rw [hxd, map_div₀, valuation_of_algebraMap, valuation_of_algebraMap, div_lt_one₀ hvb, hbm]
  refine lt_of_le_of_lt ((intValuation_le_pow_iff_dvd P e (m + 1)).2
    (Ideal.dvd_span_singleton.2 he)) ?_
  rw [WithZero.exp_lt_exp]
  omega

end Approx

/-! ## Residue degree one -/

section Residue

variable {w : FinitePlace K} {v : FinitePlace k} (hwv : FinitePlace.LiesOver w v)
include hwv

/-- If the residue degree of `w` over `v` is `1`, the residue map `𝓞_k/v → 𝓞_K/w` is
surjective: every `a ∈ 𝓞_K` is congruent modulo `w` to an element of `𝓞_k`. -/
lemma exists_algebraMap_sub_mem_of_inertiaDeg_eq_one
    (hf : v.maximalIdeal.asIdeal.inertiaDeg' w.maximalIdeal.asIdeal = 1) (a : 𝓞 K) :
    ∃ b : 𝓞 k, algebraMap (𝓞 k) (𝓞 K) b - a ∈ w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  letI : Field (𝓞 k ⧸ v.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 K ⧸ w.maximalIdeal.asIdeal) := Ideal.Quotient.field _
  rw [Ideal.inertiaDeg'_algebraMap,
    finrank_eq_one_iff_of_nonzero' (1 : 𝓞 K ⧸ w.maximalIdeal.asIdeal) one_ne_zero] at hf
  obtain ⟨c, hc⟩ := hf (Ideal.Quotient.mk _ a)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_mk_of_liesOver] at hc
  exact Ideal.Quotient.eq.1 hc

end Residue

/-! ## Two places above a place in a quadratic extension -/

section Quadratic

variable {v : FinitePlace k}

/-- If `[K : k] ≤ 2` and two distinct places `w₁ ≠ w₂` of `K` lie over `v`, then
`e(w₁/v) f(w₁/v) = 1`. -/
lemma ramificationIdx'_mul_inertiaDeg'_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    v.maximalIdeal.asIdeal.ramificationIdx' w₁.maximalIdeal.asIdeal *
      v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal = 1 := by
  classical
  haveI : w₁.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := h₁
  haveI : w₂.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := h₂
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  have hp0 : v.maximalIdeal.asIdeal ≠ ⊥ := v.maximalIdeal.ne_bot
  have hsum := Ideal.sum_ramification_inertia (𝓞 K) k K hp0 (p := v.maximalIdeal.asIdeal)
  have hmem₁ : w₁.maximalIdeal.asIdeal ∈ IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, h₁⟩
  have hmem₂ : w₂.maximalIdeal.asIdeal ∈ IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 K)).mpr ⟨inferInstance, h₂⟩
  have hne' : w₁.maximalIdeal.asIdeal ≠ w₂.maximalIdeal.asIdeal := fun h =>
    hne ((FinitePlace.maximalIdeal_inj _ _).mp (HeightOneSpectrum.ext h))
  have hsub : ({w₁.maximalIdeal.asIdeal, w₂.maximalIdeal.asIdeal} : Finset (Ideal (𝓞 K))) ⊆
      IsDedekindDomain.primesOverFinset v.maximalIdeal.asIdeal (𝓞 K) := by
    intro P hP
    simp only [Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl
    · exact hmem₁
    · exact hmem₂
  have hle := Finset.sum_le_sum_of_subset (f := fun P : Ideal (𝓞 K) =>
    v.maximalIdeal.asIdeal.ramificationIdx' P * v.maximalIdeal.asIdeal.inertiaDeg' P) hsub
  rw [Finset.sum_pair hne', hsum] at hle
  have he₁ : 0 < v.maximalIdeal.asIdeal.ramificationIdx' w₁.maximalIdeal.asIdeal :=
    Nat.pos_of_ne_zero (ramificationIdx'_ne_zero h₁)
  have he₂ : 0 < v.maximalIdeal.asIdeal.ramificationIdx' w₂.maximalIdeal.asIdeal :=
    Nat.pos_of_ne_zero (ramificationIdx'_ne_zero h₂)
  have hf₁ : 0 < v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal :=
    Ideal.inertiaDeg'_pos _ _
  have hf₂ : 0 < v.maximalIdeal.asIdeal.inertiaDeg' w₂.maximalIdeal.asIdeal :=
    Ideal.inertiaDeg'_pos _ _
  have h1 := Nat.mul_pos he₁ hf₁
  have h2 := Nat.mul_pos he₂ hf₂
  omega

/-- If `[K : k] ≤ 2` and two distinct places of `K` lie over `v`, then the residue degree of
each is `1`. -/
lemma inertiaDeg'_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    v.maximalIdeal.asIdeal.inertiaDeg' w₁.maximalIdeal.asIdeal = 1 :=
  Nat.eq_one_of_mul_eq_one_left (ramificationIdx'_mul_inertiaDeg'_eq_one_of_ne hK hne h₁ h₂)

/-- If `[K : k] ≤ 2` and two distinct places of `K` lie over `v`, then the ramification index of
each is `1`. -/
lemma ramificationIdx'_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    v.maximalIdeal.asIdeal.ramificationIdx' w₁.maximalIdeal.asIdeal = 1 :=
  Nat.eq_one_of_mul_eq_one_right (ramificationIdx'_mul_inertiaDeg'_eq_one_of_ne hK hne h₁ h₂)

/-- `Iut.inertiaDeg'_eq_one_of_ne` for Mathlib's `Ideal.inertiaDeg`. -/
lemma inertiaDeg_eq_one_of_ne (hK : Module.finrank k K ≤ 2)
    {w₁ w₂ : FinitePlace K} (hne : w₁ ≠ w₂) (h₁ : FinitePlace.LiesOver w₁ v)
    (h₂ : FinitePlace.LiesOver w₂ v) :
    w₁.maximalIdeal.asIdeal.inertiaDeg (𝓞 k) = 1 := by
  haveI : w₁.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := h₁
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : w₁.maximalIdeal.asIdeal.IsMaximal :=
    w₁.maximalIdeal.isPrime.isMaximal w₁.maximalIdeal.ne_bot
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg v.maximalIdeal.asIdeal]
  exact inertiaDeg'_eq_one_of_ne hK hne h₁ h₂

/-- The surjectivity of the residue map, stated with Mathlib's `Ideal.inertiaDeg`. -/
lemma exists_algebraMap_sub_mem_of_inertiaDeg_eq_one' {w : FinitePlace K}
    (hwv : FinitePlace.LiesOver w v) (hf : w.maximalIdeal.asIdeal.inertiaDeg (𝓞 k) = 1)
    (a : 𝓞 K) : ∃ b : 𝓞 k, algebraMap (𝓞 k) (𝓞 K) b - a ∈ w.maximalIdeal.asIdeal := by
  haveI : w.maximalIdeal.asIdeal.LiesOver v.maximalIdeal.asIdeal := hwv
  haveI : v.maximalIdeal.asIdeal.IsMaximal :=
    v.maximalIdeal.isPrime.isMaximal v.maximalIdeal.ne_bot
  haveI : w.maximalIdeal.asIdeal.IsMaximal :=
    w.maximalIdeal.isPrime.isMaximal w.maximalIdeal.ne_bot
  refine exists_algebraMap_sub_mem_of_inertiaDeg_eq_one hwv ?_ a
  rw [Ideal.inertiaDeg'_eq_inertiaDeg v.maximalIdeal.asIdeal]
  exact hf

end Quadratic

end Iut
