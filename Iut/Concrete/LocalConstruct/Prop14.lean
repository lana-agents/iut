/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Concrete.LocalConstruct.Volume
import Iut.Concrete.LocalConstruct.Arithmetic

/-!
# IUT IV, Proposition 1.4(iii) for the concrete packets (taxis #4, #278)

The field `LocalTheory.prop14_iii` asks, for a scaling element `x ∈ K_w` of the `j`-th
factor of a packet at `p` with `ord_p(x) = λ ≥ 0`, for a unit `a` of the packet such that
the images `φ(x·(R_I)^∼)` under all indeterminacy automorphisms lie in `a·(R_I)^∼`, with

`μ^log(a·(R_I)^∼) ≤ (−λ + ∑_i d_i + 1)·log p + ∑_{p − 2 < e_i} (3 + log e_i)`.

For the maximal order `(R_I)^∼` — the integral closure of `ℤ_p` in the packet — the hull
region can be taken to be `p^{⌊λ⌋}·(R_I)^∼` (`prop14iii_of_isOver`): the indeterminacy
automorphisms are `ℚ_p`-algebra automorphisms, so they fix `p^{⌊λ⌋}` and preserve
`(R_I)^∼` (`mapAlgHom_image_integral_subset`), while `x/p^{⌊λ⌋}` is integral; and
`μ^log(p^m·(R_I)^∼) = −m·log p` by the scaling law `componentVol_prime_preimage'`
(`componentVol_prime_pow_smul_integral`), which is at most `(−λ + 1)·log p`. The
different exponents and the ramification terms of the bound are nonnegative and are not
needed: the sharper bound of IUT IV, Proposition 1.4(iii) concerns the log-shell `𝓘_I`
rather than `(R_I)^∼`, whose hull is controlled by the different; the field as stated is
about `(R_I)^∼` and is implied by the elementary estimate.

## The hypothesis that every place lies over `p`

The field carries, like `LocalTheory.componentVol_prime_preimage`, the hypothesis that
every component of the packet lies over `p` (in the form `∀ j, IsOver K p (c j)` here),
satisfied by every tuple of the fiber over `p` to which it is applied
(`LocalTheory.tuple_isOver`). It cannot be dropped: a packet with a component not over `p`
is the zero ring (`subsingleton_tensor_of_not_isOver`), where every region is `{0}` and the
log-volume vanishes identically (`componentVol_eq_zero_of_not_isOver`), while the bound is
negative as soon as `ord_p(x)` exceeds `∑_i d_i + 1 + (∑_i (3 + log e_i))/log p`.
-/

namespace Iut

namespace LocalConstruct

open NumberField
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]

/-! ### Elementary bounds -/

/-- Ramification indices of places are at least `1`. -/
lemma one_le_ramIdxAt (v : Place K) : 1 ≤ ramIdxAt K v := by
  cases v with
  | inl w => exact ramIdx_pos w
  | inr w => exact le_rfl

/-- The ramification terms of the bound of Proposition 1.4(iii) are nonnegative. -/
lemma ramTerm_nonneg (p : Nat.Primes) (v : Place K) :
    0 ≤ if (p : ℕ) - 2 < ramIdxAt K v then 3 + Real.log (ramIdxAt K v) else 0 := by
  split_ifs
  · have h1 : (1 : ℝ) ≤ ramIdxAt K v := by exact_mod_cast one_le_ramIdxAt v
    linarith [Real.log_nonneg h1]
  · exact le_rfl

/-- The different exponents are nonnegative. -/
lemma differentExponent_nonneg (w : FinitePlace K) : 0 ≤ differentExponent K w :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- `ord_p(x / ℓ^m) = ord_p(x) − m`, `ℓ` the residue characteristic of `w`. -/
lemma ordp_div_residueChar_pow (w : FinitePlace K) (x : completionAt K w) (hx : x ≠ 0)
    (m : ℕ) :
    ordp K w (x / (residueChar w : completionAt K w) ^ m) = ordp K w x - m := by
  have hℓ : (residueChar w : completionAt K w) ≠ 0 := by
    rw [← map_natCast (algebraMap K (completionAt K w))]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (residueChar_prime w).ne_zero)
  have hpow : (residueChar w : completionAt K w) ^ m ≠ 0 := pow_ne_zero _ hℓ
  have h1 : ordp K w ((residueChar w : completionAt K w) ^ m) = m := by
    rw [ordp_pow', ← map_natCast (algebraMap K (completionAt K w)), ordp_p, mul_one]
  have h2 := ordp_mul w (x / (residueChar w : completionAt K w) ^ m)
    ((residueChar w : completionAt K w) ^ m) (div_ne_zero hx hpow) hpow
  rw [div_mul_cancel₀ x hpow, h1] at h2
  linarith

section Prime

variable (p : Nat.Primes) (c : ι → Place K)

/-! ### The log-volume of `p^m·(R_I)^∼` -/

/-- `p` is a unit of the packet. -/
lemma isUnit_natCast_prime : IsUnit ((p : ℕ) : Tensor K (.finite p) c) := by
  rw [← map_natCast (algebraMap ℚ_[p] (Tensor K (.finite p) c))]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr p.2.ne_zero)).map _

/-- The preimage of `p^{m+1}·(R_I)^∼` under multiplication by `p` is `p^m·(R_I)^∼`. -/
lemma preimage_mul_prime_pow_succ_smul_integral (m : ℕ) :
    (fun x => ((p : ℕ) : Tensor K (.finite p) c) * x) ⁻¹'
        (((p : ℕ) : Tensor K (.finite p) c) ^ (m + 1) • integral p c) =
      ((p : ℕ) : Tensor K (.finite p) c) ^ m • integral p c := by
  ext x
  simp only [Set.mem_preimage, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    rw [pow_succ', mul_assoc] at hxy
    exact (isUnit_natCast_prime p c).mul_left_cancel hxy
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [pow_succ', mul_assoc]⟩

/-- **`μ^log(p^m·(R_I)^∼) = −m·log p`**, in a packet all of whose places lie over `p`. -/
theorem componentVol_prime_pow_smul_integral (hc : ∀ j, IsOver K p (c j)) (m : ℕ) :
    componentVol (.finite p) c (((p : ℕ) : Tensor K (.finite p) c) ^ m • integral p c) =
      -(m : ℝ) * Real.log p := by
  induction m with
  | zero =>
    rw [pow_zero, one_smul, Nat.cast_zero, neg_zero, zero_mul]
    exact componentVol_integral
  | succ m ih =>
    have hunit : IsUnit (((p : ℕ) : Tensor K (.finite p) c) ^ (m + 1)) :=
      (isUnit_natCast_prime p c).pow _
    have h := componentVol_prime_preimage' p hc
      (((p : ℕ) : Tensor K (.finite p) c) ^ (m + 1) • integral p c)
      (measurableSet_smul_integralAt (vQ := .finite p) _)
      (haar_smul_integralAt_pos (vQ := .finite p) hunit).ne'
      (haar_smul_integralAt_lt_top (vQ := .finite p) _).ne
    rw [preimage_mul_prime_pow_succ_smul_integral, ih] at h
    push_cast
    linarith

/-! ### Containment of the indeterminacy images -/

/-- **The images of `x·(R_I)^∼` under the indeterminacy automorphisms lie in
`n^m·(R_I)^∼`** as soon as `x/n^m` is integral. -/
theorem indAut_image_smul_integral_subset (j : ι) (w : FinitePlace K)
    (h : c j = Place.finite w) (x : completionAt K w) (n m : ℕ)
    (hn : (n : completionAt K w) ^ m ≠ 0) (hx : ‖x / (n : completionAt K w) ^ m‖ ≤ 1)
    {φ : Tensor K (.finite p) c → Tensor K (.finite p) c} (hφ : φ ∈ indAut (.finite p) c) :
    φ '' (incl p c j w h x • integral p c) ⊆
      ((n : ℕ) : Tensor K (.finite p) c) ^ m • integral p c := by
  obtain ⟨σ, rfl⟩ := hφ
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hx' : incl p c j w h (x / (n : completionAt K w) ^ m) ∈ integral p c :=
    incl_mem_integral p c j w h _ hx
  refine ⟨mapAlgHom (.finite p) c σ (incl p c j w h (x / (n : completionAt K w) ^ m)) *
    mapAlgHom (.finite p) c σ y, mul_mem_integral p c
      (mapAlgHom_image_integral_subset p c σ ⟨_, hx', rfl⟩)
      (mapAlgHom_image_integral_subset p c σ ⟨y, hy, rfl⟩), ?_⟩
  have hxeq : x = (n : completionAt K w) ^ m * (x / (n : completionAt K w) ^ m) :=
    (mul_div_cancel₀ x hn).symm
  conv_rhs => rw [hxeq]
  simp only [smul_eq_mul, map_mul, map_pow, map_natCast]
  ring

/-! ### Proposition 1.4(iii) for the packets over `p` -/

/-- **IUT IV, Proposition 1.4(iii)** for the concrete packets all of whose places lie over
`p` (the field `LocalTheory.prop14_iii` under the hypothesis of
`LocalTheory.componentVol_prime_preimage`): the hull region is `p^{⌊ord_p x⌋}·(R_I)^∼`. -/
theorem prop14iii_of_isOver (hc : ∀ j, IsOver K p (c j)) (d : ι → ℝ) (j : ι)
    (w : FinitePlace K) (h : c j = Place.finite w) (x : completionAt K w) (hx : x ≠ 0)
    (hord : 0 ≤ ordp K w x)
    (hd : ∀ i w', c i = Place.finite w' → d i = differentExponent K w') :
    ∃ a : Tensor K (.finite p) c, IsUnit a ∧
      (∀ φ ∈ indAut (.finite p) c,
        φ '' (incl p c j w h x • integral p c) ⊆ a • integral p c) ∧
      componentVol (.finite p) c (a • integral p c) ≤
        (-ordp K w x + ∑ i, d i + 1) * Real.log p +
          ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then
            3 + Real.log (ramIdxAt K (c i)) else 0 := by
  have hw : residueChar w = p := by
    have := hc j
    rw [h, isOver_finite_iff] at this
    exact this
  set m : ℕ := ⌊ordp K w x⌋₊ with hm
  refine ⟨((p : ℕ) : Tensor K (.finite p) c) ^ m, (isUnit_natCast_prime p c).pow _, ?_, ?_⟩
  · intro φ hφ
    have hn : ((p : ℕ) : completionAt K w) ^ m ≠ 0 := by
      rw [← hw, ← map_natCast (algebraMap K (completionAt K w))]
      exact pow_ne_zero _
        ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (residueChar_prime w).ne_zero))
    refine indAut_image_smul_integral_subset p c j w h x p m hn ?_ hφ
    refine norm_le_one_of_ordp_nonneg ?_
    rw [← hw, ordp_div_residueChar_pow w x hx, sub_nonneg]
    exact Nat.floor_le hord
  · rw [componentVol_prime_pow_smul_integral p c hc]
    have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast p.2.one_lt)
    have hm1 : ordp K w x < m + 1 := Nat.lt_floor_add_one _
    have hd0 : 0 ≤ ∑ i, d i := Finset.sum_nonneg fun i _ => by
      obtain ⟨w', hw', -⟩ := hc i
      rw [hd i w' hw']
      exact differentExponent_nonneg w'
    have hs0 : 0 ≤ ∑ i, if (p : ℕ) - 2 < ramIdxAt K (c i) then
        3 + Real.log (ramIdxAt K (c i)) else 0 :=
      Finset.sum_nonneg fun i _ => ramTerm_nonneg p (c i)
    have hmle : -(m : ℝ) ≤ -ordp K w x + ∑ i, d i + 1 := by linarith
    calc -(m : ℝ) * Real.log p ≤ (-ordp K w x + ∑ i, d i + 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hmle hlogp.le
      _ ≤ _ := le_add_of_nonneg_right hs0

/-! ### The junk packets -/

/-- The log-volume vanishes identically on a packet with a place not over `p` (the zero
ring, whose dimension is `0`). -/
lemma componentVol_eq_zero_of_not_isOver (i : ι) (hi : ¬ IsOver K p (c i))
    (S : Set (Tensor K (.finite p) c)) : componentVol (.finite p) c S = 0 := by
  haveI := subsingleton_tensor_of_not_isOver p c i hi
  unfold componentVol
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, div_zero]

end Prime

end LocalConstruct

end Iut
