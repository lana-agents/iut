/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Volume
import Iut.Concrete.LocalConstruct.Arithmetic

/-!
# Integrality of elementary scalings of a packet (IUT IV, Proposition 1.4)

Let `T = ⊗_j K_{w_j}` be a nonarchimedean packet at `p`, all of whose places lie over `p`, and
let `y_j ∈ K_{w_j}^×`. The *elementary scaling* `z = ∏_j incl_j(y_j)` (that is,
`y_1 ⊗ ⋯ ⊗ y_n`) lies in the maximal order `(R_I)^∼` as soon as `∑_j ord_p(y_j) ≥ 0`
(`prod_incl_mem_integral`), and preserves `(R_I)^∼` when `∑_j ord_p(y_j) = 0`
(`prod_incl_smul_integral_eq`). This is the integrality input of the estimates of
IUT IV, Proposition 1.4 for the corrected indeterminacy automorphisms.

The proof is the power trick: with `N = ∏_j e_{w_j}`, each `y_j^N = p^{n_j}·u_j` with `n_j ∈ ℤ`,
`n_j = N·ord_p(y_j)` and `ord_p(u_j) = 0` (`ord_p` takes values in `e_{w_j}^{-1}ℤ`), so
`z^N = p^M·∏_j incl_j(u_j)` with `M = ∑_j n_j = N·∑_j ord_p(y_j)` (`prod_incl_pow_eq`). The
second factor lies in `R_I`; for `M ≥ 0`, `z^N` is integral over `ℤ_p`, hence so is `z`.
-/

namespace Iut

namespace LocalConstruct

open NumberField IsDedekindDomain WithZero
open scoped Pointwise

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### `ord_p` on integer powers -/

/-- `ord_p(x^n) = n·ord_p(x)` for integer exponents. -/
lemma ordp_zpow (w : FinitePlace K) (x : completionAt K w) (n : ℤ) :
    ordp K w (x ^ n) = n * ordp K w x := by
  unfold ordp
  rw [norm_zpow, Real.log_zpow]
  ring

/-- `ord_p(x⁻¹) = −ord_p(x)`. -/
lemma ordp_inv (w : FinitePlace K) (x : completionAt K w) :
    ordp K w x⁻¹ = -ordp K w x := by
  unfold ordp
  rw [norm_inv, Real.log_inv]
  ring

/-- The image of `p` in `K_w` is `≠ 0`. -/
lemma natCast_prime_ne_zero_completion (w : FinitePlace K) (p : ℕ) [Fact p.Prime] :
    (p : completionAt K w) ≠ 0 := by
  rw [← map_natCast (algebraMap K (completionAt K w))]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

/-- `ord_p(p) = 1` in a completion of residue characteristic `p`. -/
lemma ordp_natCast_prime {w : FinitePlace K} {p : ℕ} (hw : residueChar w = p) :
    ordp K w (p : completionAt K w) = 1 := by
  rw [← hw, ← map_natCast (algebraMap K (completionAt K w))]
  exact ordp_p w

/-- **`ord_p` takes values in `e^{-1}ℤ`, power form**: for `y ≠ 0` and `e_w ∣ N`,
`y^N = p^n·u` with `n = N·ord_p(y) ∈ ℤ` and `ord_p(u) = 0`. -/
lemma exists_pow_eq_zpow_mul {w : FinitePlace K} {p : ℕ} [Fact p.Prime]
    (hw : residueChar w = p) {y : completionAt K w} (hy : y ≠ 0) {N : ℕ}
    (hN : ramIdx K w ∣ N) :
    ∃ n : ℤ, (n : ℝ) = N * ordp K w y ∧ ∃ u : completionAt K w, u ≠ 0 ∧ ordp K w u = 0 ∧
      y ^ N = (p : completionAt K w) ^ n * u := by
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  set m : ℤ := log (Valued.v y)
  have hm : Valued.v y = exp m := (exp_log hv).symm
  obtain ⟨k, hk⟩ := hN
  subst hk
  have he : (ramIdx K w : ℝ) ≠ 0 := by exact_mod_cast (ramIdx_pos' w).ne'
  have hp0 := natCast_prime_ne_zero_completion w p
  have hpn : ∀ n : ℤ, (p : completionAt K w) ^ n ≠ 0 := fun n => zpow_ne_zero n hp0
  refine ⟨-m * k, ?_, y ^ (ramIdx K w * k) / (p : completionAt K w) ^ (-m * k), ?_, ?_, ?_⟩
  · rw [ordp_eq_of_valued w y m hm]
    push_cast
    field_simp
  · exact div_ne_zero (pow_ne_zero _ hy) (hpn _)
  · have h1 := ordp_mul w (y ^ (ramIdx K w * k) / (p : completionAt K w) ^ (-m * k))
      ((p : completionAt K w) ^ (-m * k)) (div_ne_zero (pow_ne_zero _ hy) (hpn _)) (hpn _)
    rw [div_mul_cancel₀ _ (hpn _), ordp_pow', ordp_zpow, ordp_natCast_prime hw,
      ordp_eq_of_valued w y m hm] at h1
    push_cast at h1
    field_simp at h1
    linarith
  · rw [mul_div_cancel₀ _ (hpn _)]

/-! ### Elementary scalings of a packet -/

variable {ι : Type} [Fintype ι] (p : Nat.Primes) (c : ι → Place K)

/-- `p` is a unit of the packet. -/
lemma isUnit_natCast_prime_tensor : IsUnit ((p : ℕ) : Tensor K (.finite p) c) := by
  rw [← map_natCast (algebraMap ℚ_[p] (Tensor K (.finite p) c))]
  exact (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr p.2.ne_zero)).map _

/-- `p`, as a unit of the packet. -/
noncomputable def primeUnit : (Tensor K (.finite p) c)ˣ :=
  (isUnit_natCast_prime_tensor p c).unit

@[simp] lemma val_primeUnit : (primeUnit p c : Tensor K (.finite p) c) = ((p : ℕ) : _) := rfl

variable {p c}

/-- The inclusion of an integer power of `p` is the corresponding power of `p` in the packet. -/
lemma incl_natCast_prime_zpow (j : ι) (w : FinitePlace K) (h : c j = Place.finite w) (n : ℤ) :
    incl p c j w h (((p : ℕ) : completionAt K w) ^ n) =
      ((primeUnit p c ^ n : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) := by
  set U : (completionAt K w)ˣ := Units.mk0 _ (natCast_prime_ne_zero_completion w (p : ℕ))
  have hU : Units.map (incl p c j w h).toMonoidHom U = primeUnit p c := by
    ext
    rw [Units.coe_map, Units.val_mk0, val_primeUnit]
    exact map_natCast (incl p c j w h) _
  have : ((p : ℕ) : completionAt K w) ^ n = ((U ^ n : (completionAt K w)ˣ) : _) := by
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [this, ← hU, ← map_zpow]
  rfl

/-- **The power trick for elementary scalings**: with `N = ∏_j e_{w_j}`,
`(∏_j incl_j(y_j))^N = p^M·∏_j incl_j(u_j)` with `M = N·∑_j ord_p(y_j) ∈ ℤ` and
`ord_p(u_j) = 0`. -/
theorem prod_incl_pow_eq (hc : ∀ j, IsOver K p (c j)) (w : ι → FinitePlace K)
    (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ M : ℤ, (M : ℝ) = N * ∑ j, ordp K (w j) (y j) ∧
      ∃ u : ∀ j, completionAt K (w j), (∀ j, u j ≠ 0) ∧ (∀ j, ordp K (w j) (u j) = 0) ∧
        (∏ j, incl p c j (w j) (h j) (y j)) ^ N =
          ((primeUnit p c ^ M : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) *
            ∏ j, incl p c j (w j) (h j) (u j) := by
  classical
  have hw : ∀ j, residueChar (w j) = (p : ℕ) := fun j =>
    (isOver_finite_iff p (w j)).mp (h j ▸ hc j)
  set N := ∏ j, ramIdx K (w j)
  have hN : 0 < N := Finset.prod_pos fun j _ => ramIdx_pos' (w j)
  have hdvd : ∀ j, ramIdx K (w j) ∣ N := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  choose n hn u hu0 hu hyu using fun j => exists_pow_eq_zpow_mul (hw j) (hy j) (hdvd j)
  refine ⟨N, hN, ∑ j, n j, ?_, u, hu0, hu, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hn j
  · rw [← Finset.prod_pow]
    have hj : ∀ j, (incl p c j (w j) (h j) (y j)) ^ N =
        ((primeUnit p c ^ n j : (Tensor K (.finite p) c)ˣ) : Tensor K (.finite p) c) *
          incl p c j (w j) (h j) (u j) := fun j => by
      rw [← map_pow, hyu j, map_mul, incl_natCast_prime_zpow]
    rw [Finset.prod_congr rfl fun j _ => hj j, Finset.prod_mul_distrib, ← Units.coe_prod]
    congr 2
    induction (Finset.univ : Finset ι) using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

/-- **Integrality of elementary scalings** (IUT IV, Proposition 1.4): if `∑_j ord_p(y_j) ≥ 0`,
then `∏_j incl_j(y_j) ∈ (R_I)^∼`. -/
theorem prod_incl_mem_integral (hc : ∀ j, IsOver K p (c j)) (w : ι → FinitePlace K)
    (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0)
    (hsum : 0 ≤ ∑ j, ordp K (w j) (y j)) :
    (∏ j, incl p c j (w j) (h j) (y j)) ∈ integral p c := by
  obtain ⟨N, hN, M, hM, u, -, hu, hpow⟩ := prod_incl_pow_eq hc w h y hy
  have hM0 : 0 ≤ M := by
    have : (0 : ℝ) ≤ M := by rw [hM]; exact mul_nonneg (Nat.cast_nonneg _) hsum
    exact_mod_cast this
  rw [mem_integral]
  refine IsIntegral.of_pow hN ?_
  rw [hpow, ← Int.toNat_of_nonneg hM0, zpow_natCast, Units.val_pow_eq_pow_val, val_primeUnit]
  refine IsIntegral.mul (IsIntegral.pow ?_ _) (IsIntegral.prod _ fun j _ => ?_)
  · rw [← map_natCast (algebraMap ℤ_[p] (Tensor K (.finite p) c))]
    exact isIntegral_algebraMap
  · exact (mem_integral p c).mp (incl_mem_integral p c j (w j) (h j) (u j)
      (norm_le_one_of_ordp_nonneg (hu j).ge))

/-- The inverse of an elementary scaling is the elementary scaling of the inverses. -/
lemma prod_incl_mul_prod_incl_inv (w : ι → FinitePlace K)
    (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0) :
    (∏ j, incl p c j (w j) (h j) (y j)) * ∏ j, incl p c j (w j) (h j) (y j)⁻¹ = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← map_mul, mul_inv_cancel₀ (hy j), map_one]

/-- Elementary scalings by nonzero elements are units of the packet. -/
lemma isUnit_prod_incl (w : ι → FinitePlace K)
    (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0) :
    IsUnit (∏ j, incl p c j (w j) (h j) (y j)) :=
  ⟨⟨_, _, prod_incl_mul_prod_incl_inv w h y hy,
    by rw [mul_comm]; exact prod_incl_mul_prod_incl_inv w h y hy⟩, rfl⟩

/-- **Elementary scalings with `∑_j ord_p(y_j) = 0` preserve `(R_I)^∼`**
(IUT IV, Proposition 1.4): `(∏_j incl_j(y_j))·(R_I)^∼ = (R_I)^∼`. -/
theorem prod_incl_smul_integral_eq (hc : ∀ j, IsOver K p (c j)) (w : ι → FinitePlace K)
    (h : ∀ j, c j = Place.finite (w j)) (y : ∀ j, completionAt K (w j)) (hy : ∀ j, y j ≠ 0)
    (hsum : ∑ j, ordp K (w j) (y j) = 0) :
    (∏ j, incl p c j (w j) (h j) (y j)) • integral p c = integral p c := by
  have hz := prod_incl_mem_integral hc w h y hy hsum.ge
  have hz' := prod_incl_mem_integral hc w h (fun j => (y j)⁻¹) (fun j => inv_ne_zero (hy j))
    (by simp only [ordp_inv, Finset.sum_neg_distrib, hsum, neg_zero, le_refl])
  have hinv := prod_incl_mul_prod_incl_inv (p := p) (c := c) w h y hy
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mul_mem_integral p c hz hx
  · intro x hx
    refine ⟨(∏ j, incl p c j (w j) (h j) (y j)⁻¹) * x, mul_mem_integral p c hz' hx, ?_⟩
    change _ • _ = x
    rw [smul_eq_mul, ← mul_assoc, hinv, one_mul]

end LocalConstruct

end Iut
