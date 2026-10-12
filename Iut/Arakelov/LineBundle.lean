/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Concrete.LocalConstruct.Integral

/-!
# Arithmetic line bundles on number fields and the Arakelov degree (roadmap P14)

The arithmetic line bundles of IUT III, Example 3.6(ii) and Proposition 3.9(iii) (the objects of
the global realified Frobenioids `F^⊛_mod`) in their **idelic description**: an arithmetic line
bundle `L` on a number field `K`, trivialized by a chosen generic section `s`, is recorded by the
local norms of `s`,

* at each finite place `w` an element `a_w ∈ K_w^×` (`‖s‖_w = ‖a_w‖_w`), with `‖a_w‖_w = 1` for
  almost all `w` (`ArithLineBundle.fin`);
* at each archimedean place `v` a positive real `r_v` (`‖s‖_v = r_v`; `ArithLineBundle.inf`).

Equivalently, `L` is the `𝓞_K`-lattice `{x ∈ K : ‖x‖_w ≤ ‖a_w‖_w⁻¹ for all w}` (the sections
`x·s` of norm `≤ 1` at all finite places) with the hermitian metrics `r_v`; the **arithmetic
divisor** of `s` is `Σ_w ord_w(a_w)·[w] + Σ_v (−log r_v)·[v]`.
The norms are Mathlib's: `‖·‖_w` on `adicCompletion` is normalized by
`‖π_w‖ = (#𝓞_K/𝔭_w)⁻¹`, and at an archimedean place the normalized absolute value is
`|·|_v^{mult v}` — these are exactly the normalizations of the product formula
`NumberField.prod_abs_eq_one`.

## The degree

`deg L = −Σ_w log‖a_w‖_w − Σ_v mult(v)·log r_v` (`ArithLineBundle.deg`), the sum of the local
contributions `finDeg`, `infDeg`; normalized by `[K : ℚ]` (`degNorm`). In the notation of IUT III
the local contribution `−log‖a_w‖_w = ord_w(a_w)·log #(𝓞_K/𝔭_w)` is (up to the sign and the
packet normalization) the local log-volume of the region `a_w·𝒪_w` relative to `𝒪_w`
(`finDeg_eq_ordp`, and `Iut/Arakelov/Container.lean` for the comparison with the log-volumes of
the concrete container).

## Contents

* `ArithLineBundle K`, `deg`, `degNorm`, the group operations `one`, `mul`, `pow`;
* `deg_mul`, `deg_one`, `deg_pow` (the degree is a homomorphism);
* `principal x`: the bundle `𝒪_K` with section `x ∈ K^×`, and the **product formula**
  `deg_principal : deg (principal x) = 0` (from `NumberField.prod_abs_eq_one`);
* **independence of the chosen section**: `deg_mul_principal`, `degNorm_mul_principal`;
* the comparison with ideal norms: `finDeg_principal_sum` (the finite part of the degree of
  the divisor of `x` is `log N((x))`, `FractionalIdeal.absNorm_span_singleton`) and
  `infDeg_principal_sum` (the archimedean part is `−log|N(x)|`);
* `finDeg_eq_ordp`, `degNorm_eq`: the normalized degree as a weighted sum of `ord_p`'s with the
  weights `[K_w : ℚ_p]/[K : ℚ]` of IUT III, Remark 3.1.1 (`placeWeight`, `infPlaceWeight`).
* `deg_congr`: the degree depends only on the local norms and metrics.

The fractional ideal `∏_w 𝔭_w^{ord_w(a_w)}` of an arbitrary bundle, its norm, and the arithmetic
Picard group with its map to the class group are in `Iut/Arakelov/FractionalIdeal.lean`.
-/

namespace Iut

namespace Arakelov

open NumberField
open scoped nonZeroDivisors

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **An arithmetic line bundle on `K` in idelic form** (with a chosen generic section `s`): the
local norms `‖s‖_w = ‖a_w‖_w` at the finite places (`a_w ∈ K_w^×`, of norm `1` for almost all
`w`) and `‖s‖_v = r_v > 0` at the archimedean places. -/
structure ArithLineBundle where
  /-- The finite components `a_w ∈ K_w^×`. -/
  fin : ∀ w : FinitePlace K, completionAt K w
  fin_ne_zero : ∀ w, fin w ≠ 0
  /-- Almost all finite components are units. -/
  finite_fin : {w | ‖fin w‖ ≠ 1}.Finite
  /-- The archimedean components `r_v > 0`. -/
  inf : InfinitePlace K → ℝ
  inf_pos : ∀ v, 0 < inf v

namespace ArithLineBundle

variable {K}

/-- The local degree at a finite place: `−log‖a_w‖_w = ord_w(a_w)·log #(𝓞_K/𝔭_w)`. -/
noncomputable def finDeg (L : ArithLineBundle K) (w : FinitePlace K) : ℝ := -Real.log ‖L.fin w‖

/-- The local degree at an archimedean place: `−mult(v)·log r_v`. -/
noncomputable def infDeg (L : ArithLineBundle K) (v : InfinitePlace K) : ℝ :=
  -((v.mult : ℝ) * Real.log (L.inf v))

lemma support_finDeg_subset (L : ArithLineBundle K) :
    Function.support L.finDeg ⊆ {w | ‖L.fin w‖ ≠ 1} := by
  intro w hw
  simp only [Set.mem_setOf_eq]
  intro h
  exact hw (by simp [finDeg, h])

lemma finite_support_finDeg (L : ArithLineBundle K) : (Function.support L.finDeg).Finite :=
  L.finite_fin.subset L.support_finDeg_subset

/-- **The Arakelov degree** `deg L = −Σ_w log‖a_w‖_w − Σ_v mult(v)·log r_v`. -/
noncomputable def deg (L : ArithLineBundle K) : ℝ := (∑ᶠ w, L.finDeg w) + ∑ v, L.infDeg v

/-- **The normalized Arakelov degree** `deg L/[K : ℚ]` (IUT III, Remark 3.1.1, Proposition
3.9(iii): the normalization making the degree invariant under base change). -/
noncomputable def degNorm (L : ArithLineBundle K) : ℝ := L.deg / Module.finrank ℚ K

/-- The degree depends only on the local norms `‖a_w‖_w` and the metrics `r_v`. -/
lemma deg_congr (L M : ArithLineBundle K) (hfin : ∀ w, ‖L.fin w‖ = ‖M.fin w‖)
    (hinf : ∀ v, L.inf v = M.inf v) : L.deg = M.deg := by
  simp only [deg, finDeg, infDeg, hfin, hinf]

/-! ### The group structure -/

/-- The trivial bundle `𝒪_K` with the section `1`. -/
noncomputable def one : ArithLineBundle K where
  fin _ := 1
  fin_ne_zero _ := one_ne_zero
  finite_fin := by simp
  inf _ := 1
  inf_pos _ := one_pos

/-- The tensor product of arithmetic line bundles (product of the sections). -/
noncomputable def mul (L M : ArithLineBundle K) : ArithLineBundle K where
  fin w := L.fin w * M.fin w
  fin_ne_zero w := mul_ne_zero (L.fin_ne_zero w) (M.fin_ne_zero w)
  finite_fin := by
    refine (L.finite_fin.union M.finite_fin).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at h
    exact hw (by simp [norm_mul, h.1, h.2])
  inf v := L.inf v * M.inf v
  inf_pos v := mul_pos (L.inf_pos v) (M.inf_pos v)

/-- The `m`-th tensor power. -/
noncomputable def pow (L : ArithLineBundle K) (m : ℕ) : ArithLineBundle K where
  fin w := L.fin w ^ m
  fin_ne_zero w := pow_ne_zero _ (L.fin_ne_zero w)
  finite_fin := by
    refine L.finite_fin.subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_setOf_eq, not_not] at h
    exact hw (by simp [norm_pow, h])
  inf v := L.inf v ^ m
  inf_pos v := pow_pos (L.inf_pos v) m

lemma finDeg_mul (L M : ArithLineBundle K) (w : FinitePlace K) :
    (L.mul M).finDeg w = L.finDeg w + M.finDeg w := by
  simp only [finDeg, mul, norm_mul]
  rw [Real.log_mul (norm_ne_zero_iff.mpr (L.fin_ne_zero w))
    (norm_ne_zero_iff.mpr (M.fin_ne_zero w))]
  ring

lemma infDeg_mul (L M : ArithLineBundle K) (v : InfinitePlace K) :
    (L.mul M).infDeg v = L.infDeg v + M.infDeg v := by
  simp only [infDeg, mul]
  rw [Real.log_mul (L.inf_pos v).ne' (M.inf_pos v).ne']
  ring

/-- **The degree is additive** under tensor products. -/
theorem deg_mul (L M : ArithLineBundle K) : (L.mul M).deg = L.deg + M.deg := by
  unfold deg
  simp only [finDeg_mul, infDeg_mul]
  rw [finsum_add_distrib L.finite_support_finDeg M.finite_support_finDeg,
    Finset.sum_add_distrib]
  ring

theorem deg_one : (one : ArithLineBundle K).deg = 0 := by
  simp [deg, finDeg, infDeg, one]

lemma finDeg_pow (L : ArithLineBundle K) (m : ℕ) (w : FinitePlace K) :
    (L.pow m).finDeg w = m * L.finDeg w := by
  simp only [finDeg, pow, norm_pow, Real.log_pow]
  ring

lemma infDeg_pow (L : ArithLineBundle K) (m : ℕ) (v : InfinitePlace K) :
    (L.pow m).infDeg v = m * L.infDeg v := by
  simp only [infDeg, pow, Real.log_pow]
  ring

theorem deg_pow (L : ArithLineBundle K) (m : ℕ) : (L.pow m).deg = m * L.deg := by
  unfold deg
  simp only [finDeg_pow, infDeg_pow]
  rw [← mul_finsum, ← Finset.mul_sum, mul_add]

theorem degNorm_mul (L M : ArithLineBundle K) : (L.mul M).degNorm = L.degNorm + M.degNorm := by
  simp only [degNorm, deg_mul, add_div]

theorem degNorm_pow (L : ArithLineBundle K) (m : ℕ) : (L.pow m).degNorm = m * L.degNorm := by
  simp only [degNorm, deg_pow, mul_div_assoc]

/-! ### Principal bundles and the product formula -/

/-- **The principal bundle of `x ∈ K^×`**: `𝒪_K` with the section `x`, i.e. the idele
`(x)_w, (|x|_v)_v` (its divisor is the principal divisor of `x`). -/
noncomputable def principal (x : K) (hx : x ≠ 0) : ArithLineBundle K where
  fin w := FinitePlace.embedding w.maximalIdeal x
  fin_ne_zero w := (map_ne_zero _).mpr hx
  finite_fin := by
    refine (FinitePlace.hasFiniteMulSupport hx).subset fun w hw => ?_
    simpa [FinitePlace.norm_embedding_eq] using hw
  inf v := v x
  inf_pos _ := InfinitePlace.pos_iff.mpr hx

lemma finDeg_principal (x : K) (hx : x ≠ 0) (w : FinitePlace K) :
    (principal x hx).finDeg w = -Real.log (w x) := by
  simp [finDeg, principal, FinitePlace.norm_embedding_eq]

/-- `∑ᶠ log f = log ∏ᶠ f` for a positive function of finite multiplicative support. -/
lemma finsum_log_eq_log_finprod {α : Type*} {f : α → ℝ} (hf : f.HasFiniteMulSupport)
    (hpos : ∀ a, 0 < f a) : ∑ᶠ a, Real.log (f a) = Real.log (∏ᶠ a, f a) := by
  have hsub : Function.support (fun a => Real.log (f a)) ⊆ ↑hf.toFinset := by
    intro a ha
    rw [Set.Finite.coe_toFinset, Function.mem_mulSupport]
    intro h
    exact ha (by simp [h])
  rw [finsum_eq_sum_of_support_subset _ hsub,
    finprod_eq_prod_of_mulSupport_subset _ hf.coe_toFinset.superset,
    Real.log_prod fun a _ => (hpos a).ne']

/-- The finite part of the degree of the principal bundle: `−log ∏_w |x|_w = log|N(x)|`. -/
theorem finsum_finDeg_principal (x : K) (hx : x ≠ 0) :
    ∑ᶠ w, (principal x hx).finDeg w = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  simp only [finDeg_principal]
  rw [finsum_neg_distrib, finsum_log_eq_log_finprod (FinitePlace.hasFiniteMulSupport hx)
    (fun w => FinitePlace.pos_iff.mpr hx), FinitePlace.prod_eq_inv_abs_norm hx]
  push_cast
  rw [Real.log_inv, neg_neg]

/-- **The finite part of the degree of the divisor of `x` is the log of the norm of the
fractional ideal `(x)`**: `Σ_w ord_w(x)·log #(𝓞_K/𝔭_w) = log N((x))`. -/
theorem finsum_finDeg_principal_eq_absNorm (x : K) (hx : x ≠ 0) :
    ∑ᶠ w, (principal x hx).finDeg w =
      Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) : ℚ) : ℝ) := by
  rw [finsum_finDeg_principal, FractionalIdeal.absNorm_span_singleton]
  push_cast
  rfl

/-- The archimedean part of the degree of the principal bundle: `−Σ_v mult(v)·log|x|_v =
−log|N(x)|`. -/
theorem sum_infDeg_principal (x : K) (hx : x ≠ 0) :
    ∑ v, (principal x hx).infDeg v = -Real.log |(Algebra.norm ℚ x : ℝ)| := by
  simp only [infDeg, principal, Finset.sum_neg_distrib]
  congr 1
  rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm, Real.log_prod fun v _ =>
    (pow_pos (InfinitePlace.pos_iff.mpr hx) _).ne']
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow]

/-- **The product formula**: principal bundles have degree `0` (`NumberField.prod_abs_eq_one`). -/
theorem deg_principal (x : K) (hx : x ≠ 0) : (principal x hx).deg = 0 := by
  rw [deg, finsum_finDeg_principal, sum_infDeg_principal, add_neg_cancel]

/-- **The degree does not depend on the chosen section**: changing the section `s` to `x·s`
(`x ∈ K^×`) multiplies the idelic description by the principal bundle of `x`. -/
theorem deg_mul_principal (L : ArithLineBundle K) (x : K) (hx : x ≠ 0) :
    (L.mul (principal x hx)).deg = L.deg := by
  rw [deg_mul, deg_principal, add_zero]

theorem degNorm_mul_principal (L : ArithLineBundle K) (x : K) (hx : x ≠ 0) :
    (L.mul (principal x hx)).degNorm = L.degNorm := by
  rw [degNorm, deg_mul_principal, degNorm]

/-! ### The degree as a weighted sum of `ord_p` -/

lemma localDeg_mul_log_ne_zero (w : FinitePlace K) :
    (localDeg K w : ℝ) * Real.log (residueChar w) ≠ 0 := by
  refine mul_ne_zero (by exact_mod_cast (LocalConstruct.localDeg_pos w).ne') ?_
  have h := (residueChar_prime w).one_lt
  exact (Real.log_pos (by exact_mod_cast h)).ne'

/-- `−log‖a_w‖_w = [K_w : ℚ_p]·ord_p(a_w)·log p`. -/
theorem finDeg_eq_ordp (L : ArithLineBundle K) (w : FinitePlace K) :
    L.finDeg w = localDeg K w * ordp K w (L.fin w) * Real.log (residueChar w) := by
  unfold finDeg ordp
  have h := localDeg_mul_log_ne_zero w
  rw [show (localDeg K w : ℝ) * (-Real.log ‖L.fin w‖ /
      (localDeg K w * Real.log (residueChar w))) * Real.log (residueChar w) =
      -Real.log ‖L.fin w‖ * ((localDeg K w * Real.log (residueChar w)) /
        (localDeg K w * Real.log (residueChar w))) by ring, div_self h, mul_one]

/-- The normalized local degree: `−log‖a_w‖_w/[K : ℚ] = ([K_w : ℚ_p]/[K : ℚ])·ord_p(a_w)·log p`. -/
theorem finDeg_div_finrank (L : ArithLineBundle K) (w : FinitePlace K) :
    L.finDeg w / Module.finrank ℚ K =
      placeWeight K w * (ordp K w (L.fin w) * Real.log (residueChar w)) := by
  rw [finDeg_eq_ordp, placeWeight]
  ring

/-- **The normalized degree as a sum of normalized local contributions** (IUT III, Remark 3.1.1
weights): `deg L/[K : ℚ] = Σ_w ([K_w : ℚ_p]/[K : ℚ])·ord_p(a_w)·log p
− Σ_v ([K_v : ℝ]/[K : ℚ])·log r_v`. -/
theorem degNorm_eq (L : ArithLineBundle K) :
    L.degNorm = (∑ᶠ w, placeWeight K w * (ordp K w (L.fin w) * Real.log (residueChar w))) +
      ∑ v, -(infPlaceWeight K v * Real.log (L.inf v)) := by
  rw [degNorm, deg, add_div]
  congr 1
  · rw [div_eq_mul_inv, finsum_mul]
    refine finsum_congr fun w => ?_
    rw [← finDeg_div_finrank, div_eq_mul_inv]
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [infDeg, infPlaceWeight]
    ring

end ArithLineBundle

end Arakelov

end Iut
