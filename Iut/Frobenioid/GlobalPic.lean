/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Global

/-!
# `δ_A : Pic_Φ(A) ≅ ℝ` for the global realified Frobenioid ([FrdI], Theorem 6.4(i))

[FrdI], Theorem 6.4(i): for the realified global Frobenioid of a number field `K`, the degree
`δ_A : Pic_Φ(A) = Φ^gp(A)/Φ^birat(A) → ℝ` is an isomorphism. Surjectivity is
`picDeg_surjective` (`Global.lean`); here we prove injectivity, i.e. **every ℝ-arithmetic divisor
of degree `0` is an ℝ-linear combination of principal divisors**:

* the finite part: for every finite place `w` some power `𝔭_w^n` (`n > 0`, the order of the class
  of `𝔭_w` in the **finite class group** `ClassGroup (𝓞 K)`, Mathlib's `instFintypeClassGroup`)
  is principal, `= (π)`, so `[w] = (1/n)·div(π)` up to an archimedean divisor
  (`exists_ratFun_fst_single`, `exists_ratFun_fst`);
* the archimedean part: an archimedean divisor `(0, y)` of degree `0` is an ℝ-combination of the
  divisors of units, by **Dirichlet's unit theorem** in the form that the logarithmic embedding of
  the units spans the trace-zero hyperplane `{w ≠ w₀} → ℝ` (Mathlib's `unitLattice_span_eq_top`)
  (`inf_mem_ratFun`).

Results: `ker_degArith_le` (`ker deg^arith = ℝ·div(K^×)`), **`picDeg_injective`**,
**`picDegEquiv : Pic_Φ ≃ₗ[ℝ] ℝ`**, and for objects of `C^⊩`:
**`GlobalRealified.nonempty_iso_iff_degree_eq`** — two objects are isomorphic iff they have the
same degree.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField Arakelov IsDedekindDomain ArithLineBundle'
open scoped nonZeroDivisors

universe u

variable {K : Type u} [Field K] [NumberField K]

/-! ### Orders of principal bundles -/

/-- `ord_w(x) = ord_{𝔭_w}((x))`. -/
lemma ord_principal (x : K) (hx : x ≠ 0) (w : FinitePlace K) :
    (ArithLineBundle.principal x hx).ord w =
      FractionalIdeal.count K w.maximalIdeal (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  rw [← ArithLineBundle.fracIdeal_principal, ArithLineBundle.count_fracIdeal,
    FinitePlace.mk_maximalIdeal]

/-- **Finiteness of the class group**: some positive power of `𝔭_w` is principal. -/
lemma exists_principal_pow (w : FinitePlace K) :
    ∃ (x : K) (_ : x ≠ 0) (n : ℕ), 0 < n ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x =
        (w.maximalIdeal.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ n := by
  have hP : (w.maximalIdeal.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr w.maximalIdeal.ne_bot
  let I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 _ hP
  let n := orderOf (ClassGroup.mk K I)
  have hn : 0 < n := orderOf_pos _
  have h1 : ClassGroup.mk K (I ^ n) = 1 := by rw [map_pow, pow_orderOf_eq_one]
  obtain ⟨x, hx⟩ := (ClassGroup.mk_eq_one_iff.mp h1).principal
  have hI : ((I ^ n : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
    apply FractionalIdeal.coeToSubmodule_injective
    simpa [FractionalIdeal.coe_spanSingleton] using hx
  refine ⟨x, ?_, n, hn, ?_⟩
  · rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hI
    exact (I ^ n).ne_zero hI
  · rw [← hI, Units.val_pow_eq_pow_val]
    rfl

/-- The finite part of a principal divisor generating `𝔭_w^n`. -/
lemma exists_divOf_fst (w : FinitePlace K) :
    ∃ (x : {x : K // x ≠ 0}) (n : ℕ), 0 < n ∧ (divOf K x).1 = Finsupp.single w (n : ℝ) := by
  obtain ⟨x, hx, n, hn, he⟩ := exists_principal_pow w
  refine ⟨⟨x, hx⟩, n, hn, Finsupp.ext fun w' => ?_⟩
  rw [divOf, toDiv_fst_apply, ord_principal, he, FractionalIdeal.count_pow]
  by_cases h : w' = w
  · subst h
    rw [FractionalIdeal.count_self]
    simp
  · have h' : w.maximalIdeal ≠ w'.maximalIdeal := fun e => h (by
      rw [← FinitePlace.mk_maximalIdeal w', ← e, FinitePlace.mk_maximalIdeal])
    rw [FractionalIdeal.count_maximal_coprime K _ h', Finsupp.single_eq_of_ne h]
    simp

lemma divOf_mem (x : {x : K // x ≠ 0}) : divOf K x ∈ ratFun K :=
  Submodule.subset_span ⟨x, rfl⟩

/-- `[w] + (archimedean)` is a realified rational function. -/
lemma exists_ratFun_fst_single (w : FinitePlace K) (t : ℝ) :
    ∃ a ∈ ratFun K, a.1 = Finsupp.single w t := by
  obtain ⟨x, n, hn, h⟩ := exists_divOf_fst w
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨(t / n) • divOf K x, (ratFun K).smul_mem _ (divOf_mem x), ?_⟩
  rw [Prod.smul_fst, h, Finsupp.smul_single, smul_eq_mul, div_mul_cancel₀ _ hn']

/-- **Every finite ℝ-divisor is the finite part of a realified rational function.** -/
lemma exists_ratFun_fst (f : FinitePlace K →₀ ℝ) : ∃ a ∈ ratFun K, a.1 = f := by
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, (ratFun K).zero_mem, rfl⟩
  | add f g hf hg =>
    obtain ⟨a, ha, rfl⟩ := hf
    obtain ⟨b, hb, rfl⟩ := hg
    exact ⟨a + b, (ratFun K).add_mem ha hb, rfl⟩
  | single w t => exact exists_ratFun_fst_single w t

/-! ### Units and Dirichlet's unit theorem -/

/-- The divisor of a unit is archimedean. -/
lemma divOf_unit_fst (u : (𝓞 K)ˣ) :
    (divOf K ⟨(u : K), by simp⟩).1 = 0 := by
  ext w
  rw [divOf, toDiv_fst_apply, ord_principal]
  have : FractionalIdeal.spanSingleton (𝓞 K)⁰ (u : K) = 1 := by
    rw [show (u : K) = algebraMap (𝓞 K) K (u : 𝓞 K) from rfl,
      ← FractionalIdeal.coeIdeal_span_singleton, Ideal.span_singleton_eq_top.mpr u.isUnit,
      FractionalIdeal.coeIdeal_top]
  rw [this, FractionalIdeal.count_one]
  simp

lemma divOf_unit_snd (u : (𝓞 K)ˣ) (v : InfinitePlace K) :
    (divOf K ⟨(u : K), by simp⟩).2 v = -Real.log (v (u : K)) := rfl

/-- The weighted archimedean coordinates `y ↦ (mult(w)·y_w)_{w ≠ w₀}`. -/
noncomputable def logCoord : ArithDiv K →ₗ[ℝ] Units.dirichletUnitTheorem.logSpace K where
  toFun y w := (w.1.mult : ℝ) * y.2 w.1
  map_add' _ _ := by ext; simp [mul_add]
  map_smul' _ _ := by ext; simp; ring

lemma logCoord_divOf_inv (u : (𝓞 K)ˣ) :
    logCoord (divOf K ⟨((u⁻¹ : (𝓞 K)ˣ) : K), by simp⟩) =
      Units.logEmbedding K (Additive.ofMul u) := by
  ext w
  change (w.1.mult : ℝ) * (divOf K _).2 w.1 = _
  rw [divOf_unit_snd, Units.dirichletUnitTheorem.logEmbedding_component]
  have h : ((u⁻¹ : (𝓞 K)ˣ) : K) = (u : K)⁻¹ := by simp
  rw [h, map_inv₀, Real.log_inv, neg_neg]

/-- **Dirichlet**: an archimedean divisor of degree `0` is a realified rational function. -/
theorem inf_mem_ratFun (y : InfinitePlace K → ℝ) (hy : degArith K (0, y) = 0) :
    ((0, y) : ArithDiv K) ∈ ratFun K := by
  classical
  -- the span `T` of the divisors of units
  let T : Submodule ℝ (ArithDiv K) :=
    Submodule.span ℝ (Set.range fun u : (𝓞 K)ˣ => divOf K ⟨(u : K), by simp⟩)
  have hT : T ≤ ratFun K := Submodule.span_le.mpr (by rintro _ ⟨u, rfl⟩; exact divOf_mem _)
  have hT1 : ∀ t ∈ T, t.1 = 0 := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t h => obtain ⟨u, rfl⟩ := h; exact divOf_unit_fst u
    | zero => rfl
    | add a b _ _ ha hb => simp [ha, hb]
    | smul c a _ ha => simp [ha]
  have htop : T.map logCoord = ⊤ := by
    rw [Submodule.map_span, eq_top_iff, ← Units.dirichletUnitTheorem.unitLattice_span_eq_top K]
    refine Submodule.span_mono ?_
    rintro _ ⟨u, -, rfl⟩
    refine ⟨_, ⟨u.toMul⁻¹, rfl⟩, ?_⟩
    simpa using logCoord_divOf_inv (Additive.toMul u)
  obtain ⟨t, ht, hte⟩ : logCoord ((0, y) : ArithDiv K) ∈ T.map logCoord := htop ▸ Submodule.mem_top
  suffices h : t = (0, y) from h ▸ hT ht
  have hdeg : degArith K t = 0 := degArith_ratFun (hT ht)
  have hcoord : ∀ w, w ≠ Units.dirichletUnitTheorem.w₀ → t.2 w = y w := by
    intro w hw
    have := congrFun hte ⟨w, hw⟩
    change (w.mult : ℝ) * t.2 w = (w.mult : ℝ) * y w at this
    exact mul_left_cancel₀ (by exact_mod_cast w.mult_pos.ne') this
  refine Prod.ext (hT1 t ht) (funext fun w => ?_)
  by_cases hw : w = Units.dirichletUnitTheorem.w₀
  · subst hw
    rw [degArith_apply, hT1 t ht, Finsupp.sum_zero_index, zero_add,
      Fintype.sum_eq_add_sum_subtype_ne _ Units.dirichletUnitTheorem.w₀] at hdeg
    rw [degArith_apply, Finsupp.sum_zero_index, zero_add,
      Fintype.sum_eq_add_sum_subtype_ne _ Units.dirichletUnitTheorem.w₀] at hy
    have he : ∑ v : {v // v ≠ Units.dirichletUnitTheorem.w₀}, (v.1.mult : ℝ) * t.2 v.1 =
        ∑ v : {v // v ≠ Units.dirichletUnitTheorem.w₀}, (v.1.mult : ℝ) * y v.1 :=
      Finset.sum_congr rfl fun v _ => by rw [hcoord v.1 v.2]
    rw [he] at hdeg
    have hm : ((Units.dirichletUnitTheorem.w₀ : InfinitePlace K).mult : ℝ) ≠ 0 := by
      exact_mod_cast (InfinitePlace.mult_pos).ne'
    exact mul_left_cancel₀ hm (by linarith)
  · exact hcoord w hw

/-! ### `δ_A` is an isomorphism -/

/-- **`ker deg^arith ⊆ ℝ·div(K^×)`.** -/
theorem ker_degArith_le : LinearMap.ker (degArith K) ≤ ratFun K := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨a, ha, ha1⟩ := exists_ratFun_fst x.1
  have hy : x - a = (0, (x - a).2) := Prod.ext (by simp [ha1]) rfl
  have hdeg : degArith K (0, (x - a).2) = 0 := by
    rw [← hy, map_sub, hx, degArith_ratFun ha, sub_zero]
  have := inf_mem_ratFun _ hdeg
  rw [← hy] at this
  simpa using (ratFun K).add_mem this ha

/-- **[FrdI], Theorem 6.4(i): `δ_A` is injective.** -/
theorem picDeg_injective : Function.Injective (picDeg K) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ ker_degArith_le

variable (K) in
/-- **[FrdI], Theorem 6.4(i): `δ_A : Pic_Φ(A) ≅ ℝ`.** -/
noncomputable def picDegEquiv : (ArithDiv K ⧸ ratFun K) ≃ₗ[ℝ] ℝ :=
  LinearEquiv.ofBijective (picDeg K) ⟨picDeg_injective, picDeg_surjective⟩

@[simp] lemma picDegEquiv_apply (x : ArithDiv K ⧸ ratFun K) : picDegEquiv K x = picDeg K x :=
  rfl

namespace GlobalRealified

/-- **Objects of `C^⊩` are classified by their degree.** -/
theorem nonempty_iso_iff_degree_eq (X Y : GlobalRealified K) :
    Nonempty (X ≅ Y) ↔ X.degree = Y.degree := by
  refine ⟨fun ⟨e⟩ => degree_eq_of_iso e, fun h => ?_⟩
  obtain ⟨⟨⟩, α⟩ := X
  obtain ⟨⟨⟩, β⟩ := Y
  have hk : α - β ∈ ratFun K := ker_degArith_le (by
    change degArith K (α - β) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h)
  obtain ⟨e, -⟩ := (Model.nonempty_iso_iff (Φ := phiRlf K) (B := bRlf K) (divB := divBRlf K)
    pt α β).mpr ⟨⟨_, hk⟩, rfl⟩
  exact ⟨e⟩

end GlobalRealified

end Frobenioid

end Iut
