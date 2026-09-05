/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Iut.Tripod.Basic

/-!
# Northcott's theorem for the tripod

This file proves `Iut.Tripod.NorthcottHyp` of `Iut.Tripod.Basic`: for every `d` and `H`, there
are only finitely many algebraic numbers `λ ∈ ℚ̄ ∖ {0, 1}` of degree `[ℚ(λ) : ℚ] ≤ d` and
absolute logarithmic Weil height `≤ H` (`Iut.Tripod.northcottHyp`).

## The proof

The proof is uniform in the field of definition `K = ℚ(λ)` and only uses the finiteness of the
set of integer polynomials of bounded degree and bounded coefficients
(`Polynomial.bUnion_roots_finite`), together with two facts about the height of `λ` in `K`:

- every conjugate `φ(λ)`, `φ : K →+* ℂ`, is bounded by the multiplicative height
  `H(λ) = exp(logHeight₁ λ)` (`Iut.Tripod.norm_embedding_le_mulHeight₁`), since the
  contribution of the infinite place of `φ` to `logHeight₁ λ` is `log⁺|φ(λ)|`;
- there is a positive integer `n ≤ H(λ)` with `nλ` an algebraic integer
  (Mathlib's `NumberField.exists_nat_le_mulHeight₁`).

Then `y = nλ` is an algebraic integer whose conjugates are bounded by `n · H(λ) ≤ H(λ)²`, so
the coefficients of its minimal polynomial `minpoly ℤ y ∈ ℤ[X]` (of degree `≤ d`) are bounded
in terms of `d` and `H` (`Polynomial.coeff_bdd_of_roots_le`, via the identification of the
complex roots of the minimal polynomial with the conjugates,
`NumberField.Embeddings.range_eval_eq_rootSet_minpoly`). Hence `λ = y/n` lies in the finite
set of quotients by `n ≤ exp(dH)` of the roots in `ℚ̄` of the finitely many integer
polynomials of degree `≤ d` with coefficients bounded by the resulting bound.
-/

namespace Iut.Tripod

open NumberField Polynomial

/-- Each conjugate `φ(x)` of an element `x` of a number field `K` is bounded in absolute value
by the multiplicative height `mulHeight₁ x = exp (logHeight₁ x)` of `x`: the contribution
`mult(v) log⁺ |φ x|` of the infinite place `v` of `φ` to `logHeight₁ x` is at least
`log⁺ |φ x| ≥ log |φ x|`. -/
theorem norm_embedding_le_mulHeight₁ {K : Type*} [Field K] [NumberField K] (x : K)
    (φ : K →+* ℂ) : ‖φ x‖ ≤ Height.mulHeight₁ x := by
  have h1 : Real.posLog (InfinitePlace.mk φ x) ≤ Height.logHeight₁ x := by
    rw [logHeight₁_eq]
    have hfin : 0 ≤ ∑ᶠ v : FinitePlace K, Real.posLog (v x) :=
      finsum_nonneg fun _ ↦ Real.posLog_nonneg
    have hinf : Real.posLog (InfinitePlace.mk φ x) ≤
        ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v x) :=
      calc Real.posLog (InfinitePlace.mk φ x)
          ≤ ((InfinitePlace.mk φ).mult : ℝ) * Real.posLog (InfinitePlace.mk φ x) :=
            le_mul_of_one_le_left Real.posLog_nonneg InfinitePlace.one_le_mult
        _ ≤ _ := Finset.single_le_sum
            (f := fun v : InfinitePlace K ↦ (v.mult : ℝ) * Real.posLog (v x))
            (fun v _ ↦ mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg) (Finset.mem_univ _)
    linarith
  rw [InfinitePlace.apply, Height.logHeight₁_eq_log_mulHeight₁] at h1
  have h2 : ‖φ x‖ ≤ Real.exp (Real.posLog ‖φ x‖) := by
    rcases eq_or_ne (φ x) 0 with h | h
    · rw [h, norm_zero]
      exact (Real.exp_pos _).le
    · calc ‖φ x‖ = Real.exp (Real.log ‖φ x‖) := (Real.exp_log (norm_pos_iff.mpr h)).symm
        _ ≤ Real.exp (Real.posLog ‖φ x‖) :=
            Real.exp_le_exp.mpr (by rw [Real.posLog_apply]; exact le_max_right _ _)
  calc ‖φ x‖ ≤ Real.exp (Real.posLog ‖φ x‖) := h2
    _ ≤ Real.exp (Real.log (Height.mulHeight₁ x)) := Real.exp_le_exp.mpr h1
    _ = Height.mulHeight₁ x := Real.exp_log (Height.mulHeight₁_pos x)

/-- The bound `exp (d · max H 0)` on the multiplicative height `exp (logHeight₁ (gen λ))` of a
point `λ` of degree `≤ d` and height `htCan λ ≤ H`. -/
noncomputable def heightBound (d : ℕ) (H : ℝ) : ℝ := Real.exp (d * max H 0)

theorem heightBound_pos (d : ℕ) (H : ℝ) : 0 < heightBound d H := Real.exp_pos _

/-- The multiplicative height `exp (logHeight₁ (gen λ))` of a point of degree `≤ d` and height
`htCan ≤ H` is at most `heightBound d H = exp (d · max H 0)`. -/
theorem mulHeight₁_gen_le {d : ℕ} {H : ℝ} {x : Pt} (hd : x ∈ ptLE d) (hH : htCan x ≤ H) :
    Height.mulHeight₁ (gen x.1) ≤ heightBound d H := by
  rw [heightBound, ← Real.exp_log (Height.mulHeight₁_pos _),
    ← Height.logHeight₁_eq_log_mulHeight₁]
  apply Real.exp_le_exp.mpr
  rw [← deg_mul_htCan x]
  exact mul_le_mul (by exact_mod_cast hd) (hH.trans (le_max_left _ _)) (htCan_nonneg _)
    (Nat.cast_nonneg _)

/-- The degree of the minimal polynomial over `ℤ` of an algebraic integer `y` of a number field
`K` is at most `[K : ℚ]`. -/
theorem natDegree_minpoly_int_le {K : Type*} [Field K] [NumberField K] {y : K}
    (hy : IsIntegral ℤ y) : (minpoly ℤ y).natDegree ≤ Module.finrank ℚ K := by
  rw [← (minpoly.monic hy).natDegree_map (algebraMap ℤ ℚ),
    ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy]
  exact minpoly.natDegree_le _

/-- The bound `⌈max B 1 ^ d · C(d, ⌊d/2⌋)⌉` on the coefficients of the minimal polynomial of an
algebraic integer of degree `≤ d` all of whose conjugates are bounded by `B`. -/
noncomputable def coeffBoundOf (d : ℕ) (B : ℝ) : ℕ := ⌈max B 1 ^ d * d.choose (d / 2)⌉₊

/-- The coefficients of the minimal polynomial over `ℤ` of an algebraic integer `y` of a number
field `K` of degree `[K : ℚ] ≤ d` all of whose conjugates `φ y`, `φ : K →+* ℂ`, are bounded by
`B` lie in `[-coeffBoundOf d B, coeffBoundOf d B]` (`Polynomial.coeff_bdd_of_roots_le`). -/
theorem coeff_minpoly_int_mem_Icc {K : Type*} [Field K] [NumberField K] {y : K}
    (hy : IsIntegral ℤ y) {d : ℕ} (hd : Module.finrank ℚ K ≤ d) {B : ℝ}
    (hB : ∀ φ : K →+* ℂ, ‖φ y‖ ≤ B) (i : ℕ) :
    (minpoly ℤ y).coeff i ∈ Set.Icc (-(coeffBoundOf d B : ℤ)) (coeffBoundOf d B) := by
  have hpQ : minpoly ℚ y = (minpoly ℤ y).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hy
  have hpdeg : (minpoly ℚ y).natDegree ≤ d := (minpoly.natDegree_le _).trans hd
  have h := coeff_bdd_of_roots_le (B := B) (algebraMap ℚ ℂ)
    (minpoly.monic (Algebra.IsIntegral.isIntegral y))
    (IsAlgClosed.splits _) hpdeg (fun z hz ↦ ?_) i
  · rw [hpQ, Polynomial.map_map, coeff_map] at h
    have hcast : ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)) ((minpoly ℤ y).coeff i) =
        (((minpoly ℤ y).coeff i : ℤ) : ℂ) := by
      simp
    rw [hcast, Complex.norm_intCast] at h
    rw [Set.mem_Icc, ← abs_le, coeffBoundOf]
    exact_mod_cast h.trans (Nat.le_ceil _)
  · classical
    rw [← Multiset.mem_toFinset] at hz
    obtain ⟨φ, rfl⟩ := (Embeddings.range_eval_eq_rootSet_minpoly K ℂ y).symm.subset hz
    exact hB φ

/-- The image of an algebraic integer `y` of a number field `K` in a field `L ⊇ K` is a root of
the minimal polynomial `minpoly ℤ y ∈ ℤ[X]` (stated with `eval₂` along `Int.castRingHom L`, to be
independent of the choice of the `ℤ`-algebra structure on `L`). -/
theorem eval₂_minpoly_int_algebraMap {K : Type*} [Field K] [NumberField K] (y : K)
    (L : Type*) [Field L] [Algebra K L] :
    (minpoly ℤ y).eval₂ (Int.castRingHom L) (algebraMap K L y) = 0 := by
  rw [← algebraMap_int_eq, ← aeval_def, aeval_algebraMap_apply, minpoly.aeval ℤ, map_zero]

/-- The bound on the coefficients of the minimal polynomial of `nλ` for a point `λ` of degree
`≤ d` and height `≤ H`, where `n ≤ heightBound d H` is a denominator of `λ`: the conjugates of
`nλ` are bounded by `heightBound d H ^ 2`. -/
noncomputable def coeffBound (d : ℕ) (H : ℝ) : ℕ :=
  coeffBoundOf d (heightBound d H * heightBound d H)

/-- The integer polynomials of degree `≤ d` with coefficients bounded by `coeffBound d H`. -/
def polySet (d : ℕ) (H : ℝ) : Set ℤ[X] :=
  {f | f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Set.Icc (-(coeffBound d H : ℤ)) (coeffBound d H)}

theorem mem_polySet {d : ℕ} {H : ℝ} {f : ℤ[X]} :
    f ∈ polySet d H ↔
      f.natDegree ≤ d ∧ ∀ i, f.coeff i ∈ Set.Icc (-(coeffBound d H : ℤ)) (coeffBound d H) :=
  Iff.rfl

open scoped Classical in
/-- The set of roots in `ℚ̄` of the polynomials of `polySet d H` is finite. -/
theorem finite_roots_polySet (d : ℕ) (H : ℝ) :
    (⋃ f ∈ polySet d H, ((f.map (Int.castRingHom Qbar)).roots.toFinset : Set Qbar)).Finite :=
  bUnion_roots_finite (Int.castRingHom Qbar) d (Set.finite_Icc _ _)

/-- For a point `λ` of degree `≤ d` and height `≤ H` there are a positive integer
`n ≤ heightBound d H` and a monic integer polynomial `p ∈ polySet d H` such that `nλ` is a root
of `p`: `p` is the minimal polynomial of the algebraic integer `nλ`. -/
theorem exists_nat_mem_polySet {d : ℕ} {H : ℝ} {x : Pt} (hd : x ∈ ptLE d) (hH : htCan x ≤ H) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℝ) ≤ heightBound d H ∧ ∃ p ∈ polySet d H, p.Monic ∧
      p.eval₂ (Int.castRingHom Qbar) ((n : Qbar) * x.1) = 0 := by
  have hmul := mulHeight₁_gen_le hd hH
  have hB₀_pos := heightBound_pos d H
  obtain ⟨n, hn0, hnle, hint⟩ := exists_nat_le_mulHeight₁ (gen x.1)
  have hnB : (n : ℝ) ≤ heightBound d H := hnle.trans hmul
  have hd' : Module.finrank ℚ (fieldOf x.1) ≤ d := by
    rw [← deg_eq_finrank]
    exact hd
  have hconj : ∀ φ : fieldOf x.1 →+* ℂ,
      ‖φ ((n : fieldOf x.1) * gen x.1)‖ ≤ heightBound d H * heightBound d H := by
    intro φ
    rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul hnB ((norm_embedding_le_mulHeight₁ _ φ).trans hmul) (norm_nonneg _)
      hB₀_pos.le
  refine ⟨n, hn0, hnB, _, ⟨(natDegree_minpoly_int_le hint).trans hd',
    coeff_minpoly_int_mem_Icc hint hd' hconj⟩, minpoly.monic hint, ?_⟩
  -- `nλ` is a root of its minimal polynomial
  have hy : (n : Qbar) * x.1 = algebraMap (fieldOf x.1) Qbar ((n : fieldOf x.1) * gen x.1) := by
    simp
  rw [hy]
  exact eval₂_minpoly_int_algebraMap _ Qbar

/-- **Northcott's theorem for the tripod**: for every `d` and `H`, there are only finitely many
`λ ∈ ℚ̄ ∖ {0, 1}` with `[ℚ(λ) : ℚ] ≤ d` and absolute logarithmic Weil height `≤ H`. -/
theorem northcottHyp : NorthcottHyp := by
  classical
  intro d H
  -- the finite set `T` of the quotients `y / n` of the roots `y` of the polynomials of
  -- `polySet d H` by the integers `1 ≤ n ≤ heightBound d H`
  have hTfin : (⋃ n ∈ Finset.Icc 1 ⌊heightBound d H⌋₊, (fun y : Qbar ↦ (n : Qbar)⁻¹ * y) ''
      (⋃ f ∈ polySet d H, ((f.map (Int.castRingHom Qbar)).roots.toFinset : Set Qbar))).Finite :=
    (Finset.finite_toSet _).biUnion fun n _ ↦ (finite_roots_polySet d H).image _
  refine (hTfin.preimage Subtype.val_injective.injOn).subset fun x ⟨hd, hH⟩ ↦ ?_
  obtain ⟨n, hn0, hnB, p, hp, hpm, hroot⟩ := exists_nat_mem_polySet hd hH
  have hn' : (n : Qbar) ≠ 0 := by exact_mod_cast hn0
  simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Finset.mem_Icc,
    Multiset.mem_toFinset, exists_prop]
  refine ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr hn0, Nat.le_floor hnB⟩, (n : Qbar) * x.1,
    ⟨p, hp, ?_⟩, inv_mul_cancel_left₀ hn' _⟩
  rw [mem_roots (hpm.map (Int.castRingHom Qbar)).ne_zero, IsRoot.def, eval_map]
  exact hroot

end Iut.Tripod
