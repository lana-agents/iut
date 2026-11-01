/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.Tempered.RatFunBase
import Mathlib.NumberTheory.Padics.Complex

/-!
# Isometric embeddings of finite extensions of `ℚ_p` into `ℂ_p` (MR18 T8/T10 instantiation)

The `L`-statements of `RatFunBase.lean` take an isometric field homomorphism `φ : L → Ω` into a
complete algebraically closed nonarchimedean field `Ω`. For `L` an algebraic normed extension of
`ℚ_p` (e.g. a finite extension, the base fields `K_v` of [EtTh] §3 and IUT I Ex 3.2) this file
supplies `Ω = ℂ_[p]` (Mathlib's `PadicComplex`, algebraically closed by `PadicComplex.isAlgClosed`)
together with such a `φ`.

The proof is uniqueness of the extension of the `p`-adic norm: any `ℚ_p`-embedding
`ι : L → \bar{ℚ}_p` (from `IsAlgClosed.lift`) is isometric because both norms equal the spectral
norm (Mathlib `NormedAlgebra.norm_eq_spectralNorm`, a consequence of `spectralNorm_unique`), and
the spectral norm only depends on the minimal polynomial (`minpoly.algHom_eq`). The norm of
`ℂ_[p]` extends that of `\bar{ℚ}_p` (`PadicComplex.norm_extends`).

## Main results

* `PadicEmbed.norm_algHom_padicAlgCl`: every `ℚ_p`-algebra map `L → \bar{ℚ}_p` is isometric.
* `PadicEmbed.toPadicComplex p L : L →ₐ[ℚ_[p]] ℂ_[p]` and `PadicEmbed.norm_toPadicComplex`:
  an isometric `ℚ_p`-embedding `L → ℂ_p`.
* `PadicEmbed.norm_algHom_padicComplex`: in fact **every** `ℚ_p`-algebra map `L → ℂ_p` is
  isometric (its image is algebraic over `ℚ_p`, so lies in a finite extension carrying the
  restricted norm, which is again the spectral norm).
* `PadicEmbed.completeSpace_of_finiteDimensional`, `PadicEmbed.isUltrametricDist`: a finite
  normed extension of `ℚ_p` satisfies the standing hypotheses `[CompleteSpace L]`,
  `[IsUltrametricDist L]` of `RatFunBase.lean`.
* `PadicEmbed.exists_norm_eq_rpow_padicAlgCl`, `PadicEmbed.exists_norm_eq_rpow_padicComplex`:
  the value groups of `\bar{ℚ}_p` and `ℂ_p` lie in `p^ℚ` (spectral norm = `|a₀|^{1/d}` for the
  minimal polynomial; density of `\bar{ℚ}_p` in `ℂ_p` and the ultrametric inequality). This is the
  hypothesis `ValueGroupRat` of `EllDiv.lean` for `ℂ_p` (`valueGroupRat_padicComplex`).
-/

namespace Iut.Frobenioid.BAn.PadicEmbed

/-- A normed extension of `ℚ_p` is ultrametric. -/
theorem isUltrametricDist (p : ℕ) [Fact p.Prime] (L : Type*) [NormedField L]
    [NormedAlgebra ℚ_[p] L] : IsUltrametricDist L :=
  IsUltrametricDist.of_normedAlgebra ℚ_[p]

/-- A finite-dimensional normed extension of `ℚ_p` is complete. -/
theorem completeSpace_of_finiteDimensional (p : ℕ) [Fact p.Prime] (L : Type*) [NormedField L]
    [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L] : CompleteSpace L :=
  FiniteDimensional.complete ℚ_[p] L

variable (p : ℕ) [hp : Fact p.Prime]
variable (L : Type*) [NormedField L] [NormedAlgebra ℚ_[p] L]

variable {p L} [Algebra.IsAlgebraic ℚ_[p] L]

/-- **Every `ℚ_p`-embedding `L → \bar{ℚ}_p` is isometric** (uniqueness of the extension of the
`p`-adic norm to an algebraic extension). -/
theorem norm_algHom_padicAlgCl (ι : L →ₐ[ℚ_[p]] PadicAlgCl p) (x : L) : ‖ι x‖ = ‖x‖ := by
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x, ← PadicAlgCl.spectralNorm_eq]
  simp only [spectralNorm, minpoly.algHom_eq ι ι.injective x]

variable (p L) in
/-- **An isometric `ℚ_p`-embedding `L → ℂ_p`**: a `ℚ_p`-embedding into `\bar{ℚ}_p` (algebraic
closure) followed by the inclusion `\bar{ℚ}_p ⊆ ℂ_p`. -/
noncomputable def toPadicComplex : L →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (IsAlgClosed.lift : L →ₐ[ℚ_[p]] _)

theorem norm_toPadicComplex (x : L) : ‖toPadicComplex p L x‖ = ‖x‖ := by
  simp only [toPadicComplex, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq, PadicComplex.norm_extends, norm_algHom_padicAlgCl]

variable (p L) in
/-- The ring-homomorphism form used by `RatFunBase.lean` (`Entire.map`, `Mero.map`). -/
noncomputable def toPadicComplexHom : L →+* ℂ_[p] := (toPadicComplex p L).toRingHom

theorem norm_toPadicComplexHom (x : L) : ‖toPadicComplexHom p L x‖ = ‖x‖ :=
  norm_toPadicComplex x

/-- **Every `ℚ_p`-algebra map `L → ℂ_p` is isometric.** The image of `x` is algebraic over `ℚ_p`;
on the finite extension `ℚ_p(ψ x) ⊆ ℂ_p` the restricted norm is the spectral norm, which only
depends on the minimal polynomial, and so does the norm of `x`. -/
theorem norm_algHom_padicComplex (ψ : L →ₐ[ℚ_[p]] ℂ_[p]) (x : L) : ‖ψ x‖ = ‖x‖ := by
  have hx : IsIntegral ℚ_[p] (ψ x) := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral.map ψ
  let E := IntermediateField.adjoin ℚ_[p] ({ψ x} : Set ℂ_[p])
  haveI : FiniteDimensional ℚ_[p] E := IntermediateField.adjoin.finiteDimensional hx
  haveI : Algebra.IsAlgebraic ℚ_[p] E := Algebra.IsAlgebraic.of_finite ℚ_[p] E
  let y : E := ⟨ψ x, IntermediateField.mem_adjoin_simple_self ℚ_[p] (ψ x)⟩
  have h1 : ‖ψ x‖ = ‖y‖ := rfl
  rw [h1, NormedAlgebra.norm_eq_spectralNorm ℚ_[p] y, NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x]
  simp only [spectralNorm]
  have hy : minpoly ℚ_[p] y = minpoly ℚ_[p] x :=
    (IntermediateField.minpoly_eq y).trans (minpoly.algHom_eq ψ ψ.injective x)
  exact congrArg spectralValue hy

/-! ### The value groups of `\bar{ℚ}_p` and `ℂ_p` are `p^ℚ` -/

variable (p)

/-- Every nonzero element of the algebraic closure of `ℚ_[p]` has norm in `p ^ ℚ`. -/
theorem exists_norm_eq_rpow_padicAlgCl (x : PadicAlgCl p) (hx : x ≠ 0) :
    ∃ m : ℚ, ‖x‖ = (p : ℝ) ^ (m : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc : (minpoly ℚ_[p] x).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  have hp : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast, ← Real.rpow_mul hp.le]
  push_cast
  ring_nf

/-- Every nonzero element of `ℂ_[p]` has norm in `p ^ ℚ`. -/
theorem exists_norm_eq_rpow_padicComplex (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ m : ℚ, ‖x‖ = (p : ℝ) ^ (m : ℝ) := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x y < ‖x‖ :=
    (UniformSpace.Completion.denseRange_coe.exists_dist_lt x hpos)
  have hyx : ‖(y : ℂ_[p]) - x‖ < ‖x‖ := by rwa [← dist_eq_norm, dist_comm]
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyx
  obtain ⟨m, hm⟩ := exists_norm_eq_rpow_padicAlgCl p y hy0
  refine ⟨m, ?_⟩
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hyx.ne'
  rw [add_sub_cancel, max_eq_left hyx.le, PadicComplex.norm_extends] at h
  rw [← h, hm]

end Iut.Frobenioid.BAn.PadicEmbed
