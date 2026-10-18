/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Iut.Frobenioid.GlobalGaloisRlf

/-!
# The arithmetic degree of realified pull-backs

[FrdI], Example 6.3 (l.6219–6326 of `~/iut-scratch/frd/FrdI.txt`): the arithmetic degree
`deg^arith_L : Φ(L)^gp → ℝ`. On `B(G)⁰` the degrees of the divisor monoids are compatible with
pull-back up to the degree of the extension; `degG_pbDiv` (`GlobalGaloisCmp.lean`) is the integral
statement. Here:

* **`degArith_castG`**: `deg^arith(castG x) = degG x`, i.e. `log N(I) = Σ_w ord_w(I)·log N(𝔭_w)`
  (checked on the primes `𝔭_w`, `absNorm_primeU`);
* **`degArith_pbR`**: `deg^arith_L(σ^* x) = [L:K]·deg^arith_K(x)` for ℝ-divisors `x`.
-/

namespace Iut

namespace Frobenioid

open CategoryTheory NumberField FractionalIdeal Arakelov

open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- `N(𝔭_w) = N(w)`. -/
lemma absNorm_primeU (w : FinitePlace K) :
    ((absNorm ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) : ℚ) : ℝ) = primeNorm w := by
  classical
  change ((absNorm (Arakelov.FracIdeal.ofCounts K
    ((Finsupp.single w 1).equivMapDomain FinitePlace.equivHeightOneSpectrum)) : ℚ) : ℝ) = _
  have h : Arakelov.FracIdeal.ofCounts K
      ((Finsupp.single w (1 : ℤ)).equivMapDomain FinitePlace.equivHeightOneSpectrum) =
      ((w.maximalIdeal.asIdeal : Ideal (𝓞 K)) : FI K) := by
    rw [Arakelov.FracIdeal.ofCounts, Finsupp.equivMapDomain_single,
      finprod_eq_single _ (FinitePlace.equivHeightOneSpectrum w)]
    · simp
    · intro v hv
      rw [Finsupp.single_apply, if_neg (Ne.symm hv), zpow_zero]
  rw [h, coeIdeal_absNorm, primeNorm]
  simp

/-- The finite part of `log N(I)` in coordinates. -/
noncomputable def logNormFin : (FinitePlace K →₀ ℤ) →+ ℝ :=
  Finsupp.liftAddHom fun w => (zmultiplesHom ℝ (Real.log (primeNorm w)))

lemma logNormFin_single (w : FinitePlace K) (n : ℤ) :
    logNormFin (Finsupp.single w n) = n * Real.log (primeNorm w) := by
  simp [logNormFin]

/-- **`log N(I) = Σ_w ord_w(I)·log N(𝔭_w)`.** -/
theorem log_absNorm_eq (x : Additive (FI K)ˣ) :
    Real.log ((absNorm ((Additive.toMul x : (FI K)ˣ) : FI K) : ℚ) : ℝ) =
      logNormFin (toZFin K x) := by
  let f : (FinitePlace K →₀ ℤ) →+ ℝ :=
    { toFun := fun c => Real.log ((absNorm ((Additive.toMul ((toZ K).symm (c, 0)).1 : (FI K)ˣ) :
          FI K) : ℚ) : ℝ)
      map_zero' := by
        rw [show ((0, 0) : ArithDivZ K) = 0 from rfl, map_zero]
        simp
      map_add' := fun a b => by
        rw [show ((a + b, 0) : ArithDivZ K) = (a, 0) + (b, 0) by simp, map_add]
        change Real.log ((absNorm (((Additive.toMul ((toZ K).symm (a, 0)).1 *
          Additive.toMul ((toZ K).symm (b, 0)).1 : (FI K)ˣ)) : FI K) : ℚ) : ℝ) = _
        rw [Units.val_mul, map_mul, Rat.cast_mul,
          Real.log_mul (by exact_mod_cast absNorm_unit_ne_zero _)
            (by exact_mod_cast absNorm_unit_ne_zero _)] }
  have hf : f = logNormFin := by
    refine Finsupp.addHom_ext fun w n => ?_
    have hs : Finsupp.single w n = n • Finsupp.single w (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_zsmul, map_zsmul, logNormFin_single]
    change n • Real.log ((absNorm ((Additive.toMul (primeU w) : (FI K)ˣ) : FI K) : ℚ) : ℝ) = _
    rw [absNorm_primeU]
    simp
  have hx : x = ((toZ K).symm (toZFin K x, 0)).1 := (ofZFin_toZFin x).symm
  conv_lhs => rw [hx]
  exact congrArg (fun g : (FinitePlace K →₀ ℤ) →+ ℝ => g (toZFin K x)) hf

/-- **`deg^arith(castG x) = degG x`.** -/
theorem degArith_castG (x : ArithDivG K) : degArith K (castG K x) = degG K x := by
  rw [castG_apply, degArith_apply]
  change _ = Real.log ((absNorm ((Additive.toMul x.1 : (FI K)ˣ) : FI K) : ℚ) : ℝ) +
    ∑ v, (v.mult : ℝ) * x.2 v
  rw [log_absNorm_eq]
  congr 1
  rw [castDiv_fst', castFin, Finsupp.mapRange.addMonoidHom_apply,
    Finsupp.sum_mapRange_index (fun _ => zero_mul _), logNormFin, Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun w _ => ?_
  simp [zsmul_eq_mul]

variable {L : Type*} [Field L] [NumberField L] [Algebra K L]

/-- **`deg^arith_L(σ^* x) = [L:K]·deg^arith_K(x)`** for ℝ-divisors. -/
theorem degArith_pbR (x : ArithDiv K) :
    degArith L (pbR (algebraMap K L) x) = Module.finrank K L * degArith K x := by
  have : (degArith L).comp (pbR (algebraMap K L)) = (Module.finrank K L : ℝ) • degArith K :=
    linearMap_ext_castDiv fun y => by
      have hy : castDiv K y = castG K ((toZ K).symm y) := by
        rw [castG_apply, AddEquiv.apply_symm_apply]
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hy, ← castG_pbDiv, degArith_castG,
        degArith_castG, degG_pbDiv, smul_eq_mul]
  exact LinearMap.congr_fun this x

end Frobenioid

end Iut
