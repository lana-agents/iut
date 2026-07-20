/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
import Iut4Sec1.Real.LogError

/-!
# Constructible mixed-characteristic local fields

This module constructs the valuation ring, normalized discrete order,
ramification and residue data, and different of every finite-dimensional field
extension of `ℚ_[p]`. The norm, completeness, DVR structure, and finite residue
field are derived from the spectral norm; none is a constructor hypothesis.

The canonical fractional ideal of exponent `n / e` is the `n`th integral power
of the maximal ideal. The module also proves the elementary parameter equality
from Proposition 1.2 and gives a degree-two extension obtained from `X² - 2`.
-/

noncomputable section

open scoped NormedField Padic WithZero
open Valued.integer

namespace Iut4Sec1

variable (p : ℕ) [Fact p.Prime]
variable (L : Type*) [Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The norm valuation associated to the spectral norm on a finite extension of `ℚ_[p]`. -/
noncomputable def spectralValuation : Valuation L NNReal := by
  letI : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField ℚ_[p] L
  letI : NormedAlgebra ℚ_[p] L := spectralNorm.normedAlgebra ℚ_[p] L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  exact NormedField.valuation

/-- The norm valuation on `ℚ_[p]`. -/
noncomputable def baseValuation : Valuation ℚ_[p] NNReal := NormedField.valuation

private noncomputable def baseRingEquivPadicInt : (baseValuation p).integer ≃+* ℤ_[p] where
  toFun x := ⟨x, by
    have hx := x.2
    change ‖(x : ℚ_[p])‖₊ ≤ 1 at hx
    exact_mod_cast hx⟩
  invFun x := ⟨x, by
    change baseValuation p (x : ℚ_[p]) ≤ 1
    rw [baseValuation, NormedField.valuation_apply]
    exact_mod_cast x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private noncomputable instance baseIntegerRingIsDVR :
    IsDiscreteValuationRing (baseValuation p).integer :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (baseRingEquivPadicInt p).symm

private theorem spectralResidueFieldFinite :
    Finite (IsLocalRing.ResidueField (spectralValuation p L).integer) := by
  letI : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField ℚ_[p] L
  letI : NormedAlgebra ℚ_[p] L := spectralNorm.normedAlgebra ℚ_[p] L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : CompleteSpace L := spectralNorm.completeSpace ℚ_[p] L
  letI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  letI : Valued L NNReal := NormedField.toValued
  letI : Valuation.RankOne (Valued.v : Valuation L NNReal) := by
    change Valuation.RankOne (NormedField.valuation (K := L))
    infer_instance
  have hRing : (Valued.integer L : Set L) = Metric.closedBall 0 1 := by
    ext x
    change Valued.v x ≤ 1 ↔ dist x 0 ≤ 1
    change NormedField.valuation x ≤ 1 ↔ dist x 0 ≤ 1
    rw [NormedField.valuation_apply, dist_zero_right]
    exact (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := 1)).symm
  letI : CompactSpace (Valued.integer L) :=
    isCompact_iff_compactSpace.mp (hRing.symm ▸ isCompact_closedBall 0 1)
  change Finite (Valued.ResidueField L)
  exact
    compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
      (inferInstance : CompactSpace (Valued.integer L)) |>.2.2

private noncomputable def pInBaseRing : (baseValuation p).integer := ⟨p, by
  change NormedField.valuation (p : ℚ_[p]) ≤ 1
  rw [NormedField.valuation_apply]
  exact_mod_cast Padic.norm_p_lt_one.le⟩

private theorem base_maximalIdeal_eq_span_p :
    IsLocalRing.maximalIdeal (baseValuation p).integer =
      Ideal.span ({pInBaseRing p} : Set (baseValuation p).integer) := by
  let e := baseRingEquivPadicInt p
  have hmap :
      (IsLocalRing.maximalIdeal (baseValuation p).integer).map e =
        (Ideal.span ({pInBaseRing p} : Set (baseValuation p).integer)).map e := by
    rw [IsLocalRing.map_ringEquiv_maximalIdeal, Ideal.map_span, Set.image_singleton,
      show e (pInBaseRing p) = (p : ℤ_[p]) by rfl, PadicInt.maximalIdeal_eq_span_p]
  apply_fun Ideal.comap e at hmap
  simpa only [Ideal.comap_map_of_surjective e e.surjective,
    Ideal.comap_bot_of_injective e e.injective, sup_bot_eq] using hmap

/--
Standard valuation data for a finite extension of `ℚ_[p]`.

The fields record only the spectral valuation and its usual local-ring laws.
The normalized order, positive ramification index, residue degree, and different
are definitions or theorems below rather than assumed conclusions.
-/
structure MixedCharLocalFieldData where
  /-- The multiplicative norm valuation on the extension. -/
  valuation : Valuation L NNReal
  /-- Compatibility with the canonical spectral norm. -/
  valuation_eq_spectral : valuation = spectralValuation p L
  /-- Compatibility with the norm valuation on `ℚ_[p]`. -/
  [valuationExtension : (baseValuation p).HasExtension valuation]
  /-- The spectral integer ring is a discrete valuation ring. -/
  [integerRingIsDVR : IsDiscreteValuationRing valuation.integer]
  /-- The image of `p` belongs to the maximal ideal. -/
  p_valuation_lt_one : valuation (algebraMap ℚ_[p] L p) < 1

namespace MixedCharLocalFieldData

variable {p L} (D : MixedCharLocalFieldData p L)

abbrev ringOfIntegers := D.valuation.integer
abbrev baseRingOfIntegers := (baseValuation p).integer

/-- The maximal ideal of the spectral integer ring. -/
noncomputable def maximalIdeal : Ideal D.ringOfIntegers := by
  letI := D.integerRingIsDVR
  exact IsLocalRing.maximalIdeal _

/-- The canonical integer-valued discrete valuation of the extension. -/
noncomputable def discreteValuation : Valuation L ℤᵐ⁰ := by
  letI := D.integerRingIsDVR
  exact (IsDiscreteValuationRing.maximalIdeal D.ringOfIntegers).valuation L

noncomputable def pElement : L := algebraMap ℚ_[p] L p

/-- The positive exponent of `p` under the canonical discrete valuation. -/
noncomputable def ramificationIndex : ℕ :=
  (-WithZero.log (D.discreteValuation (pElement (p := p) (L := L)))).toNat

/-- The ideal-theoretic ramification index of the extension. -/
noncomputable def idealRamificationIndex : ℕ := by
  letI := D.valuationExtension
  exact (IsLocalRing.maximalIdeal D.ringOfIntegers).ramificationIdx
    (baseRingOfIntegers (p := p))

/-- The inertia degree of the extension's maximal ideal over `ℤ_[p]`. -/
noncomputable def residueDegree : ℕ := by
  letI := D.valuationExtension
  exact (IsLocalRing.maximalIdeal D.ringOfIntegers).inertiaDeg
    (baseRingOfIntegers (p := p))

/-- The local different of the spectral integer ring over the base integer ring. -/
noncomputable def different : Ideal D.ringOfIntegers := by
  letI := D.valuationExtension
  letI := D.integerRingIsDVR
  exact differentIdeal (baseRingOfIntegers (p := p)) D.ringOfIntegers

/-- The rational order normalized to send `p` to `1`, and `0` to `⊤`. -/
noncomputable def normalizedOrder (x : L) : WithTop ℚ := by
  classical
  exact if x = 0 then ⊤ else
    (((-WithZero.log (D.discreteValuation x) : ℤ) : ℚ) /
      (D.ramificationIndex : ℚ) : ℚ)

/-- The rational exponent represented by the integer numerator `n`. -/
noncomputable def fractionalExponentValue (n : ℤ) : ℚ :=
  n / D.ramificationIndex

/-- The canonical fractional ideal with normalized exponent `n / e`. -/
noncomputable def fractionalPower (n : ℤ) :
    FractionalIdeal (nonZeroDivisors D.ringOfIntegers) L := by
  letI := D.integerRingIsDVR
  exact (↑(IsLocalRing.maximalIdeal D.ringOfIntegers) :
    FractionalIdeal (nonZeroDivisors D.ringOfIntegers) L) ^ n

private theorem p_mem_maximalIdeal :
    (⟨pElement (p := p) (L := L), D.p_valuation_lt_one.le⟩ : D.ringOfIntegers) ∈
      IsLocalRing.maximalIdeal D.ringOfIntegers := by
  apply (Valuation.mem_maximalIdeal_iff L D.valuation).2
  exact D.p_valuation_lt_one

omit [FiniteDimensional ℚ_[p] L] in
private theorem p_ne_zero : pElement (p := p) (L := L) ≠ 0 := by
  exact (map_ne_zero (algebraMap ℚ_[p] L)).2
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem discreteValuation_p_lt_one :
    D.discreteValuation (pElement (p := p) (L := L)) < 1 := by
  letI := D.integerRingIsDVR
  let pO : D.ringOfIntegers :=
    ⟨pElement (p := p) (L := L), D.p_valuation_lt_one.le⟩
  have h := ((IsDiscreteValuationRing.maximalIdeal D.ringOfIntegers).valuation_lt_one_iff_mem
    (K := L) pO).2 (p_mem_maximalIdeal D)
  change D.discreteValuation (algebraMap D.ringOfIntegers L pO) < 1 at h
  have hpO : algebraMap D.ringOfIntegers L pO = pElement (p := p) (L := L) := rfl
  rwa [hpO] at h

/-- The residue field is finite, as a consequence of spectral compactness. -/
theorem residueFieldFinite : Finite (IsLocalRing.ResidueField D.ringOfIntegers) := by
  rcases D with ⟨valuation, hvaluation, hp⟩
  subst valuation
  exact spectralResidueFieldFinite p L

/-- The constructed ramification index is positive. -/
theorem ramificationIndex_pos : 0 < D.ramificationIndex := by
  have hne : D.discreteValuation (pElement (p := p) (L := L)) ≠ 0 := by
    simp [p_ne_zero (p := p) (L := L)]
  have hlog :
      WithZero.log (D.discreteValuation (pElement (p := p) (L := L))) < 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_lt_log hne one_ne_zero).2 (discreteValuation_p_lt_one D)
  rw [ramificationIndex, Nat.pos_iff_ne_zero]
  intro h
  have hz := Int.toNat_eq_zero.mp h
  omega

/-- The valuation-theoretic and ideal-theoretic ramification indices agree. -/
theorem ramificationIndex_eq_idealRamificationIndex :
    D.ramificationIndex = D.idealRamificationIndex := by
  letI := D.valuationExtension
  letI := D.integerRingIsDVR
  let v : IsDedekindDomain.HeightOneSpectrum (baseValuation p).integer :=
    IsDiscreteValuationRing.maximalIdeal _
  let w : IsDedekindDomain.HeightOneSpectrum D.ringOfIntegers :=
    IsDiscreteValuationRing.maximalIdeal _
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change (IsLocalRing.maximalIdeal D.ringOfIntegers).LiesOver
      (IsLocalRing.maximalIdeal (baseValuation p).integer)
    infer_instance
  have hpBase : pInBaseRing p ≠ 0 := by
    intro h
    have h' := congrArg ((↑) : (baseValuation p).integer → ℚ_[p]) h
    change (p : ℚ_[p]) = 0 at h'
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h'
  have hbaseInt : v.intValuation (pInBaseRing p) = WithZero.exp (-1 : ℤ) := by
    apply v.intValuation_singleton hpBase
    exact base_maximalIdeal_eq_span_p p
  have hbaseVal : v.valuation ℚ_[p] (p : ℚ_[p]) = WithZero.exp (-1 : ℤ) := by
    rw [← hbaseInt, ← v.valuation_of_algebraMap (K := ℚ_[p])]
    rfl
  let eOld : ℕ := v.asIdeal.ramificationIdx' w.asIdeal
  have hlie := v.valuation_liesOver L w (p : ℚ_[p])
  have hw : D.discreteValuation (pElement (p := p) (L := L)) =
      WithZero.exp (-(eOld : ℤ)) := by
    change w.valuation L (algebraMap ℚ_[p] L p) = WithZero.exp (-(eOld : ℤ))
    rw [← hlie, hbaseVal]
    simp only [eOld]
    simp
  have hlog :
      -WithZero.log (D.discreteValuation (pElement (p := p) (L := L))) = (eOld : ℤ) := by
    rw [hw, WithZero.log_exp]
    omega
  have heOld : eOld = D.idealRamificationIndex := by
    dsimp only [eOld, idealRamificationIndex, v, w, ringOfIntegers]
    exact Ideal.ramificationIdx'_eq_ramificationIdx _ _
      (IsDiscreteValuationRing.maximalIdeal (baseValuation p).integer).ne_bot
  rw [ramificationIndex, hlog, Int.toNat_natCast, heOld]

/-- The constructed rational order has the normalization `ord(p) = 1`. -/
theorem normalizedOrder_p :
    D.normalizedOrder (pElement (p := p) (L := L)) = 1 := by
  have hp := p_ne_zero (p := p) (L := L)
  have hne : D.discreteValuation (pElement (p := p) (L := L)) ≠ 0 := by simp [hp]
  have hlog :
      WithZero.log (D.discreteValuation (pElement (p := p) (L := L))) < 0 := by
    rw [← WithZero.log_one]
    exact (WithZero.log_lt_log hne one_ne_zero).2 (discreteValuation_p_lt_one D)
  rw [normalizedOrder, if_neg hp, ramificationIndex]
  have hnonneg :
      0 ≤ -WithZero.log (D.discreteValuation (pElement (p := p) (L := L))) := by omega
  have hcast :
      (((-WithZero.log (D.discreteValuation (pElement (p := p) (L := L)))).toNat : ℕ) : ℚ) =
        ((-WithZero.log (D.discreteValuation (pElement (p := p) (L := L))) : ℤ) : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnonneg
  rw [hcast]
  norm_num [ne_of_lt hlog]

/-- The packaged different is mathlib's Dedekind different ideal. -/
theorem different_eq_differentIdeal :
    letI := D.valuationExtension
    letI := D.integerRingIsDVR
    D.different =
      differentIdeal (baseRingOfIntegers (p := p)) D.ringOfIntegers := by
  rfl

end MixedCharLocalFieldData

/--
Construct mixed-characteristic local-field data for every finite-dimensional
field extension of `ℚ_[p]`. Completeness follows from finite-dimensionality of
the spectral norm, and compactness then supplies the DVR and finite-residue
instances.
-/
noncomputable def mixedCharLocalFieldData_of_finiteExtension :
    MixedCharLocalFieldData p L := by
  letI : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField ℚ_[p] L
  letI : NormedAlgebra ℚ_[p] L := spectralNorm.normedAlgebra ℚ_[p] L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  letI : CompleteSpace L := spectralNorm.completeSpace ℚ_[p] L
  letI : ProperSpace L := FiniteDimensional.proper ℚ_[p] L
  letI : Valued L NNReal := NormedField.toValued
  letI : Valuation.RankOne (Valued.v : Valuation L NNReal) := by
    change Valuation.RankOne (NormedField.valuation (K := L))
    infer_instance
  let vL : Valuation L NNReal := NormedField.valuation
  have hRing : (Valued.integer L : Set L) = Metric.closedBall 0 1 := by
    ext x
    change Valued.v x ≤ 1 ↔ dist x 0 ≤ 1
    change NormedField.valuation x ≤ 1 ↔ dist x 0 ≤ 1
    rw [NormedField.valuation_apply, dist_zero_right]
    exact (NNReal.coe_le_coe (r₁ := ‖x‖₊) (r₂ := 1)).symm
  letI : CompactSpace (Valued.integer L) :=
    isCompact_iff_compactSpace.mp (hRing.symm ▸ isCompact_closedBall 0 1)
  letI : IsDiscreteValuationRing (Valued.integer L) :=
    Valued.integer.isDiscreteValuationRing_of_compactSpace
  have hLocal :=
    compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
      (inferInstance : CompactSpace (Valued.integer L))
  letI : Finite (Valued.ResidueField L) := hLocal.2.2
  letI : (baseValuation p).HasExtension vL := by
    constructor
    intro x y
    simp only [baseValuation, vL, Valuation.comap_apply, NormedField.valuation_apply]
    have hn (z : ℚ_[p]) : ‖algebraMap ℚ_[p] L z‖₊ = ‖z‖₊ := by
      apply NNReal.eq
      simp only [coe_nnnorm]
      rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p], spectralNorm_extends]
    rw [hn x, hn y]
  exact {
    valuation := vL
    valuation_eq_spectral := by rw [spectralValuation]
    valuationExtension := inferInstance
    integerRingIsDVR := inferInstance
    p_valuation_lt_one := by
      change NormedField.valuation (algebraMap ℚ_[p] L p) < 1
      rw [NormedField.valuation_apply]
      apply NNReal.coe_lt_coe.mp
      simp only [coe_nnnorm]
      rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p], spectralNorm_extends, Padic.norm_p]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  }

/-- The upper logarithmic-lattice exponent from Proposition 1.2. -/
noncomputable def aParam (p e : ℕ) : ℝ :=
  if 2 < p then
    ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e
  else 2

/-- The lower logarithmic-lattice exponent from Proposition 1.2. -/
noncomputable def bParam (p e : ℕ) : ℝ :=
  ((⌊Real.log (((p : ℝ) * e) / (p - 1 : ℕ)) / Real.log p⌋ : ℤ) : ℝ) - 1 / e

/-- For `0 < e ≤ p - 2`, the two Proposition 1.2 parameters are `±1/e`. -/
theorem localParameters_eq_of_smallRamification
    (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (he : 0 < e) (hsmall : e ≤ p - 2) :
    aParam p e = 1 / (e : ℝ) ∧ bParam p e = -1 / (e : ℝ) := by
  have ha := Iut4Sec1.nonarchimedeanLogError_eq_zero_of_le p e hp2 he hsmall
  have hpOne : 1 < p := hp.one_lt
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have heOne : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hdenNat : 0 < p - 1 := by omega
  have hden : (0 : ℝ) < (p - 1 : ℕ) := by exact_mod_cast hdenNat
  have hsmallR : (e : ℝ) ≤ (p - 2 : ℕ) := by exact_mod_cast hsmall
  have hsubLt : ((p - 2 : ℕ) : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast (by omega : p - 2 < p - 1)
  let q : ℝ := ((p : ℝ) * e) / (p - 1 : ℕ)
  have hqOne : 1 < q := by
    rw [show q = ((p : ℝ) * e) / (p - 1 : ℕ) by rfl, one_lt_div hden]
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      norm_num [Nat.cast_sub (by omega : 1 ≤ p)]
    rw [hcast]
    nlinarith
  have hqLt : q < p := by
    rw [show q = ((p : ℝ) * e) / (p - 1 : ℕ) by rfl, div_lt_iff₀ hden]
    nlinarith
  have hpPos : (0 : ℝ) < p := by linarith
  have hqPos : 0 < q := hqOne.trans' zero_lt_one
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogq : 0 ≤ Real.log q := (Real.log_pos hqOne).le
  have hlogLt : Real.log q < Real.log p := Real.strictMonoOn_log hqPos hpPos hqLt
  have hfloor : ⌊Real.log q / Real.log p⌋ = (0 : ℤ) := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨div_nonneg hlogq hlogp.le, (div_lt_one hlogp).2 hlogLt⟩
  constructor
  · rw [aParam, if_pos hp2]
    unfold Iut4Sec1.nonarchimedeanLogError at ha
    linarith
  · rw [bParam, show ((p : ℝ) * e) / (p - 1 : ℕ) = q by rfl, hfloor]
    rw [div_eq_mul_inv]
    ring

namespace RamifiedQuadraticExample

open Polynomial

/-- The Eisenstein polynomial `X² - 2` over `ℚ_[2]`. -/
noncomputable def polynomial : ℚ_[2][X] := X ^ 2 - C 2

private theorem two_not_square (x : ℚ_[2]) : x ^ 2 ≠ 2 := by
  intro h
  have hv := congrArg Padic.valuation h
  rw [Padic.valuation_pow] at hv
  have hv' : (2 : ℤ) * x.valuation = 1 :=
    hv.trans (Padic.valuation_p (p := 2))
  omega

private theorem polynomial_irreducible : Irreducible polynomial := by
  exact X_pow_sub_C_irreducible_of_prime Nat.prime_two two_not_square

noncomputable instance : Fact (Irreducible polynomial) := ⟨polynomial_irreducible⟩

/-- The degree-two extension `ℚ_[2](√2)`. -/
abbrev Extension := AdjoinRoot polynomial

noncomputable instance : Module.Finite ℚ_[2] Extension := by
  exact (show (polynomial : ℚ_[2][X]).Monic by
    rw [polynomial]
    exact monic_X_pow_sub_C (2 : ℚ_[2]) (by norm_num)).finite_adjoinRoot

private theorem finrank_extension : Module.finrank ℚ_[2] Extension = 2 := by
  let pb := AdjoinRoot.powerBasis' (show (polynomial : ℚ_[2][X]).Monic by
    rw [polynomial]
    exact monic_X_pow_sub_C (2 : ℚ_[2]) (by norm_num))
  rw [pb.finrank]
  change polynomial.natDegree = 2
  rw [polynomial, natDegree_X_pow_sub_C]

/-- Constructed local-field data for the ramified quadratic example. -/
noncomputable def data : MixedCharLocalFieldData 2 Extension :=
  mixedCharLocalFieldData_of_finiteExtension 2 Extension

/--
The quadratic example has degree two and its integer ring, normalized order,
ramification index, and different evaluate to the canonical constructions.
-/
theorem ramifiedQuadratic_evaluation :
    Module.finrank ℚ_[2] Extension = 2 ∧
      (data.ringOfIntegers : Set Extension) = {x | data.valuation x ≤ 1} ∧
      data.normalizedOrder
          (MixedCharLocalFieldData.pElement (p := 2) (L := Extension)) = 1 ∧
      0 < data.ramificationIndex ∧
      data.ramificationIndex = data.idealRamificationIndex ∧
      (letI := data.valuationExtension
       letI := data.integerRingIsDVR
       data.different =
         differentIdeal (MixedCharLocalFieldData.baseRingOfIntegers (p := 2))
           data.ringOfIntegers) := by
  refine ⟨finrank_extension, rfl, MixedCharLocalFieldData.normalizedOrder_p data,
    MixedCharLocalFieldData.ramificationIndex_pos data,
    MixedCharLocalFieldData.ramificationIndex_eq_idealRamificationIndex data, ?_⟩
  exact MixedCharLocalFieldData.different_eq_differentIdeal data

end RamifiedQuadraticExample

end Iut4Sec1
