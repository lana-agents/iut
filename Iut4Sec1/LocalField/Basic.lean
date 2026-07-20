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
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.Algebra.Polynomial.Lifts
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
from Proposition 1.2 and computes the integer ring, ramification, normalized
orders, and different of the extension `ℚ_[2](√2)`.
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

/-- Membership in the spectral integer ring is equivalent to integrality over the base
spectral integer ring. -/
theorem mem_ringOfIntegers_iff_isIntegral (x : L) : x ∈ D.ringOfIntegers ↔
    IsIntegral (baseRingOfIntegers (p := p)) x := by
  letI : Algebra.IsAlgebraic ℚ_[p] L := Algebra.IsAlgebraic.of_finite ℚ_[p] L
  letI : NontriviallyNormedField L := spectralNorm.nontriviallyNormedField ℚ_[p] L
  letI : NormedAlgebra ℚ_[p] L := spectralNorm.normedAlgebra ℚ_[p] L
  letI : IsUltrametricDist L := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  constructor
  · intro hx
    change D.valuation x ≤ 1 at hx
    rw [D.valuation_eq_spectral, spectralValuation, NormedField.valuation_apply] at hx
    have hs : spectralNorm ℚ_[p] L x ≤ 1 := by exact_mod_cast hx
    have hc : ∀ n, ‖(minpoly ℚ_[p] x).coeff n‖ ≤ 1 :=
      (spectralValue_le_one_iff
        (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)).mp hs
    have hlifts : minpoly ℚ_[p] x ∈
        Polynomial.lifts (algebraMap (baseRingOfIntegers (p := p)) ℚ_[p]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨(minpoly ℚ_[p] x).coeff n, by
        change baseValuation p ((minpoly ℚ_[p] x).coeff n) ≤ 1
        rw [baseValuation, NormedField.valuation_apply]
        exact_mod_cast hc n⟩, rfl⟩
    obtain ⟨q, hqmap, -, hqmonic⟩ :=
      Polynomial.lifts_and_natDegree_eq_and_monic hlifts
        (minpoly.monic (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
    refine ⟨q, hqmonic, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[p] x q,
      hqmap, minpoly.aeval]
  · rintro ⟨q, hqmonic, hqx⟩
    have hroot : Polynomial.aeval x
        (q.map (algebraMap (baseRingOfIntegers (p := p)) ℚ_[p])) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      exact hqx
    have hcoeff : ∀ n,
        ‖(q.map (algebraMap (baseRingOfIntegers (p := p)) ℚ_[p])).coeff n‖ ≤ 1 := by
      intro n
      rw [Polynomial.coeff_map]
      change ‖((q.coeff n : baseRingOfIntegers (p := p)) : ℚ_[p])‖ ≤ 1
      exact_mod_cast q.coeff n |>.2
    have hsvalue : spectralValue
        (q.map (algebraMap (baseRingOfIntegers (p := p)) ℚ_[p])) ≤ 1 :=
      (spectralValue_le_one_iff (hqmonic.map _)).mpr hcoeff
    have hs : spectralNorm ℚ_[p] L x ≤ 1 :=
      (norm_root_le_spectralValue (f := spectralAlgNorm ℚ_[p] L)
        isPowMul_spectralNorm isNonarchimedean_spectralNorm
        (hqmonic.map _) hroot).trans hsvalue
    change D.valuation x ≤ 1
    rw [D.valuation_eq_spectral, spectralValuation, NormedField.valuation_apply]
    exact_mod_cast hs

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

/-- The spectral integer ring of `ℚ_[2]`. -/
abbrev BaseIntegers := MixedCharLocalFieldData.baseRingOfIntegers (p := 2)

/-- The spectral integer ring of the quadratic extension. -/
abbrev RingOfIntegers := data.ringOfIntegers

local instance : (baseValuation 2).HasExtension data.valuation :=
  data.valuationExtension

local instance : IsScalarTower BaseIntegers RingOfIntegers Extension := ⟨fun _ _ _ => by
  simp only [Algebra.smul_def, map_mul, mul_assoc]
  rfl⟩

private noncomputable def baseTwo : BaseIntegers := pInBaseRing 2

/-- The distinguished square root of `2`. -/
noncomputable def root : Extension := AdjoinRoot.root polynomial

private theorem root_sq : root ^ 2 =
    MixedCharLocalFieldData.pElement (p := 2) (L := Extension) := by
  have h := AdjoinRoot.eval₂_root polynomial
  rw [polynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

private noncomputable def integerPolynomial : BaseIntegers[X] := X ^ 2 - C baseTwo

private theorem root_integral : IsIntegral BaseIntegers root := by
  refine ⟨integerPolynomial, ?_, ?_⟩
  · rw [integerPolynomial]
    exact monic_X_pow_sub_C baseTwo (by norm_num)
  · rw [integerPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change root ^ 2 -
      MixedCharLocalFieldData.pElement (p := 2) (L := Extension) = 0
    rw [root_sq, sub_self]

/-- The distinguished square root as an algebraic integer. -/
noncomputable def rootInt : RingOfIntegers :=
  ⟨root, (MixedCharLocalFieldData.mem_ringOfIntegers_iff_isIntegral data root).2 root_integral⟩

private theorem base_maximalIdeal_eq_span_two :
    IsLocalRing.maximalIdeal BaseIntegers =
      Ideal.span ({baseTwo} : Set BaseIntegers) := by
  simpa only [baseTwo] using base_maximalIdeal_eq_span_p 2

private theorem baseTwo_prime : Prime baseTwo := by
  apply (Ideal.span_singleton_prime (show baseTwo ≠ 0 by
    intro h
    have h' := congrArg ((↑) : BaseIntegers → ℚ_[2]) h
    norm_num [baseTwo, pInBaseRing] at h')).mp
  rw [← base_maximalIdeal_eq_span_two]
  exact (IsLocalRing.maximalIdeal.isMaximal BaseIntegers).isPrime

private theorem minpoly_root_base : minpoly BaseIntegers root = integerPolynomial := by
  apply Polynomial.map_injective (algebraMap BaseIntegers ℚ_[2])
    (IsFractionRing.injective BaseIntegers ℚ_[2])
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[2] root_integral,
    root, AdjoinRoot.minpoly_root]
  · simp [polynomial, integerPolynomial]
    rfl
  · rw [polynomial]
    exact (monic_X_pow_sub_C (2 : ℚ_[2]) (by norm_num)).ne_zero

private theorem integerPolynomial_eisenstein :
    integerPolynomial.IsEisensteinAt
      (Ideal.span ({baseTwo} : Set BaseIntegers)) := by
  refine (show integerPolynomial.Monic by
      rw [integerPolynomial]
      exact monic_X_pow_sub_C baseTwo (by norm_num)).isEisensteinAt_of_mem_of_notMem
    (Ideal.IsPrime.ne_top (Ideal.isPrime_span_singleton_of_prime baseTwo_prime)) ?_ ?_
  · intro i hi
    rw [integerPolynomial, natDegree_X_pow_sub_C] at hi
    interval_cases i <;> simp [integerPolynomial]
  · rw [integerPolynomial, coeff_sub, coeff_X_pow, coeff_C_zero, if_neg (by norm_num),
      zero_sub, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdiv
    have hunit : IsUnit baseTwo := by
      obtain ⟨c, hc⟩ := hdiv
      have hc' : (-1 : BaseIntegers) = baseTwo * c := by
        apply mul_left_cancel₀ baseTwo_prime.ne_zero
        simpa [pow_two, mul_assoc] using hc
      exact isUnit_iff_dvd_one.mpr ⟨-c, by rw [mul_neg, ← hc']; simp⟩
    exact baseTwo_prime.not_unit hunit

private theorem polynomial_monic : polynomial.Monic := by
  rw [polynomial]
  exact monic_X_pow_sub_C (2 : ℚ_[2]) (by norm_num)

private noncomputable def powerBasis : PowerBasis ℚ_[2] Extension :=
  AdjoinRoot.powerBasis' polynomial_monic

private theorem powerBasis_gen : powerBasis.gen = root := rfl

private theorem powerBasis_dim : powerBasis.dim = 2 := by
  rw [powerBasis, AdjoinRoot.powerBasis'_dim, polynomial, natDegree_X_pow_sub_C]

private theorem powerBasis_discr : Algebra.discr ℚ_[2] powerBasis.basis = 8 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [show Module.finrank ℚ_[2] Extension = 2 by
    rw [powerBasis.finrank, powerBasis_dim]]
  norm_num [powerBasis_gen, root, AdjoinRoot.minpoly_root polynomial_monic.ne_zero,
    polynomial]
  change -((Algebra.norm ℚ_[2]) (algebraMap ℚ_[2] Extension 2) *
    (Algebra.norm ℚ_[2]) root) = 8
  rw [Algebra.norm_algebraMap]
  rw [show Module.finrank ℚ_[2] Extension = 2 by
    rw [powerBasis.finrank, powerBasis_dim]]
  rw [← powerBasis_gen, Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
  norm_num [powerBasis_gen, powerBasis_dim, root,
    AdjoinRoot.minpoly_root polynomial_monic.ne_zero, polynomial]

private noncomputable def integerSubalgebra : Subalgebra BaseIntegers Extension :=
  (IsScalarTower.toAlgHom BaseIntegers RingOfIntegers Extension).range

private theorem mem_integerSubalgebra_iff (x : Extension) :
    x ∈ integerSubalgebra ↔ x ∈ data.ringOfIntegers := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem integerSubalgebra_eq_adjoin :
    integerSubalgebra =
      Algebra.adjoin BaseIntegers ({root} : Set Extension) := by
  apply le_antisymm
  · intro x hx
    have hxint : IsIntegral BaseIntegers x :=
      (MixedCharLocalFieldData.mem_ringOfIntegers_iff_isIntegral data x).1
        ((mem_integerSubalgebra_iff x).1 hx)
    have hdiscr := Algebra.discr_mul_isIntegral_mem_adjoin ℚ_[2]
      (B := powerBasis) (powerBasis_gen ▸ root_integral) hxint
    rw [powerBasis_discr] at hdiscr
    have hp3 : baseTwo ^ 3 • x ∈
        Algebra.adjoin BaseIntegers ({powerBasis.gen} : Set Extension) := by
      simp only [Algebra.smul_def] at hdiscr ⊢
      convert hdiscr using 1
      change algebraMap BaseIntegers Extension (baseTwo ^ 3) * x =
        algebraMap ℚ_[2] Extension 8 * x
      congr 1
    have heis : (minpoly BaseIntegers powerBasis.gen).IsEisensteinAt
        (Ideal.span ({baseTwo} : Set BaseIntegers)) := by
      rw [powerBasis_gen, minpoly_root_base]
      exact integerPolynomial_eisenstein
    simpa only [powerBasis_gen] using
      (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
        (B := powerBasis) (p := baseTwo) (n := 3) baseTwo_prime
        (powerBasis_gen ▸ root_integral) hxint hp3 heis)
  · apply Algebra.adjoin_le
    rintro x (rfl : x = root)
    exact (mem_integerSubalgebra_iff root).2 rootInt.2

private theorem ringOfIntegers_coe_eq_adjoin :
    (data.ringOfIntegers : Set Extension) =
      Algebra.adjoin BaseIntegers ({root} : Set Extension) := by
  ext x
  change x ∈ data.ringOfIntegers ↔
    x ∈ Algebra.adjoin BaseIntegers ({root} : Set Extension)
  rw [← mem_integerSubalgebra_iff, integerSubalgebra_eq_adjoin]

private theorem ringOfIntegers_eq_adjoin :
    Algebra.adjoin BaseIntegers ({rootInt} : Set RingOfIntegers) = ⊤ := by
  let f : RingOfIntegers →ₐ[BaseIntegers] Extension :=
    IsScalarTower.toAlgHom BaseIntegers RingOfIntegers Extension
  apply (Subalgebra.map_injective (f := f) Subtype.val_injective)
  rw [Algebra.map_top]
  rw [AlgHom.map_adjoin, Set.image_singleton]
  change Algebra.adjoin BaseIntegers ({root} : Set Extension) = f.range
  exact integerSubalgebra_eq_adjoin.symm

private theorem rootInt_integral : IsIntegral BaseIntegers rootInt := by
  let f : RingOfIntegers →ₐ[BaseIntegers] Extension :=
    IsScalarTower.toAlgHom BaseIntegers RingOfIntegers Extension
  rw [← isIntegral_algHom_iff f Subtype.val_injective]
  exact root_integral

private noncomputable instance : Module.Finite BaseIntegers RingOfIntegers := by
  rw [Module.finite_def, ← Algebra.top_toSubmodule, ← ringOfIntegers_eq_adjoin]
  exact rootInt_integral.fg_adjoin_singleton

private theorem ramification_mul_residue :
    data.ramificationIndex * data.residueDegree = 2 := by
  letI := data.integerRingIsDVR
  have h := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    RingOfIntegers ℚ_[2] Extension
      (IsDiscreteValuationRing.not_a_field BaseIntegers)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal BaseIntegers)
      (IsLocalRing.maximalIdeal RingOfIntegers)
      (IsDiscreteValuationRing.not_a_field BaseIntegers),
    Ideal.inertiaDeg'_eq_inertiaDeg] at h
  rw [MixedCharLocalFieldData.ramificationIndex_eq_idealRamificationIndex data]
  simpa only [MixedCharLocalFieldData.idealRamificationIndex,
    MixedCharLocalFieldData.residueDegree,
    show Module.finrank ℚ_[2] Extension = 2 by
      rw [powerBasis.finrank, powerBasis_dim]] using h

private theorem root_ne_zero : root ≠ 0 := by
  intro h
  have hp := root_sq
  rw [h, zero_pow (by norm_num : 2 ≠ 0)] at hp
  exact (map_ne_zero (algebraMap ℚ_[2] Extension)).2 (by norm_num) hp.symm

private theorem neg_log_p_eq_ramificationIndex :
    -WithZero.log (data.discreteValuation
      (MixedCharLocalFieldData.pElement (p := 2) (L := Extension))) =
        (data.ramificationIndex : ℤ) := by
  have hpos := MixedCharLocalFieldData.ramificationIndex_pos data
  rw [MixedCharLocalFieldData.ramificationIndex] at hpos ⊢
  have hz : 0 ≤ -WithZero.log (data.discreteValuation
      (MixedCharLocalFieldData.pElement (p := 2) (L := Extension))) := by
    omega
  exact (Int.toNat_of_nonneg hz).symm

private theorem twice_neg_log_root_eq_ramificationIndex :
    2 * (-WithZero.log (data.discreteValuation root)) =
      (data.ramificationIndex : ℤ) := by
  have hv := congrArg data.discreteValuation root_sq
  rw [map_pow] at hv
  have hlog := congrArg WithZero.log hv
  rw [WithZero.log_pow, nsmul_eq_mul] at hlog
  rw [← neg_log_p_eq_ramificationIndex]
  omega

private theorem ramificationIndex_eq_two : data.ramificationIndex = 2 := by
  have hpos := MixedCharLocalFieldData.ramificationIndex_pos data
  have heven := twice_neg_log_root_eq_ramificationIndex
  have hef := ramification_mul_residue
  have hediv : data.ramificationIndex ∣ 2 :=
    ⟨data.residueDegree, hef.symm⟩
  have hele : data.ramificationIndex ≤ 2 := Nat.le_of_dvd (by norm_num) hediv
  omega

private theorem residueDegree_eq_one : data.residueDegree = 1 := by
  have hef := ramification_mul_residue
  rw [ramificationIndex_eq_two] at hef
  omega

private theorem neg_log_root_eq_one :
    -WithZero.log (data.discreteValuation root) = 1 := by
  have h := twice_neg_log_root_eq_ramificationIndex
  rw [ramificationIndex_eq_two] at h
  omega

private theorem normalizedOrder_root : data.normalizedOrder root = (1 / 2 : ℚ) := by
  rw [MixedCharLocalFieldData.normalizedOrder, if_neg root_ne_zero,
    ramificationIndex_eq_two, neg_log_root_eq_one]
  norm_num

private theorem minpoly_rootInt : minpoly BaseIntegers rootInt = integerPolynomial := by
  apply Polynomial.map_injective (algebraMap BaseIntegers ℚ_[2])
    (IsFractionRing.injective BaseIntegers ℚ_[2])
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ_[2] Extension rootInt_integral]
  change minpoly ℚ_[2] root = integerPolynomial.map (algebraMap BaseIntegers ℚ_[2])
  rw [root, AdjoinRoot.minpoly_root polynomial_monic.ne_zero]
  simp [polynomial, integerPolynomial]
  rfl

/-- The generator `2√2` of the quadratic different. -/
noncomputable def differentGenerator : RingOfIntegers :=
  algebraMap BaseIntegers RingOfIntegers baseTwo * rootInt

private theorem field_eq_adjoin_root :
    Algebra.adjoin ℚ_[2]
      ({algebraMap RingOfIntegers Extension rootInt} : Set Extension) = ⊤ := by
  change Algebra.adjoin ℚ_[2] ({root} : Set Extension) = ⊤
  simpa only [powerBasis_gen] using powerBasis.adjoin_gen_eq_top

private theorem different_eq_span_generator :
    data.different = Ideal.span ({differentGenerator} : Set RingOfIntegers) := by
  letI := data.integerRingIsDVR
  have h := conductor_mul_differentIdeal BaseIntegers ℚ_[2] Extension rootInt
    field_eq_adjoin_root
  rw [conductor_eq_top_of_adjoin_eq_top ringOfIntegers_eq_adjoin, Ideal.top_mul] at h
  have htwo : (1 : Extension) + 1 =
      algebraMap ℚ_[2] Extension (baseTwo : ℚ_[2]) := by
    rw [← map_one (algebraMap ℚ_[2] Extension), ← map_add]
    congr 1
    change (1 : ℚ_[2]) + 1 = 2
    norm_num
  change differentIdeal BaseIntegers RingOfIntegers =
    Ideal.span ({differentGenerator} : Set RingOfIntegers)
  rw [h]
  congr 2
  ext
  simpa [differentGenerator, minpoly_rootInt, integerPolynomial] using
    (Or.inl htwo : (1 : Extension) + 1 =
      algebraMap ℚ_[2] Extension (baseTwo : ℚ_[2]) ∨ rootInt = 0)

private theorem differentGenerator_ne_zero : differentGenerator ≠ 0 := by
  rw [differentGenerator, mul_ne_zero_iff]
  exact ⟨by
    simpa using (FaithfulSMul.algebraMap_injective BaseIntegers RingOfIntegers).ne
      baseTwo_prime.ne_zero,
    fun h => root_ne_zero (congrArg ((↑) : RingOfIntegers → Extension) h)⟩

private theorem neg_log_differentGenerator_eq_three :
    -WithZero.log (data.discreteValuation
      (algebraMap RingOfIntegers Extension differentGenerator)) = 3 := by
  have hpne : data.discreteValuation
      (MixedCharLocalFieldData.pElement (p := 2) (L := Extension)) ≠ 0 := by
    simp [MixedCharLocalFieldData.pElement]
  have hrne : data.discreteValuation root ≠ 0 := by simp [root_ne_zero]
  have hval : algebraMap RingOfIntegers Extension differentGenerator =
      MixedCharLocalFieldData.pElement (p := 2) (L := Extension) * root := by
    rfl
  rw [hval, map_mul, WithZero.log_mul hpne hrne]
  have hp := neg_log_p_eq_ramificationIndex
  have hr := neg_log_root_eq_one
  rw [ramificationIndex_eq_two] at hp
  omega

private theorem normalizedOrder_differentGenerator :
    data.normalizedOrder
      (algebraMap RingOfIntegers Extension differentGenerator) = (3 / 2 : ℚ) := by
  have hne : algebraMap RingOfIntegers Extension differentGenerator ≠ 0 := by
    intro h
    apply differentGenerator_ne_zero
    apply Subtype.ext
    exact h
  rw [MixedCharLocalFieldData.normalizedOrder, if_neg hne,
    ramificationIndex_eq_two, neg_log_differentGenerator_eq_three]
  norm_num

private theorem discreteValuation_root_eq_exp_neg_one :
    data.discreteValuation root = WithZero.exp (-1 : ℤ) := by
  have hne : data.discreteValuation root ≠ 0 := by simp [root_ne_zero]
  rw [← WithZero.exp_log hne]
  congr
  have h := neg_log_root_eq_one
  omega

private theorem rootInt_irreducible : Irreducible rootInt := by
  letI := data.integerRingIsDVR
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible RingOfIntegers
  have hπval :
      (IsDiscreteValuationRing.maximalIdeal RingOfIntegers).valuation Extension
        (algebraMap RingOfIntegers Extension π) = WithZero.exp (-1 : ℤ) := by
    calc
      _ = (IsDiscreteValuationRing.maximalIdeal RingOfIntegers).intValuation π :=
        (IsDiscreteValuationRing.maximalIdeal RingOfIntegers).valuation_of_algebraMap π
      _ = WithZero.exp (-1 : ℤ) :=
        (IsDiscreteValuationRing.maximalIdeal RingOfIntegers).intValuation_singleton
          hπ.ne_zero hπ.maximalIdeal_eq
  have hrval :
      (IsDiscreteValuationRing.maximalIdeal RingOfIntegers).valuation Extension
        (algebraMap RingOfIntegers Extension rootInt) = WithZero.exp (-1 : ℤ) := by
    exact discreteValuation_root_eq_exp_neg_one
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_valuation_eq
    (A := RingOfIntegers) (K := Extension)
      (algebraMap RingOfIntegers Extension rootInt)
      (algebraMap RingOfIntegers Extension π) (hrval.trans hπval.symm)
  have huO : (u : RingOfIntegers) * rootInt = π := by
    apply Subtype.ext
    change algebraMap RingOfIntegers Extension ((u : RingOfIntegers) * rootInt) =
      algebraMap RingOfIntegers Extension π
    rw [map_mul]
    simpa only [Algebra.smul_def, Units.smul_def] using hu
  have hassoc : Associated rootInt π := ⟨u, by simpa [mul_comm] using huO⟩
  exact hassoc.symm.irreducible hπ

private theorem maximalIdeal_eq_span_root :
    data.maximalIdeal = Ideal.span ({rootInt} : Set RingOfIntegers) := by
  letI := data.integerRingIsDVR
  exact rootInt_irreducible.maximalIdeal_eq

private theorem rootInt_sq :
    rootInt ^ 2 = algebraMap BaseIntegers RingOfIntegers baseTwo := by
  apply Subtype.ext
  exact root_sq

private theorem different_eq_maximalIdeal_pow_three :
    data.different = data.maximalIdeal ^ 3 := by
  rw [different_eq_span_generator, maximalIdeal_eq_span_root,
    Ideal.span_singleton_pow]
  congr 2
  ext
  rw [differentGenerator, ← rootInt_sq]
  ring_nf

/--
For `ℚ_[2](√2)`, the spectral integer ring is `ℤ_[2][√2]`, the extension is
totally ramified with `e = 2` and `f = 1`, `ord(√2) = 1/2`, and the different
is `(2√2) = 𝔪^3`; its normalized different order is `3/2`.
-/
theorem ramifiedQuadratic_evaluation :
    Module.finrank ℚ_[2] Extension = 2 ∧
      (data.ringOfIntegers : Set Extension) =
        Algebra.adjoin BaseIntegers ({root} : Set Extension) ∧
      data.ramificationIndex = 2 ∧
      data.residueDegree = 1 ∧
      data.normalizedOrder root = (1 / 2 : ℚ) ∧
      data.different = Ideal.span ({differentGenerator} : Set RingOfIntegers) ∧
      data.different = data.maximalIdeal ^ 3 ∧
      data.normalizedOrder
        (algebraMap RingOfIntegers Extension differentGenerator) = (3 / 2 : ℚ) := by
  exact ⟨finrank_extension, ringOfIntegers_coe_eq_adjoin,
    ramificationIndex_eq_two, residueDegree_eq_one, normalizedOrder_root,
    different_eq_span_generator, different_eq_maximalIdeal_pow_three,
    normalizedOrder_differentGenerator⟩

end RamifiedQuadraticExample

end Iut4Sec1
