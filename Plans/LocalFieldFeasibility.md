# P5 local-field feasibility report

Date: 2026-07-19

## Verdict

| Item | Verdict | Reason |
|---|---|---|
| Finite complete normed extension of `ℚ_[p]` | **GO** | The spectral-norm API constructs compatible nontrivially normed-field and normed-algebra structures from a finite field extension, and supplies completeness. |
| Valuation ring, normalized order, ramification/residue data, and different | **GO** | The compact spectral integer ring yields a DVR and finite residue field. For its canonical discrete field valuation `w`, the probe constructs `e = (-log(w(p))).toNat`, proves `0 < e`, defines the rational order with zero sent to `⊤`, and proves `ord(p) = 1`. Inertia, the ideal-theoretic ramification expression, and the different also elaborate. |
| Finite tensor over `ℤ_[p]`, reduction, total quotient ring, normalization | **GO** | `PiTensorProduct`, quotient by `nilradical`, localization at `nonZeroDivisors`, and `integralClosure` compose at the type/instance level. |
| Log/exp convergence ball | **GO** | For every prime `p`, every arbitrary finite-dimensional `L/ℚ_[p]`, and the transported spectral norm, the probe proves `Summable` for log on `‖x‖ < 1` and exp on `‖x‖ < ‖p‖`; the proof includes `p = 2`. |
| Haar measure normalized on the integer ring | **GO** | Finite dimensionality gives properness; the integer ring is the compact closed unit ball with nonempty interior, so `addHaarMeasure` normalizes it to mass one. |

**Overall P5 implementer verdict after review correction: GO, pending round-2
review.** All five items now have elaborated constructions. In particular, the
item 2 probe returns a discrete valuation, positive normalization exponent, and
normalized order together with `ord(p) = 1`, while item 4 proves both requested
`Summable` statements for arbitrary finite extensions and all primes. No caller
hypothesis carries either conclusion. This remains a feasibility verdict, not a
proof of P6--P11; P6 was not started and remains forbidden until review accepts
this correction.

All probe sources are ignored files below `.pi/probes/`; none is imported by the
project or tracked by Git.

## 1. Finite complete normed extension of `ℚ_[p]` — GO

Probe: `.pi/probes/P5FiniteExtension.lean`.

### Imports tried

```lean
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.ProperSpace
```

### Declarations tried

* `Algebra.IsAlgebraic.of_finite`
* `spectralNorm.normedField`
* `spectralNorm.nontriviallyNormedField` (also used by the item 2 probe)
* `spectralNorm.normedAlgebra`
* `spectralNorm.completeSpace`
* `FiniteDimensional.proper`

The probe starts only with

```lean
[Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
```

and installs the spectral structures. `CompleteSpace L` and
`NormedAlgebra ℚ_[p] L` are then synthesized. Completeness is therefore derived,
not an input field of a project structure.

### Minimal errors

No remaining error. An early local-instance form made `p` inaccessible from the
result type of a `NormedField L` instance; moving the spectral instances inside
the prototype example removed that elaboration-order issue without changing the
representation.

### Proposed representation

P6 should quantify an algebraic field extension by the three assumptions above,
then locally install:

```lean
Algebra.IsAlgebraic.of_finite ℚ_[p] L
spectralNorm.nontriviallyNormedField ℚ_[p] L
spectralNorm.normedAlgebra ℚ_[p] L
spectralNorm.completeSpace ℚ_[p] L
```

This supplies a canonical construction from the algebraic extension data and
avoids asking callers for a separately chosen norm or completeness proof.

## 2. Valuation ring, normalized order, `e`, `f`, and different — GO (strengthened after review)

Probe: `.pi/probes/P5ValuationData.lean`.

### Imports tried

```lean
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.NormedValued
```

### Declarations tried

* `NormedField.valuation`, `NormedField.toValued`
* `Valuation.valuationSubring`
* `FiniteDimensional.proper`
* `Valued.integer.isDiscreteValuationRing_of_compactSpace`
* `Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`
* `Valuation.HasExtension` and its induced valuation-integer algebra
* `Ideal.ramificationIdx`, `Ideal.inertiaDeg`
* `differentIdeal`
* `IsDiscreteValuationRing.addVal`
* `IsDiscreteValuationRing.maximalIdeal`, `IsDiscreteValuationRing.isRankOneDiscrete`
* `IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem`
* `WithZero.log_lt_log`, `Int.toNat_of_nonneg`
* `IsDedekindDomain.HeightOneSpectrum.valuation_liesOver`
* `Ideal.ramificationIdx'_eq_ramificationIdx`

The probe proves that `Valued.integer L` is the closed unit ball, installs its
`CompactSpace` instance, derives `IsDiscreteValuationRing (Valued.integer L)`
and `Finite (Valued.ResidueField L)`, and constructs a
`NormedField.valuation` extension instance by proving equality of spectral norms
on the base field. With that extension in scope, the following expressions
elaborate:

```lean
(IsLocalRing.maximalIdeal vL.integer).ramificationIdx vK.integer
(IsLocalRing.maximalIdeal vL.integer).inertiaDeg vK.integer
differentIdeal vK.integer vL.integer
```

The correction probe then takes the height-one maximal ideal of the DVR and its
canonical discrete field valuation

```lean
w : IsDedekindDomain.HeightOneSpectrum vL.integer
wv : Valuation L ℤᵐ⁰ := w.valuation L
```

and proves an existential result returning `wv`, `e : ℕ`, and
`ord : L → WithTop ℚ`. It derives `wv (algebraMap ℚ_[p] L p) < 1` from
`‖algebraMap ℚ_[p] L p‖ = p⁻¹ < 1`, sets
`e = (-WithZero.log (wv (algebraMap ℚ_[p] L p))).toNat`, proves `0 < e`, sends
zero to `⊤`, and divides the nonzero integer exponent by `e`. The returned
result proves

```lean
ord (algebraMap ℚ_[p] L p) = 1
```

without an assumption containing that equality or the positivity conclusion.

### Minimal errors

The first direct attempt ended at:

```text
failed to synthesize instance of type class
  IsDiscreteValuationRing O
```

This was not treated as a caller hypothesis. The resolved route derives
properness from `FiniteDimensional.proper`, compactness of the closed unit ball,
and then the DVR and finite-residue instances from the valued locally compact
API. No unresolved error remains.

### Proposed representation

Let `vK` and `vL` be the norm valuations on `ℚ_[p]` and `L`, and let
`OK := vK.integer`, `OL := vL.integer`. The spectral restriction theorem proves
`vK.HasExtension vL`. Use the canonical discrete valuation

```lean
wv := (IsDiscreteValuationRing.maximalIdeal OL).valuation L
```

and define `e` to be the positive integer exponent of the image of `p` under
`wv`. Define `ord 0 = ⊤`; for nonzero `x`, convert `wv x` to its additive integer
exponent with `-WithZero.log` and divide by `e`. This is the representation
actually constructed by the strengthened probe and it yields `ord(p) = 1` by
reduction, after proving positivity of `e` from the strict norm inequality.
Define `f` as `(IsLocalRing.maximalIdeal OL).inertiaDeg OK` and the local
different as `differentIdeal OK OL`.

The alternate ideal-theoretic expression
`(IsLocalRing.maximalIdeal OL).ramificationIdx OK` also elaborates. P6 should
prove its compatibility with the valuation-theoretic `e` before using lemmas
stated with that expression; `valuation_liesOver` and
`ramificationIdx'_eq_ramificationIdx` remain the identified bridge. This
compatibility is not stored as caller data and is not claimed as a P5 theorem.

## 3. Finite tensor, reduction, total quotient ring, normalization — GO

Probe: `.pi/probes/P5TensorNormalization.lean`.

### Imports tried

```lean
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.PiTensorProduct
```

### Declarations tried

* `PiTensorProduct`, `PiTensorProduct.tprod`
* `nilradical` and ideal quotient notation
* `nonZeroDivisors`
* `Localization`
* `integralClosure`

For a finite index type `ι` and a family of `ℤ_[p]`-algebras `A i`, the probe
instantiates all four commutative rings:

```lean
PiTensorProduct ℤ_[p] A
(PiTensorProduct ℤ_[p] A) ⧸ nilradical (PiTensorProduct ℤ_[p] A)
Localization (nonZeroDivisors <reduced tensor>)
integralClosure <reduced tensor> <total quotient ring>
```

### Minimal errors

The binder notation with `ℤ_[p]` nested inside the tensor notation produced the
parser message `expected token`. Using the declaration directly as
`PiTensorProduct ℤ_[p] A` elaborates and preserves the intended object. No
algebraic instance error remains.

### Proposed representation

Use `PiTensorProduct ℤ_[p] (fun i => OL i)` for the finite tensor of integer
rings. Define the reduction by quotienting its nilradical, its total quotient
ring by localizing at all non-zero-divisors, and its normalization as the
integral closure of the reduced tensor in that localization. P8 must still prove
the finiteness, product decomposition, and different inclusions needed by
Proposition 1.1; P5 only confirms that the objects themselves compose honestly.

## 4. Log/exp convergence ball — GO (strengthened after review)

Probe: `.pi/probes/P5LogExp.lean`.

### Imports tried

```lean
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
```

### Declarations tried

* `Algebra.IsAlgebraic.of_finite`
* `spectralNorm.nontriviallyNormedField`, `spectralNorm.normedAlgebra`,
  `spectralNorm.completeSpace`, `spectralNorm_extends`
* `Padic.norm_eq_zpow_neg_valuation`, `Padic.valuation_natCast`, `Padic.norm_p`
* `pow_padicValNat_dvd`, `padicValNat_factorial_le`
* `summable_pow_mul_geometric_of_norm_lt_one`,
  `summable_geometric_of_norm_lt_one`
* `Summable.of_nonneg_of_le`, `Summable.of_norm`

The strengthened probe quantifies an arbitrary prime `p` and arbitrary

```lean
[Field L] [Algebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
```

installs the spectral norm and completeness, and proves the conjunction of the
two actual convergence statements:

```lean
∀ x : L, ‖x‖ < 1 → Summable (fun n => logTerm L n x)
∀ x : L, ‖x‖ < ‖algebraMap ℚ_[p] L p‖ →
  Summable (fun n => x ^ n / n.factorial)
```

### Proof route and ball

`spectralNorm_extends` first proves that every natural-number coefficient has
the same norm in `L` as in `ℚ_[p]`. For log, `pow_padicValNat_dvd` bounds
`‖(n+1)⁻¹‖` by `n+1`; the norm of the `n`th term is therefore dominated by
`(n+1) * ‖x‖^(n+1)`, whose summability follows from
`summable_pow_mul_geometric_of_norm_lt_one`.

For exp, `padicValNat_factorial_le` bounds `‖(n!)⁻¹‖` by `p^n`. Hence the term
norm is dominated by `(p * ‖x‖)^n`. The hypothesis
`‖x‖ < ‖algebraMap ℚ_[p] L p‖ = p⁻¹` makes this a summable geometric series.
No step assumes that `p` is odd, so the same proof covers `p = 2`. Both final
results are obtained with `Summable.of_norm`; they are proof terms, not named
`Prop` definitions.

### Minimal errors

The round-1 probe only defined convergence propositions and was rejected. The
strengthened arbitrary-extension theorem now elaborates with no remaining
error. Mathlib still has no ready local-field logarithm with the P7
inverse/image/kernel package. The GO verdict proves convergence on these balls
and does not claim those later inverse or torsion-kernel results.

### Proposed representation

Define `padicLog x` by the `log(1+x)` termwise `tsum` and define exponential by
the proved factorial series on the strict ball. The probe's norm-majorant
lemmas provide the convergence API; P7 may compare this sum with
`NormedSpace.exp` where its radius API applies. Keep the `p = 2` radius explicit.
Do not add a `LogExpPackage` certificate.

## 5. Haar measure normalized on the integer ring — GO

Probe: `.pi/probes/P5Haar.lean`.

### Imports tried

```lean
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.NormedValued
```

### Declarations tried

* `FiniteDimensional.proper`
* `TopologicalSpace.PositiveCompacts`
* `isCompact_closedBall`
* `Metric.ball_subset_interior_closedBall`
* `MeasureTheory.Measure.addHaarMeasure`
* `MeasureTheory.Measure.addHaarMeasure_self`

The probe installs `ProperSpace L`, equips `L` with its Borel measurable space,
packages `closedBall 0 1` as a positive compact, and obtains a measure `μ` with
`μ K0 = 1`. It also proves that this closed ball is the valuation ring's
underlying set.

### Minimal errors

The first measure construction lacked `MeasurableSpace L`; choosing `borel L`
and the corresponding `BorelSpace L` instance resolved it. No unresolved error
remains.

### Proposed representation

Define the additive Haar measure from the positive compact integer ring, rather
than choosing an arbitrary Haar measure and adding a normalization field. Its
mass-one theorem is `addHaarMeasure_self`. P11 will prove scalar, direct-sum,
tensor, and quotient formulas from this constructed measure.

## Probe commands and trust boundary

The passing probes were checked individually with:

```bash
lake env lean .pi/probes/P5FiniteExtension.lean
lake env lean .pi/probes/P5ValuationData.lean
lake env lean .pi/probes/P5TensorNormalization.lean
lake env lean .pi/probes/P5LogExp.lean
lake env lean .pi/probes/P5Haar.lean
```

The phase trust audit is run only in the specification's documented mode:

```bash
AUDIT_FEASIBILITY_PHASE=P5 ./scripts/audit_trust.sh
```

Taxis issue #4 already covers the P5--P11 local-field infrastructure exposed by
these probes. No separate big subproject beyond that issue's scope was found,
so no new child issue was filed.
