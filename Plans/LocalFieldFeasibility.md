# P5 local-field feasibility report

Date: 2026-07-19

## Verdict

| Item | Verdict | Reason |
|---|---|---|
| Finite complete normed extension of `ℚ_[p]` | **GO** | The spectral-norm API constructs compatible nontrivially normed-field and normed-algebra structures from a finite field extension, and supplies completeness. |
| Valuation ring, normalized order, ramification/residue data, and different | **GO** | The spectral valuation ring is compact, hence a DVR with finite residue field; valuation-extension instances then expose ramification, inertia, and the different. Normalizing the resulting discrete field valuation by the ramification index gives the planned order with `ord(p) = 1`. |
| Finite tensor over `ℤ_[p]`, reduction, total quotient ring, normalization | **GO** | `PiTensorProduct`, quotient by `nilradical`, localization at `nonZeroDivisors`, and `integralClosure` compose at the type/instance level. |
| Log/exp convergence ball | **GO** | The formal series and generic radius APIs elaborate, and existing `p`-adic valuation estimates give a non-circular comparison route: log on `‖x‖ < 1`, exp on the smaller uniform ball `‖x‖ < ‖p‖`. |
| Haar measure normalized on the integer ring | **GO** | Finite dimensionality gives properness; the integer ring is the compact closed unit ball with nonempty interior, so `addHaarMeasure` normalizes it to mass one. |

**Overall P5 verdict: GO.** All five prototypes identify a construction/proof
route without adding the desired conclusions as assumptions. This is a
feasibility verdict, not a proof of P6--P11. P6 was not started.

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

## 2. Valuation ring, normalized order, `e`, `f`, and different — GO

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
`vK.HasExtension vL`. Define:

* `e` as `(IsLocalRing.maximalIdeal OL).ramificationIdx OK`;
* `f` as `(IsLocalRing.maximalIdeal OL).inertiaDeg OK`;
* the local different as `differentIdeal OK OL`;
* the uniformizer-normalized field valuation by
  `(IsDiscreteValuationRing.maximalIdeal OL).valuation L`;
* `ord` by converting that discrete multiplicative valuation to its additive
  integer exponent and dividing by `e`.

The P6 proof uses
`IsDedekindDomain.HeightOneSpectrum.valuation_liesOver` at `p`, then rewrites the
older multiplicity definition with `Ideal.ramificationIdx'_eq_ramificationIdx`.
This connects the discrete valuation of the image of `p` with `e` and yields
`ord(p) = 1` after scaling. The data above are constructed independently of that
equality; storing `ord(p) = 1` as caller data would violate the honesty rule.

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

## 4. Log/exp convergence ball — GO

Probe: `.pi/probes/P5LogExp.lean`.

### Imports tried

```lean
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PowerSeries.Log
```

### Declarations tried

* `PowerSeries.log`, `PowerSeries.exp`
* `PowerSeries.coeff_log`, `PowerSeries.coeff_exp`
* `NormedSpace.expSeries`
* `NormedSpace.expSeries_summable_of_mem_ball`
* `NormedSpace.expSeries_hasSum_exp_of_mem_ball`
* `FormalMultilinearSeries.le_radius_of_summable_norm`
* `padicValNat_le_nat_log`
* `padicValNat_factorial`, `padicValNat_factorial_le`
* `Padic.norm_p`
* `summable_pow_mul_geometric_of_norm_lt_one`

The probe defines the termwise log, its `tsum`, the generic exponential, and the
exact convergence propositions without proving them by assumption.

### Proof route and ball

For log, `padicValNat_le_nat_log` bounds the norm of `1/(n+1)` by a polynomial
factor in `n+1`. Thus the log terms are dominated by a polynomial times
`‖x‖^(n+1)`, summable for `‖x‖ < 1` by
`summable_pow_mul_geometric_of_norm_lt_one`.

For exp, `padicValNat_factorial_le` gives the coarse bound needed to dominate
`‖x^n/n!‖` by a geometric series whenever `‖x‖ < ‖p‖ = p⁻¹`. This strict ball
works uniformly, including `p = 2`. `spectralNorm_extends` transports the
coefficient norm calculations from `ℚ_[p]` to `L`. The generic formal
multilinear radius theorem then packages the resulting summability.

### Minimal errors

No remaining elaboration error. Mathlib has no ready local-field logarithm with
the P7 inverse/image/kernel package, so P7 must implement the comparison proofs
above. The GO verdict concerns convergence on these balls and does not claim the
later inverse or torsion-kernel results.

### Proposed representation

Define `padicLog x` by the `log(1+x)` termwise `tsum` and use
`NormedSpace.exp`/`NormedSpace.expSeries` for exponential, with project lemmas
that expose the proven strict balls. Keep the `p = 2` radius explicit. Do not add
a `LogExpPackage` certificate.

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
