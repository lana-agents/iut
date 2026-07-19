# IUT IV Section 1: phase-gated implementation specification

Date: 2026-07-19

## 1. Objective and source of truth

Formalize Section 1, “Log-volume Estimates,” of Mochizuki’s *Inter-universal
Teichmüller Theory IV* (`references/iut4.pdf`, pp. 9–39 of the paper), covering
Propositions 1.1–1.8, Definition 1.9, and Theorem 1.10. The repository must also
contain a Verso blueprint and a `leanprover/comparator` challenge/solution pair.

The mathematical source of truth is the paper, checked against
`references/iut4-section1.txt`; `references/iut4.txt` is only a searchable
extraction. The public [`proetale`](https://github.com/chrisflav/proetale) repository is the
template for the Verso and comparator infrastructure.

A conditional Lean theorem must expose every imported IUT result and every
non-IUT library gap as an ordinary explicit argument. It must not be described
as an unconditional formalization of that input.

## 2. Honesty boundary

### 2.1 Mathematics proved in this repository

The following results require Lean proof terms rather than certificate fields.

* Ceiling/floor inequalities, finite sums/products, Proposition 1.7, and (E1),
  (E2).
* The local-field results in Propositions 1.1–1.4, but only after the feasibility
  gates in §5 establish that the intended finite-extension model is constructible.
  Desired local conclusions may not be fields of `MixedCharLocalFieldData`.
* Proposition 1.5.
* Only prime-counting consequences that are immediate from mathlib's existing
  Chebyshev theorem may be included unconditionally. Proposition 1.6 is stated
  conditionally on `PrimeCountingCertificate`; this repository does not pursue
  a stronger unconditional bound.
* The finite-group and linear-algebra lemmas isolated from Proposition 1.8.
  Elliptic/abelian geometry outside current mathlib is conditional under §2.3.
* Definition 1.9(i), together with the related raw-degree local-ratio variant
  recorded in P4, and all elementary assembly in Theorem 1.10 after every
  interface/certificate argument has been supplied. Definition 1.9(ii)'s
  displayed quotient is not currently claimed for the scaling reason recorded
  in P4 and the blueprint.

A helper structure may package ambient operations and their standard laws. It
may not contain an advertised proposition under another name.

### 2.2 Imported-IUT interfaces: exact signatures

There are exactly five imported-IUT structures. P15 first adds their ambient
carriers and all containers in `Iut4Sec1/IUT/Carriers.lean`, then adds the
carrier-indexed reduction family, and only then defines the five interfaces in
`Iut4Sec1/IUT/Interfaces.lean`; the interfaces do not get to choose the
carriers. P14 contains no declaration indexed by `InitialThetaCarriers`. In
particular:

* `InitialThetaCarriers` is a data-only record whose fields are the types
  `Fmod`, `Ftpd`, `F`, and `K` with their `Field`/`NumberField` instances; the
  three tower embeddings; `ell : ℕ`; the finite place types and maps induced by
  those embeddings; fixed finite sets `goodPlaces`, `badPlaces`, and
  `distinguishedPlaces`; the elliptic-curve carrier; and concrete
  `qDivisor`, `differentFtpd`, `differentF`, `conductorFtpd`, and `conductorF`
  values of the `ArithmeticDivisor` type from P4. It has no real-valued field.
  Quantities `dmod`, `emod`, `logQ`, `logDifferent`, and `logConductor` are
  definitions computed from these objects.
* `LocalShell`, `RationalTensorPacket`, `IntegralContainer`,
  `PossibleImages`, `Ind1Container`, `Ind2Container`, `Ind3Container`,
  `HolomorphicHull`, `LocalHullContainer`, `localLogVolume`, and
  `globalHullLogVolume` are definitions parameterized by the fixed carrier
  record. In particular, `HolomorphicHull` and every right-hand container in a
  containment field exist before `ThetaPilotRealization`.
* `RawPacketWeight D j t` is the product of the positive local degrees from
  `D`; `normalizedPacketWeight` is its quotient by the finite sum of all raw
  weights. These are definitions before `ProcessionNormalization`.

The carrier record has no imported-result or numerical-conclusion field and is
not itself an imported-result interface. Its standard algebraic instance laws
serve only to type the fixed objects. The following Lean-shaped declarations are the required signatures;
implementation may change binder syntax only when elaboration requires it. A
reviewed specification amendment is required to add, remove, or weaken a field.
Here `D : InitialThetaCarriers`, `v : D.PlaceQ`, `j : D.J`, and
`t : D.PacketTuple v j`; finiteness/decidable-equality instances are attached to
the carrier types.

```lean
structure InitialThetaData (D : InitialThetaCarriers) : Prop where
  ell_prime : D.ell.Prime
  seven_le_ell : 7 ≤ D.ell
  fmodToFtpd_injective : Function.Injective D.fmodToFtpd
  ftpdToF_injective : Function.Injective D.ftpdToF
  fToK_injective : Function.Injective D.fToK
  tower_comp :
    D.fmodToK = D.fToK.comp (D.ftpdToF.comp D.fmodToFtpd)
  ftpd_finite_over_fmod : Module.Finite D.Fmod D.Ftpd
  f_finite_over_ftpd : Module.Finite D.Ftpd D.F
  k_finite_over_f : Module.Finite D.F D.K
  k_galois_over_fmod : D.IsGaloisKOverFmod
  good_bad_disjoint : Disjoint D.goodPlaces D.badPlaces
  good_union_bad : D.goodPlaces ∪ D.badPlaces = Finset.univ
  bad_nonempty : D.badPlaces.Nonempty
  bad_residueCharacteristic_odd :
    ∀ v ∈ D.badPlaces, Odd (D.residueCharacteristic v)
  qDivisor_effective : D.qDivisor.Effective
  differentFtpd_effective : D.differentFtpd.Effective
  differentF_effective : D.differentF.Effective
  conductorFtpd_effective : D.conductorFtpd.Effective
  conductorF_effective : D.conductorF.Effective
```

`D.IsGaloisKOverFmod` is an abbreviation fixed in `Carriers.lean` for
`D.fmodToK.IsGalois`, not a caller-selected predicate. These are the ordinary
hypotheses appearing in the statement/setup of Theorem 1.10. `dmod`, `emod`,
`eStarMod`, the place predicates, and every real invariant are derived from
`D`; no field of `InitialThetaData` has type `x ≤` the Theorem 1.10 bound.
Torsion rationality, Legendre descent, good/semi-stable reduction, and the
elliptic consequences used for (D0)–(D7)/(R1)–(R4) are not hidden here; they
come from the explicit `ReductionCertificate` family in §2.3.

```lean
structure LogShellPacket (D : InitialThetaCarriers) where
  shell : ∀ v : D.PlaceMod, LocalShell D v
  rationalTensorPacket :
    ∀ (v : D.PlaceQ) (j : D.J), RationalTensorPacket D v j
  integralContainer :
    ∀ (v : D.PlaceQ) (j : D.J), IntegralContainer D v j
  logVolume_mono :
    ∀ {v j} {A B : Set (D.LocalSpace v j)}, A ⊆ B →
      localLogVolume D v j A ≤ localLogVolume D v j B
  logVolume_smul :
    ∀ {v j} (n : ℤ) (A : Set (D.LocalSpace v j)),
      localLogVolume D v j (D.uniformizerPow n • A) =
        localLogVolume D v j A - n * Real.log (D.residueCharacteristicQ v)
  logVolume_directSum :
    ∀ (v : D.PlaceQ) (j : D.J)
      (A : ∀ w : D.PlacesOver v, Set (D.PlaceSpace w j)),
      localLogVolume D v j (D.directSumImage A) =
        ∑ w : D.PlacesOver v, D.placeWeight w * D.placeLogVolume w j (A w)
  logVolume_tensor :
    ∀ (v : D.PlaceQ) (j : D.J)
      (A : ∀ i : D.TensorIndex j, Set (D.TensorFactorSpace v j i)),
      localLogVolume D v j (D.tensorProductImage A) =
        ∑ i : D.TensorIndex j, D.tensorFactorLogVolume v j i (A i)
  integralContainer_volume :
    ∀ v j, localLogVolume D v j (integralContainer v j) = 0
```

`directSumImage`, `tensorProductImage`, `placeLogVolume`, and
`tensorFactorLogVolume` are fixed definitions in `Carriers.lean`, rather than
fields or caller-selected relations. These equalities contain no numerical upper
bound.

```lean
structure ThetaPilotRealization
    (D : InitialThetaCarriers) (S : LogShellPacket D) where
  realize : ∀ v j, D.ThetaPilot v j → D.LocalSpace v j
  possibleImages_subset_ind1 :
    ∀ v j, PossibleImages D S realize v j ⊆ Ind1Container D S v j
  ind1_subset_ind2 :
    ∀ v j, Ind1Container D S v j ⊆ Ind2Container D S v j
  ind2_subset_ind3 :
    ∀ v j, Ind2Container D S v j ⊆ Ind3Container D S v j
  hull_subset_localContainer :
    ∀ v j, HolomorphicHull D (Ind3Container D S v j) ⊆
      LocalHullContainer D S v j
```

Every proposition-valued field is exactly a set containment. In particular,
`ThetaPilotRealization` has no `logVolume ≤ ...` field, no global numerical
inequality, and no configurable hull/container carrier.

```lean
structure ProcessionNormalization
    (D : InitialThetaCarriers) (S : LogShellPacket D)
    (R : ThetaPilotRealization D S) : Prop where
  procession_volume_eq :
    globalHullLogVolume D S R =
      ∑ j : D.J, ∑ t : D.PacketTupleFor j,
        normalizedPacketWeight D j t *
          localLogVolume D (D.placeOf t) j (LocalHullContainer D S _ j)
```

`rawPacketWeight_pos`, `rawPacketWeight_sum_pos`, and
`sum_normalizedPacketWeight_eq_one` must be proved before this structure from
positive local degrees and finite nonempty index types. Weight normalization is
not a field.

```lean
structure Corollary312Input
    (D : InitialThetaCarriers) (S : LogShellPacket D)
    (R : ThetaPilotRealization D S) where
  CTheta : ℝ
  neg_one_le_CTheta : -1 ≤ CTheta
  cor312_relation :
    globalHullLogVolume D S R = (CTheta + 1) * D.absLogQ
```

`D.absLogQ = (1 / (2 * D.ell)) * D.logQ` is defined beforehand and proved
positive. `cor312_relation` is the exact equality used in the paper to pass
between hull log-volume and `CTheta`; this structure has no upper bound on
`CTheta` or hull volume.

The final theorem takes values of all five structures explicitly. No instance is
declared globally. Blueprint nodes using them are marked **conditional on IUT
I–III interfaces**.

### 2.3 Explicit non-IUT library-gap interfaces

#### Prime-counting certificate (chosen route (b))

Mathlib v4.32.0 proves

```lean
Chebyshev.eventually_primeCounting_le {ε : ℝ} (εpos : 0 < ε) :
  ∀ᶠ x in Filter.atTop,
    Nat.primeCounting ⌊x⌋₊ ≤ (Real.log 4 + ε) * x / Real.log x
```

Its leading coefficient is `log 4`, which is strictly greater than `4 / 3`.
Mathlib v4.32.0 has no prime-number-theorem asymptotic from which the paper's
coefficient follows. This project therefore chooses route (b):

```lean
structure PrimeCountingCertificate : Prop where
  pnt :
    Filter.Tendsto
      (fun x : ℝ =>
        (Nat.primeCounting ⌊x⌋₊ : ℝ) * Real.log x / x)
      Filter.atTop (nhds 1)
```

This is a clearly named external, non-IUT assumption. Proposition 1.6 is stated
conditionally as `proposition16_of_primeCountingCertificate`; its `n₀`,
`ηprm`, exact `4 / 3` nth-prime bound, and exact `4 / 3` prime-counting bound are
derived from `PrimeCountingCertificate.pnt`, rather than stored as certificate
fields.

The PrimeNumberTheoremAnd project of Kontorovich, Tao, et al. is the known Lean
discharge path for this certificate. Adapting it as a potential future
repository dependency is outside this project's scope and is tracked externally
as taxis issue #6. This repository does not reprove the prime number theorem.

P13 may include only unconditional consequences obtained as trivial direct
applications of existing mathlib Chebyshev results, such as a wrapper around
`Chebyshev.eventually_primeCounting_le` at a specified positive rational `ε`.
No effort is allocated to proving or sharpening unconditional prime-counting
bounds here. Such a wrapper is not substituted for Proposition 1.6 and is not
used to claim the paper's exact statement.

All downstream constant tracking uses
`proposition16_of_primeCountingCertificate`: in Step (viii),

```text
lStarMod * log(sLe) ≤ (4 / 3) * (eStarMod * ell + etaPrm)
```

remains exact, so the paper's subsequent `20`, `56`, and `10` constants are
unchanged. Consequently Theorem 1.10 is also explicitly conditional on a
`PrimeCountingCertificate`. The unconditional Chebyshev lemma cannot discharge
that parameter.

#### Elliptic/abelian geometry and reduction certificates

The library gap is wider than Proposition 1.8(v)–(vii). Mathlib v4.32.0 has
Weierstrass equations, integral/minimal equations, and good-reduction predicates,
but not the needed package of abelian varieties, polarized automorphism groups,
Tate modules, elliptic moduli stacks with level structure, scheme-automorphism
descent, Néron/semi-abelian models, or inertia consequences.

After P14 has recorded feasibility and proved any unconditional core lemmas,
P15 may add `Iut4Sec1/Elliptic/Carriers.lean` and
`Iut4Sec1/Elliptic/ReductionInterface.lean`. This happens after
`Iut4Sec1/IUT/Carriers.lean` has introduced `InitialThetaCarriers`, so the
reduction interface may define the following indexed family without a forward
reference:

```lean
inductive ReductionUse (D : InitialThetaCarriers)
  | serre
  | automorphismDescent
  | twoTorsionFactorization
  | rationalTorsionUniqueness
  | semistable (v : D.RelevantFinitePlace)
  | legendre
  | inertia (v : D.RelevantFinitePlace) (n : ℕ)

def ReductionConclusion (D : InitialThetaCarriers) : ReductionUse D → Prop
  | .serre => Function.Injective D.polarizedAutToTorsion
  | .automorphismDescent => D.autSequence.Exact ∧
      D.minimalField = D.fieldGeneratedByJ ∧ D.modelsEquivSections
  | .twoTorsionFactorization =>
      ∃ ρ₂ : D.GE →* MulAut D.twoTorsion, D.rhoTwo = ρ₂.comp D.toGE
  | .rationalTorsionUniqueness =>
      ∀ E₁ E₂ ∈ D.rationalTorsionModels, D.ModelsIsomorphic E₁ E₂
  | .semistable v => D.HasSemistableModel v
  | .legendre => D.HasLegendreModel ∧ D.LegendreQuadraticSemistable
  | .inertia v n =>
      (D.HasGoodReduction v → D.TorsionActionUnramified v n) ∧
      (D.HasBadMultiplicativeReduction v → D.TorsionKernelTame v n ∧
        D.TorsionKernelRamificationIndex v n ∣ n)

structure ReductionCertificate
    (D : InitialThetaCarriers) (u : ReductionUse D) : Prop where
  conclusion : ReductionConclusion D u
```

All symbols on the right are fixed geometric definitions in
`Elliptic/Carriers.lean`; in particular `ReductionConclusion` is not configurable.
The index family is restricted in the final theorem to the finite set
`D.reductionUses` containing exactly the global and place-indexed uses needed in
Theorem 1.10. This historical name covers the whole unavailable elliptic/abelian
package, not only reduction parts (v)–(vii). The match cases faithfully state the
relevant clauses of Proposition 1.8; the ordinary hypotheses (`ell ≥ 3`,
invertibility, rational torsion, `Aut = {±1}`, and reduction hypotheses) are
arguments inside the fixed definitions and are not dropped. No case mentions a
Theorem 1.10 numerical inequality.

Only finite-group/linear-algebra lemmas such as faithfulness of a finite-order
matrix action under explicit eigenvalue hypotheses are unconditional. Every
geometric wrapper is named `..._of_reductionCertificate`, and blueprint item 1.8
remains **conditional/partial**. The final theorem takes
`reduction : ∀ u : ReductionUse D, u ∈ D.reductionUses →
ReductionCertificate D u` explicitly.

No additional unproved claim may be moved into an interface. A newly discovered
library gap causes a NO-GO verdict and a reviewed specification-amendment commit.

### 2.4 Mathlib v4.32.0 API snapshot used by this plan

This revision rechecked the pinned dependency rather than relying on API names
from another release.

* `Mathlib/NumberTheory/Chebyshev.lean` contains the exact
  `Chebyshev.eventually_primeCounting_le` signature quoted above;
  `Mathlib/NumberTheory/PrimeCounting.lean` defines `Nat.primeCounting`,
  `Nat.primeCounting'`, and zero-based `Nat.nth Nat.Prime` lemmas, but no PNT.
* `NumberField.FinitePlace.adicCompletion` supplies a normed complete local
  completion and its integer ring has an `IsDiscreteValuationRing` instance.
  `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean` identifies the rational
  completion with `ℚ_[p]`. No checked theorem directly constructs all required
  normalized data for an arbitrary finite extension of `ℚ_[p]`; this is why P5
  and the P6 constructor gate are mandatory.
* The `Mathlib/NumberTheory/Padics/` search found no general local-field
  logarithm/exponential API with the Proposition 1.2 image and torsion-kernel
  theorems. Generic power-series tools exist, so P7 is a prerequisite project,
  not a structure assumption.
* `Mathlib/RingTheory/DedekindDomain/Different.lean` provides
  `differentIdeal`, transitivity, and ramification criteria, but not the local
  tensor-normalization and upper-bound package requested in Propositions
  1.1/1.3. Generic additive Haar measure exists, without the normalized local
  volume computations in Proposition 1.4.
* `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean` gives the real inner
  product and norm on `ℂ ⊗[ℝ] ℂ`, including `TensorProduct.norm_tmul`; this
  supports the Proposition 1.5 challenge map and factor-two metric statement.
* `NumberField.FinitePlace` exposes the associated maximal ideal and its
  `Ideal.absNorm`, while `NumberField.InfinitePlace` represents archimedean
  places modulo conjugation. Together with `Finsupp`, these support the
  Definition 1.9(i) challenge model, but no checked API uniformly pulls both
  place types through a finite field extension with the local-degree identity.
* `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` defines integral and
  minimal Weierstrass equations and good reduction; the affine/projective point
  files provide point groups, and `Weierstrass.lean` provides the two-torsion
  polynomial. The abelian-variety, moduli/descent, semi-abelian/Néron,
  Tate-module, and inertia APIs listed in §2.3 were not found, so these pieces do
  not suffice to state a complete clause of Proposition 1.8.

## 3. Comparator challenge suite and justification

### 3.1 Inclusion rule and Section 1 inventory

`Comparator/Challenge.lean` remains a standalone `import Mathlib` module. It
contains every Section 1 target that can be stated without importing this
project and without manufacturing a surrogate for unavailable IUT or
arithmetic-geometry infrastructure. Small definitions assembled directly from
mathlib primitives are allowed, as in the public `proetale` comparator template.
Every theorem target below has a proof body consisting of one `sorry`.
Auxiliary definitions contain no placeholder.

The following inventory is binding for the P3b expansion.

| Section item | Decision | Challenge representation or reason |
|---|---|---|
| Proposition 1.1 | **OUT** | The statement needs the normalization of a reduced iterated tensor product of local integer rings, total quotient rings, normalized different exponents, and fractional-ideal scalar actions. Mathlib primitives exist separately, but assembling this just to state the inclusion is the substantive P5/P8 representation project. |
| Proposition 1.2 | **IN (numerical clause)** | State the displayed small-ramification equality `aParam p e = 1/e ∧ bParam p e = -1/e`; define `aParam` and `bParam` by the paper's ceiling/floor formulas. The requested unit-log-lattice equality for arbitrary finite extensions of `ℚ_[p]` stays out: v4.32.0 has `Padic`, completions, and abstract finite extensions, but no general local-field logarithm with the required image lattice, and no turnkey model connecting all of these to normalized ramification data. |
| Proposition 1.3 | **OUT** | Its actual assertions quantify normalized local different orders in towers and tame/Galois ramification; those objects are not connected by a fairly easy mathlib-only interface. Replacing them by arbitrary real variables plus the desired inequalities would merely assume the proposition. |
| Proposition 1.4 | **IN (two arithmetic cores)** | Keep the proved ceiling-error sum and add the second finite-sum error bound with the paper's `∑ (3 + log eᵢ)` term. Haar log-volume, torsion quotients, tensor normalization, and the displayed lattice inclusions remain outside the challenge. |
| Proposition 1.5 | **IN (part (i))** | Define the canonical real-linear CRT map `ℂ ⊗[ℝ] ℂ →ₗ[ℝ] ℂ × ℂ`, `z ⊗ₜ w ↦ (z*w, conj z*w)`, and the direct-sum squared metric. State bijectivity and the factor-two norm identity for every tensor. The multiple-factor integral-container clauses are deferred to P12 rather than rebuilt in the challenge. |
| Proposition 1.6 | **IN** | State the unconditional eventual `4/3` prime-counting inequality using `Nat.primeCounting ⌊x⌋₊`. It is a valid mathlib-vocabulary statement even though v4.32.0 cannot prove it. Its solution-side consequence is recorded in §3.4. |
| Proposition 1.7 | **IN** | State the full finite weighted-average identity using tuples `Fin n → E`, with positive weights, `Nonempty E`, and `NeZero n`. Auxiliary tuple weight/value definitions are copied into the challenge. |
| Proposition 1.8 | **OUT** | Mathlib's `WeierstrassCurve`, point groups, two-torsion polynomial, variable changes, and good-reduction predicates do not provide any complete clause of Proposition 1.8: Serre's criterion needs polarized abelian varieties and Tate modules, while clauses (ii)–(vii) need Galois descent, moduli, semistable models, or inertia. Restating the existing discriminant identity would be related elliptic algebra, but would not state one of the proposition's claims. |
| Definition 1.9 | **IN (part (i))** | Define places as `FinitePlace K ⊕ InfinitePlace K`, `ArithmeticDivisor K` as a finitely supported real function, finite-place weight `log (Ideal.absNorm v.maximalIdeal.asIdeal)`, infinite-place weight `1`, effectiveness, degree, and normalized degree divided by `finrank ℚ K`. State nonnegativity of normalized degree for effective divisors. Pullback invariance and part (ii)'s `E`-degree stay out because mathlib has no fairly easy uniform pullback map on both kinds of places with the required local-degree formula. |
| Theorem 1.10 | **OUT** | The theorem proper quantifies initial Θ-data, log-shells, Θ-pilot realizations, procession normalization, and Corollary 3.12; these are precisely the IUT I–III interfaces forbidden in the mathlib-only challenge. |

The proof of Theorem 1.10 also uses the elementary identities (E1) and (E2).
They are **IN** as two additional targets because they are standalone finite-sum
identities over `ℝ`; this does not bring any Θ-pilot content into the challenge.

### 3.2 Exact target manifest

The P3b challenge has the following ten theorem targets and therefore exactly
ten `sorry` occurrences, one in each listed proof and nowhere else.
Binder spelling may change only as required by elaboration; the mathematical
types and fully qualified names are fixed here.

1. **Proposition 1.2 parameter equality.** The challenge defines
   `Iut4Sec1.aParam` and `Iut4Sec1.bParam` from
   ```lean
   aParam p e = if 2 < p then
     ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e else 2
   bParam p e =
     ((⌊Real.log (((p : ℝ) * e) / (p - 1 : ℕ)) / Real.log p⌋ : ℤ) : ℝ) - 1 / e
   ```
   and states
   ```lean
   theorem localParameters_eq_of_smallRamification
       (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p)
       (he : 0 < e) (hsmall : e ≤ p - 2) :
       aParam p e = 1 / (e : ℝ) ∧ bParam p e = -1 / (e : ℝ) := by
     sorry
   ```

2. **First Proposition 1.4(iii) error sum.** Keep the existing
   `nonarchimedeanLogError` definition and declaration:
   ```lean
   theorem nonarchimedean_logError_sum_le {ι : Type*} [DecidableEq ι]
       (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
       (hp : p.Prime) (hp2 : 2 < p) (hIstar : Istar ⊆ I)
       (he : ∀ i ∈ I, 0 < e i)
       (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
       ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
         4 * (Istar.card : ℝ) / p := by
     sorry
   ```
   Its project proof remains the P3 theorem.

3. **Second Proposition 1.4(iii) error sum.** State
   ```lean
   theorem nonarchimedean_secondError_sum_le {ι : Type*} [DecidableEq ι]
       (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
       (hp : p.Prime) (hIstar : Istar ⊆ I)
       (he : ∀ i ∈ I, 0 < e i)
       (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
       (∑ i ∈ I, (aParam p (e i) + bParam p (e i))) * Real.log p ≤
         ∑ i ∈ Istar, (3 + Real.log (e i)) := by
     sorry
   ```
   This is exactly the numerical estimate used after log-volume scaling in the
   second display; it does not pretend to define Haar log-volume.

4. **Proposition 1.5 CRT map.** Define `complexTensorToProd` by
   `TensorProduct.lift` from the bilinear map
   `z, w ↦ (z * w, Complex.conj z * w)`, and state
   ```lean
   theorem complexTensorToProd_bijective :
       Function.Bijective complexTensorToProd := by
     sorry
   ```

5. **Proposition 1.5 factor-two metric.** Define
   `complexPairNormSq u = Complex.normSq u.1 + Complex.normSq u.2` and state
   ```lean
   theorem complexTensorToProd_normSq (x : ℂ ⊗[ℝ] ℂ) :
       complexPairNormSq (complexTensorToProd x) = 2 * ‖x‖ ^ 2 := by
     sorry
   ```
   Here the tensor norm is mathlib's inner-product tensor norm. The explicit
   `complexPairNormSq` avoids the max norm on the ordinary product type and is
   the direct-sum Hermitian squared metric meant in Proposition 1.5(i).

6. **Proposition 1.6 prime counting.** State
   ```lean
   theorem eventually_primeCounting_le_four_thirds :
       ∀ᶠ x : ℝ in Filter.atTop,
         (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
           4 * x / (3 * Real.log x) := by
     sorry
   ```

7. **Proposition 1.7 weighted averages.** Define, for
   `x : Fin n → E`,
   ```lean
   tupleWeight λ x = ∏ j, λ (x j)
   tupleValue β x = ∑ j, β (x j)
   ```
   and state `Iut4Sec1.weighted_average_eq` for a finite nonempty `E`,
   `[NeZero n]`, positive `λ`, and `i : Fin n`: the two quotients
   ```text
   (Σ x, tupleValue β x * tupleWeight λ x) / (Σ x, tupleWeight λ x)
   (Σ x, n * β (x i) * tupleWeight λ x) / (Σ x, tupleWeight λ x)
   ```
   are equal and both equal
   `n * ((Σ e, β e * λ e) / (Σ e, λ e))`. This conjunction of two equalities
   is the exact planned theorem type.

8. **(E1).** State `Iut4Sec1.average_range_sum` for `0 < n`:
   ```text
   (1 / n) * Σ m in range n, (m + 1) = (n + 1) / 2
   ```
   with every term coerced to `ℝ`.

9. **(E2).** State `Iut4Sec1.average_range_sq_sum` for `0 < n`:
   ```text
   (1 / n) * Σ m in range n, (m + 1)^2 = ((2*n + 1) * (n + 1)) / 6
   ```
   with every term coerced to `ℝ`.

10. **Definition 1.9 degree positivity.** The challenge defines
    `ArithmeticPlace`, `ArithmeticDivisor`, `arithmeticPlaceWeight`,
    `ArithmeticDivisorEffective`, `arithmeticDivisorDegree`, and
    `normalizedArithmeticDivisorDegree` exactly as described in §3.1, then states
    ```lean
    theorem normalizedArithmeticDivisorDegree_nonneg
        {K : Type*} [Field K] [NumberField K]
        (D : ArithmeticDivisor K)
        (hD : ArithmeticDivisorEffective D) :
        0 ≤ normalizedArithmeticDivisorDegree D := by
      sorry
    ```

The first error-sum proof still uses the argument already reviewed in P3: for
`d = p - 2 > 0`, positivity gives
`ceil (e / d) - 1 < e / d`, hence the error is below
`1 / d ≤ 4 / p`; it vanishes when `e ≤ d`, and summation filters the exceptional
indices. The other targets are present because they are faithful, compact
mathlib-only statements, regardless of current proof availability.

### 3.3 Comparator configuration and phase growth

Comparator configuration always has challenge module `Challenge`, solution
module `Solution`, `definition_names: []`, and the reviewed permitted-axiom list
contained in `{propext, Quot.sound, Classical.choice}`. Auxiliary definitions are
part of the statement vocabulary, not comparator tasks.

`theorem_names` means exactly: theorem declarations currently exported by
`Solution` with project proof terms and required to pass comparator. A sorried
challenge target may remain outside that array. P3b therefore expands the file
to ten targets while leaving only the already proved first error sum in
`theorem_names`; later phases append names only in the same commit that adds the
corresponding project proof and Solution import.

| Challenge theorem | Project proving phase | First config inclusion |
|---|---:|---:|
| `Iut4Sec1.nonarchimedean_logError_sum_le` | P3 (complete) | P3 |
| `Iut4Sec1.weighted_average_eq` | P4 | P4 |
| `Iut4Sec1.average_range_sum` | P4 | P4 |
| `Iut4Sec1.average_range_sq_sum` | P4 | P4 |
| `Iut4Sec1.normalizedArithmeticDivisorDegree_nonneg` | P4 | P4 |
| `Iut4Sec1.localParameters_eq_of_smallRamification` | P6 | P6 |
| `Iut4Sec1.nonarchimedean_secondError_sum_le` | P11 | P11 |
| `Iut4Sec1.complexTensorToProd_bijective` | P12 | P12 |
| `Iut4Sec1.complexTensorToProd_normSq` | P12 | P12 |
| `Iut4Sec1.eventually_primeCounting_le_four_thirds` | no unconditional proving phase | never under the present honesty boundary |

Thus the array has one name after P3b, five after P4, six after P6, seven after
P11, and nine after P12. The challenge still has ten sorried targets. P13 proves
only a theorem conditional on `PrimeCountingCertificate`; that theorem does not
prove the no-argument challenge declaration, so the Proposition 1.6 target stays
out of config. PrimeNumberTheoremAnd's status as a known future discharge path
does not change this configuration decision. Comparator success never converts
a challenge placeholder into a project axiom or certificate.

### 3.4 Solution and definition bridges

`Comparator/Solution.lean` is permanently import/re-export only after P3. It may
contain project imports and `#check` commands, but no `def`, `abbrev`, `instance`,
`lemma`, `theorem`, or wrapper declaration. In particular it never copies a
challenge auxiliary definition.

The challenge uses the eventual project names and signatures for `aParam`,
`bParam`, `nonarchimedeanLogError`, tuple weight/value,
`complexTensorToProd`, `complexPairNormSq`, and the arithmetic-divisor
vocabulary. P4, P6, P11, and P12 must either implement those project
constants with the same definitions or first prove project-side
`..._eq_comparatorFormula` lemmas and use those lemmas in the project theorem.
The exported target itself always has exactly the challenge type. Per target:

* the P3 first error sum is already a direct re-export;
* P4 directly re-exports the weighted-average, (E1), (E2), and divisor-positivity
  project theorems; its challenge-local Finsupp divisor model is copied as the
  project foundation, so no conversion structure is introduced;
* P6 directly re-exports the parameter equality after its `aParam`/`bParam`
  definitions are checked against the challenge formulas;
* P11 directly re-exports the second error sum, using equality lemmas if its
  internal log-volume notation unfolds through a differently organized helper;
* P12 directly re-exports both complex-tensor theorems after checking the CRT
  map and squared-metric definitions by definitional equality;
* the unconditional prime-counting target has no Solution declaration or bridge.
  `proposition16_of_primeCountingCertificate` has an extra hypothesis and cannot
  be used to populate config.

Challenge and Solution remain separate roots and are never imported together.
The signature script builds isolated declaration manifests for both roots,
intersects them, and diffs the complete elaborated type of **every shared
public declaration**, including shared auxiliary definitions and every
config-listed theorem. It also checks that every config name occurs in that
intersection and that no proved shared theorem target is omitted from config.
Normalization may remove only source locations and warning headers; declaration
names, universes, binder information, and types remain in the diff.

## 4. Repository conventions, trust audit, and phase gates

* Work directly on `main`, one reviewed phase-sized commit at a time, with
  message `P<n>: <summary>`. Do not push unless instructed.
* Every phase ends with `lake build` and `git diff --check`. Blueprint phases
  also build and generate the site.
* Keep `Iut4Sec1.lean` as the import root and update it with each public module.
* Do not commit `.lake/`, `.pi/`, `blueprint-verso/.lake/`, or generated
  `blueprint-verso/_out/`.
* `Comparator/Challenge.lean` has the sole reviewed placeholder exception. It
  has one `sorry` in P2/P3 and exactly ten after P3b, one for each target in
  §3.2. There are no other reviewed exceptions unless a later review records an
  exact file, line, token, and reason. In particular, the reviewed-exception
  list for `axiom`, `constant`, `admit`, `native_decide`,
  `Lean.ofReduceBool`, `ofReduceBool`, `implemented_by`, and `unsafe` is empty.
* Tracked files must use repository-relative paths or public URLs. The trust
  audit rejects machine-local absolute home paths and credential-shaped strings
  in every tracked text file; documentation, plans, workflows, and source files
  are all in scope.
* A reviewer must accept each phase before the next begins. Prototype phases
  have an explicit GO/NO-GO verdict; NO-GO prohibits the dependent phase until
  this specification is amended and reviewed.

### 4.1 Tracked-source token audit

From P1 onward `scripts/audit_trust.sh` runs `git grep` over tracked `*.lean`
files. It rejects command/tokens matching the following extended regular
expression:

```text
(^|[^[:alnum:]_])(axiom|constant|sorry|admit|native_decide|Lean\.ofReduceBool|ofReduceBool|implemented_by|unsafe)([^[:alnum:]_]|$)
```

The script excludes `Comparator/Challenge.lean` from the broad scan, then checks
the phase-appropriate count: one `sorry` through P3 and exactly ten from P3b
onward, with the ten theorem names matching §3.2. It also rejects every other
listed token in that file. It fails on an untracked Lean file as well, except
ignored `.pi/` probe files during a feasibility phase. Any future exception is
a literal allow-list entry `(path, line, token, reason)` reviewed in the phase
that introduces it; glob or directory exceptions are forbidden.

The trust script also scans every tracked text file and rejects a machine-local
absolute home path matching `/(Users|home)/`. This check is implemented before
P3b. Any exception uses a literal `(path, line, matched path token, reason)`
record under the same exact-match, single-use rules as token exceptions; glob
and directory exceptions are forbidden, and the reviewed list is currently
empty. The grouped pattern definition in the script contains neither matched
literal, so it needs no exception. A temporary tracked-index fixture tests the
negative path, the expected failure is recorded, and the fixture is removed
before the clean audit.

The same tracked-text scan rejects credential-shaped strings. Its patterns
include `[a-z]+_pat_[0-9a-f]{16,}` and the common `ghp_`, `gho_`, and
`github_pat_` token forms with credential-length alphanumeric payloads. Pattern
components in the script are split so the audit definition does not match
itself. Credential exceptions, if ever reviewed for synthetic documentation,
are exact single-use `(path, line, matched literal, reason)` entries; glob and
directory exceptions are forbidden, and real credentials are never eligible.
Diagnostics report only path and line, not the matched payload. A temporary
tracked-index fixture containing an obviously synthetic token-shaped string
must fail, be removed, and be followed by a clean audit.

### 4.2 Generated all-public-declaration axiom audit

P1 adds `scripts/AuditAxioms.lean`. It imports `Iut4Sec1` and, in a `run_cmd`,
iterates the environment, retaining every non-private declaration whose defining
module (from `Lean.findModuleOf?`) has prefix `Iut4Sec1`. For each retained name
it runs `Lean.collectAxioms`. The command prints a deterministic sorted table and
fails unless every dependency is in the reviewed standard allow-list
`{propext, Quot.sound, Classical.choice}`. Thus definitions and helper/public
theorems are audited, not only advertised results. Generated declarations are
included when public; private/compiler-generated names are excluded using
`Lean.isPrivateName` and the documented reserved-name predicate.

`scripts/audit_axioms.sh` first regenerates a declaration manifest from the
compiled root environment, compares it with the declarations visited by
`AuditAxioms.lean`, and then invokes `lake env lean scripts/AuditAxioms.lean`.
The count/name comparison prevents a filtering bug from silently auditing an
empty subset. `Comparator/Solution.lean` is audited separately because it is not
imported with the duplicate challenge. The challenge is expected to depend on
`sorryAx` and is excluded from this axiom gate.

Headline `#print axioms` checks remain additional review gates for the
comparator core, each proposition, and the final theorem. Passing a selected
headline check never substitutes for the generated all-public audit.

The standard tail of every phase from P1 onward is therefore:

```bash
./scripts/audit_trust.sh
./scripts/audit_axioms.sh
lake build
git diff --check
```

## 5. Phases

### P0 — Bootstrap and reviewed specification

**Scope.** Commit the scaffold, source files, this specification, and
`Plans/Iut4Sec1WorkLog.md`. P0 and its review revisions contain no blueprint,
comparator, or formalization code.

**Checks.** The bootstrap scaffold and its demonstration declaration were
removed after P4 by project-owner direction. The command listing below was
amended after that removal to give the current root-module equivalents; the P0
work-log entry remains the historical record of what was run at P0.

```bash
lake env lean Iut4Sec1.lean
lake build Iut4Sec1
lake build
printf 'import Iut4Sec1\n' > /tmp/Iut4Sec1Import.lean
lake env lean /tmp/Iut4Sec1Import.lean
git diff --check
git status --short --ignored
```

**Gate.** The reviewer verifies source/reference integrity, the complete
conditional signature, phase feasibility gates, and absence of implementation.
P1 waits for acceptance.

### P1 — Verso scaffold and trust-audit infrastructure

**Scope.** Add the nested Verso package and ten chapters for items 1.1–1.10,
adapted from `proetale`. Every node is either linked to an existing declaration
or marked not started/conditional. Add `scripts/audit_trust.sh`,
`scripts/AuditAxioms.lean`, and `scripts/audit_axioms.sh` as the then-current §4
specifies.
The all-public audit must detect a temporary deliberately contaminated public
declaration in an ignored `.pi/` probe, after which the probe is removed.

**Checks.** Build the root and nested packages, run `ci-pages.sh`, verify the
site/manifest, run both audits, and run `git diff --check`.

**Review focus.** Ten faithful chapter entries; visible IUT, prime-counting, and
elliptic certificate labels; audit coverage is nonempty and the negative test
fails for the intended reason.

### P2 — Comparator challenge and temporary independent solution

**Scope.** Add comparator infrastructure. `Challenge.lean` imports only
`Mathlib` and contains the copied definition/signature plus its sole placeholder.
`Solution.lean` also imports only `Mathlib` and temporarily contains the copied
definition/signature plus a placeholder. The project theorem does not yet exist.
The two roots are separate libraries/default targets and are never imported
together. Add config, README, workflow, and `CheckDecls.lean`.

**Checks.** Build Challenge, Solution, checkdecls, and root; print challenge
axioms; run the trust audit with the temporary P2 allow-list entry for the one
solution placeholder. This temporary entry expires in P3.

**Gate.** Reviewer compares the two source headers byte-for-byte after stripping
imports/docs and confirms neither imports `Iut4Sec1`.

### P3 — Comparator arithmetic and simultaneous solution re-export

**Scope.** Add `Iut4Sec1/Real/LogError.lean` with
`nonarchimedeanLogError`, its nonnegativity/zero/four-over-p lemmas, and
`nonarchimedean_logError_sum_le` with exactly the challenge signature. In the
same commit replace all declarations in `Comparator/Solution.lean` by:

```lean
import Iut4Sec1.Real.LogError

#check Iut4Sec1.nonarchimedean_logError_sum_le
```

The imported project declaration is the solution module's exported theorem;
there is no wrapper or redeclaration. Add
`scripts/check_comparator_signature.sh`, which creates two ignored temporary
files, imports `Challenge` and `Solution` separately, prints `#check` with fixed
pretty-printer options, normalizes only file-location/warning noise, and diffs
the complete elaborated types. It never imports both modules together.

**Checks.** Build project, Challenge, and Solution; run the signature script;
print axioms for the project theorem and solution theorem separately; run the
full §4 audits with no solution exception.

**Gate.** The diff of elaborated types is empty, only Challenge contains the
placeholder, and no duplicate declaration can occur in P3 or any later phase.

### P3b — User-directed multi-statement comparator expansion

**Scope.** Implement §3 without changing project mathematics. Expand
`Comparator/Challenge.lean` from one theorem to the ten-target mathlib-only
suite and copy in only the auxiliary definitions enumerated there. Every target
ends in one `sorry`; auxiliary definitions contain none. Keep
`Comparator/Solution.lean` as its P3 project import/re-export, and keep config's
`theorem_names` equal to the singleton already proved in P3.

Upgrade `scripts/check_comparator_signature.sh` to produce isolated public
manifests for Challenge and Solution, intersect them, and diff complete
elaborated types for all shared declarations as required by §3.4. It verifies
config completeness for the currently proved shared theorem targets rather than
assuming that every sorried challenge target has a Solution declaration. Update
the comparator README with the ten-target manifest and the config semantics.

Upgrade `scripts/audit_trust.sh` to require exactly ten named challenge targets
and ten `sorry` occurrences. Preserve the already implemented tracked-text
machine-local-path guard from §4.1 and rerun its temporary negative test.

**Checks.** Build Challenge, Solution, checkdecls, and the root; run the upgraded
all-shared signature diff; print axioms for the configured project/Solution
theorem; run both trust audits and the path negative test; run
`git diff --check`. Confirm the tracked source search required by the
user-directed amendment is empty.

**Gate.** Challenge imports only `Mathlib`; each §3.2 target occurs exactly once
and has exactly one placeholder; Solution declares nothing; config still has
exactly one theorem; all shared declarations have identical elaborated types;
and no tracked file contains a machine-local absolute home path.

### P4 — Finite combinatorics and Definition 1.9 foundations

**Scope.** Prove Proposition 1.7, (E1)/(E2), positive raw-weight arithmetic, and
normalized weights in `Combinatorics/`. The public `tupleWeight`, `tupleValue`,
`weighted_average_eq`, `average_range_sum`, and `average_range_sq_sum` have the
exact challenge signatures. Define finite-support arithmetic divisors, support,
effectiveness, degree, normalized degree, pullback, and parts in `Global/`,
with global normalized-degree pullback invariance. Also prove pullback
invariance of the related raw-degree local ratio. Definition 1.9(ii)'s displayed
quotient remains outside the formalized claim: its globally normalized numerator
is invariant while its local-degree denominator scales by the extension degree.
The foundational place/Finsupp model and
`normalizedArithmeticDivisorDegree_nonneg` match §3.2 exactly.

In the same commit, add these four proved challenge theorems to Solution by
project import/`#check` only and append their names to config, taking
`theorem_names` from one entry to five.

**Gate.** Check positive denominators and empty-index exclusions. Print axioms
for `weighted_average_eq`, both range identities,
`normalizedArithmeticDivisorDegree_nonneg`,
`sum_normalizedPacketWeight_eq_one`, and `rawLocalDegreeRatio_pullback`; run
the all-shared comparator signature check and all audits.

### P5 — Reviewed local-field feasibility/prototype gate

**Scope.** Do not add public formalization. Record exact mathlib v4.32.0 API
findings in `Plans/LocalFieldFeasibility.md`. Prototype in ignored
`.pi/probes/`:

1. an arbitrary finite-dimensional complete normed extension of `ℚ_[p]`;
2. its valuation ring, normalized order with `ord p = 1`, ramification/residue
   degrees, and local different;
3. a finite tensor product over `ℤ_[p]`, reduction, total quotient ring, and
   normalization;
4. power-series log/exp convergence on one required ball;
5. normalized additive Haar measure of the integer ring.

The report gives each item GO/NO-GO, exact imports/declarations tried, minimal
errors, and the proposed representation. Probe files stay ignored and are not
project imports.

**GO criterion.** All five items elaborate far enough to identify a proof route
without assuming their desired conclusions. Otherwise the verdict is NO-GO and
P6 is forbidden pending a reviewed scope/interface revision.

### P6 — Constructible mixed-characteristic local fields

**Scope.** Define `MixedCharLocalFieldData` with ambient finite extension,
valuation/ring, and standard compatibility laws only. Provide the required
constructor

```lean
mixedCharLocalFieldData_of_finiteExtension
```

for every finite-dimensional complete normed extension of `ℚ_[p]` admitted by
the P5 representation; callers do not supply `ord(p)=1`, positivity of `e`,
residue finiteness, or different compatibility. Add a degree-greater-than-one,
end-to-end concrete example that constructs the data and evaluates the ring of
integers, normalized order, ramification index, and different. A degree-one
`ℚ_[p]` example alone does not pass.

Also define fractional powers and `aParam`/`bParam` with exactly the challenge
formulas, and export `localParameters_eq_of_smallRamification`. Add that theorem
to Solution by import/`#check` only and append it to config, taking the count
from five to six.

**Gate.** Reviewer checks constructor universality for the chosen representation,
the nontrivial example, and the all-shared signature match for `aParam`,
`bParam`, and the parameter theorem. Failure is NO-GO, not permission to add
conclusion fields.

### P7 — Analytic prerequisite: local `p`-adic log and exp

**Scope.** In a separate prerequisite project/module, construct power-series
`padicLog` and `padicExp`, prove convergence on exact valuation balls, inverse
laws, image bounds, and the torsion-kernel statement needed later. No
`LogExpPackage` certificate is permitted.

**Gate.** Review strict versus non-strict radii, the `p = 2` branch, and print
axioms for both inverse laws. A failed prototype forces NO-GO/spec revision.

### P8 — Algebraic prerequisite: tensor normalization and Proposition 1.1

**Scope.** Define finite iterated tensor products over `ℤ_[p]`, reduction, total
quotient rings, and normalization. Prove the two-factor different inclusion,
induction, generator independence via fractional ideals, faithfully-flat
descent, and Proposition 1.1.

**Gate.** The distinguished exponent omits exactly one index. The proof uses the
actual constructor from P6 and contains no normalization/different inclusion as
a data field.

### P9 — Local differents prerequisite: Proposition 1.3

**Scope.** Develop tower-normalized different orders and prove the lower bound,
tame equality, and Galois upper bound of Proposition 1.3, including the
`p`-primary extension-degree exponent.

**Gate.** Check order normalization, tame hypotheses, and the Kummer/induction
argument. Print axioms for all three public estimates.

### P10 — Log lattices and Proposition 1.2

**Scope.** Use P7 and P8 to define unit-log lattices, prove the two local
inclusions and small-ramification equality, then prove the tensor inclusions and
parts (ii)–(iv) of Proposition 1.2. Automorphisms are explicit linear
equivalences preserving the log lattice. The P6 comparator parameter theorem
and config are unchanged.

**Gate.** Floors/ceilings and fractional exponents match the paper; no desired
inclusion is a structure field.

### P11 — Haar-volume prerequisite and Proposition 1.4

**Scope.** Construct normalized additive Haar log-volume for P6 fields; prove
integer-ring and `p`-scaling normalization, finite direct-sum/tensor laws,
torsion quotient contribution, and all parts of Proposition 1.4. Use the P3
project theorem for the first numerical sum bound and export
`nonarchimedean_secondError_sum_le` for the second. Add the latter to Solution
by import/`#check` only and append it to config, taking the count from six to
seven.

**Gate.** Check division by local degree, the exact `m/(ef)` term, both bounds in
1.4(iii), and the `3 + log e` term. Run the all-shared comparator signature
check and all audits.

### P12 — Archimedean metric estimates

**Scope.** Define `complexTensorToProd` and `complexPairNormSq` exactly as in
the challenge, then define the eight primitive real-linear isometries of `ℂ`;
prove the two-factor and finite tensor/direct-sum metric comparisons and
integral container statement of Proposition 1.5. Export the challenge
bijectivity and factor-two norm theorems. Add both to Solution by import/`#check`
only and append both names to config, taking the count from seven to nine.

**Gate.** Document squared-norm convention, factor `2^(|I|-1)`, number of
complex factors, and all primitive automorphisms. Run the all-shared comparator
signature check on both definitions and theorems.

### P13 — Conditional Proposition 1.6 statement

**Scope.** Add `PrimeCountingCertificate` with exactly the field in §2.3 and
state `proposition16_of_primeCountingCertificate` conditionally, including both
clauses and indexing `p₁ = 2`. PrimeNumberTheoremAnd is the known future
discharge path, but adding or adapting that dependency is out of scope. At most,
include trivial direct consequences of mathlib's existing Chebyshev theorem;
do not spend effort proving or sharpening an unconditional PNT-strength bound,
and do not call a weaker result Proposition 1.6.

**Gate.** Print every certificate field type and the conditional result's
axioms; the theorem visibly takes the certificate. Any unconditional
prime-counting lemma must be a direct consequence of an already available
mathlib theorem and remains separate. Record that the exact `4 / 3` constant,
not the Chebyshev coefficient, feeds P17. Do not add
`eventually_primeCounting_le_four_thirds` to Solution or config: the available
project theorem with that constant still takes `PrimeCountingCertificate`, while
the challenge target does not.

### P14 — Elliptic feasibility gate and honest Proposition 1.8 scope

**Scope.** First create ignored `.pi/probes/` files and a reviewed
`Plans/EllipticFeasibility.md` inventory for polarized abelian varieties, Tate
modules, moduli/level structures, descent, semi-abelian/Néron models, and inertia.
Then prove only feasible finite-group/linear-algebra lemmas. Record the exact
planned cases and fixed geometric conclusions for the §2.3 certificate family,
but do not define `ReductionUse D`, `D.reductionUses`, `ReductionCertificate D`,
or any other declaration indexed by `InitialThetaCarriers`; that carrier does
not exist until P15. Do not promise unconditional geometric Proposition 1.8
declarations.

**Gate.** Report GO only for each unconditional lemma actually prototyped.
Blueprint 1.8 lists the unconditional core separately and marks every geometric
clause conditional/partial. Review the planned certificate-case inventory
against Proposition 1.8; certificate field printing is deferred to P15.

### P15 — Data-only carriers, reduction family, five IUT interfaces, and statement signature gate

**Scope.** First add `IUT/Carriers.lean` with `InitialThetaCarriers` and the
fixed containers exactly as §2.2. Next add `Elliptic/Carriers.lean` and
`Elliptic/ReductionInterface.lean` with `ReductionUse D`,
`ReductionConclusion D`, `D.reductionUses`, `ReductionCertificate D`, and the
conditional wrappers exactly as §2.3. Only after those indexed declarations
elaborate, add `IUT/Interfaces.lean` with the five imported-IUT structures.
Add setup definitions for Theorem 1.10 and the proposition-valued
`ThetaPilotEstimateStatement`. Its signature is exactly:

```lean
def ThetaPilotEstimateStatement
    (D : InitialThetaCarriers)
    (data : InitialThetaData D)
    (shells : LogShellPacket D)
    (realization : ThetaPilotRealization D shells)
    (procession : ProcessionNormalization D shells realization)
    (cor312 : Corollary312Input D shells realization)
    (reduction : ∀ u : ReductionUse D, u ∈ D.reductionUses →
      ReductionCertificate D u)
    (primeCounting : PrimeCountingCertificate) : Prop :=
  -- exact CTheta upper bound and both final inequalities
```

No theorem proving this proposition is added yet.

**Required signature-level gate.** A tracked
`scripts/CheckFinalSignature.lean` imports the statement and contains an
`example` quantifying all eight displayed binders and checking the fully applied
proposition. The phase runs `#check @ThetaPilotEstimateStatement` and reviewers
must see, separately, the five IUT packages
`InitialThetaData`, `LogShellPacket`, `ThetaPilotRealization`,
`ProcessionNormalization`, `Corollary312Input`, plus the
`ReductionCertificate` family and `PrimeCountingCertificate` (seven conditional
packages total; `D` is their data-only carrier). Omitting or bundling any one is
a phase failure.

**Additional gate.** Run `#print` on each of the five structures and on every
reduction certificate field, and inspect the type of every field. Confirm
realization proposition fields are containments, there is no realization
log-volume upper bound, Corollary 3.12 has only its exact equality and
`-1 ≤ CTheta`, and normalized-weight sum is a theorem rather than a field.

### P16 — Local Θ-pilot bounds and procession averaging

**Scope.** Prove distinguished, unramified, and archimedean local bounds from
P11/P12 plus the exact containment fields. Prove weighted packet and procession
bounds from P4. Every declaration explicitly carries the relevant five IUT
arguments.

**Gate.** Local cases are exhaustive; weighted normalization uses the proved
weight theorem; imported containments are used only through explicit fields.

### P17 — Global arithmetic and constant tracking

**Scope.** Prove the different/conductor comparisons and (D0)–(D7)/(R1)–(R4)
consequences from the explicit finite `reduction` family. Prove the small-prime
sum from `proposition16_of_primeCountingCertificate primeCounting`. Track the
paper's constants `12`, `20`, `56`, `1/6`, and `10` through Step (viii).

**Gate.** `smallPrimeSum_bound` visibly takes `PrimeCountingCertificate` and the
different/conductor lemmas visibly take the reduction family. The unconditional
Chebyshev theorem is not substituted. Print axioms and rerun the P15 signature
fixture.

### P18 — Conditional Theorem 1.10

**Scope.** Prove

```lean
theorem logVolumeEstimatesForThetaPilotObjects
    (D : InitialThetaCarriers)
    (data : InitialThetaData D)
    (shells : LogShellPacket D)
    (realization : ThetaPilotRealization D shells)
    (procession : ProcessionNormalization D shells realization)
    (cor312 : Corollary312Input D shells realization)
    (reduction : ∀ u : ReductionUse D, u ∈ D.reductionUses →
      ReductionCertificate D u)
    (primeCounting : PrimeCountingCertificate) :
    ThetaPilotEstimateStatement D data shells realization procession cor312
      reduction primeCounting
```

using P16/P17 and `Corollary312Input.neg_one_le_CTheta`. Update blueprint links
without removing conditional/partial labels.

**Gate.** Run the P15 signature fixture for both the proposition and theorem.
`#print axioms` may show only reviewed standard logical axioms; all seven
conditional packages remain ordinary explicit arguments.

### P19 — Final coverage and reproducibility audit

**Scope.** Complete README/comparator documentation and all ten Verso chapters.
Generate the final site and declaration manifest. Record precisely which parts
are proved, conditional, and partial.

**Checks.** Clean root/nested builds; comparator; `scripts/audit_trust.sh`;
all-public `scripts/audit_axioms.sh`; headline `#print axioms` for each item and
Theorem 1.10; signature fixture; blueprint site; `git diff --check`; and ignored
status audit.

**Gate.** Only the challenge has reviewed placeholders: exactly ten, one for
each §3.2 target. Final config has the nine project-proved targets from §3.3;
the unconditional Proposition 1.6 target remains visibly out. No public helper
escapes the all-declaration audit; the all-shared signature diff is empty; a
clean checkout reproduces all products. The project is described as a
conditional Section 1 formalization while any IUT, prime-counting, or reduction
certificate remains.

## 6. Review log

The orchestrator appends one line per verdict. Old verdicts are not rewritten.

| Phase | Commit | Reviewer | Verdict | Date | Notes |
|---|---|---|---|---|---|
| P0 (round 1) | `957878c` | pi | CHANGES REQUESTED | 2026-07-19 | Duplicate comparator declarations, unavailable `4/3` prime API, omitted final inputs, loose interfaces, feasibility, and audit coverage required revision. |
| P0 (round 2) | `9b8c485` | pi | ACCEPTED | 2026-07-19 | All seven round-1 findings resolved; one non-blocking work-log wording note. P0 gate closed. |
| P1 (round 1) | `01a95ef` | pi | CHANGES REQUESTED | 2026-07-19 | PR workflow ran head code with write token; ignored-.pi audit bypass; missing λ domain in Prop 1.4 chapter. |
| P1 (round 2) | `51ab4b6` | pi | CHANGES REQUESTED | 2026-07-19 | Round-1 findings resolved; new: lean_action_ci.yml write/OIDC on PR job; symlink audit bypass. |
| P1 (round 3) | `22b8cb9` | pi | ACCEPTED | 2026-07-19 | CI permissions scoped; symlinks fail closed with permanent negative test. P1 gate closed. |
| P2 (round 1) | `3d4c5c0` | pi | ACCEPTED | 2026-07-19 | Challenge/Solution byte-identical payloads, isolated mathlib-only roots, exact config, literal single-line P2 audit exception. P2 gate closed. |
| P0 (user-directed amendment) | `20c7e3f` | project owner | DIRECTED AMENDMENT | 2026-07-19 | Replace the single-theorem comparator design by the mathlib-only Section 1 suite; keep challenge-only targets out of config; remove tracked machine-local repository references. |
| P3 (round 1) | `abe17b7` | pi | ACCEPTED | 2026-07-19 | Comparator theorem proved; solution re-export and signature script verified; proof-quality pass clean. P3 gate closed. |
| P0 amendment (round 1) | `20c7e3f` | pi | CHANGES REQUESTED | 2026-07-19 | Path audit specified but unimplemented; P14 used carriers introduced in P15; review-log hash placeholder. |
| P0 amendment (round 2) | `7329e2a` | pi | ACCEPTED | 2026-07-19 | Path audit implemented with negative test; carrier ordering fixed; amendment gate closed. |
| P3b (round 1) | `5730dab` | pi | ACCEPTED | 2026-07-19 | Ten-target suite faithful to §3.2 and the paper; all statements verified true; two cosmetic elaboration deviations logged. P3b gate closed. |
| P4 (round 1) | `696cc65`+`975b455` | pi | CHANGES REQUESTED | 2026-07-19 | Def 1.9(ii) normalization overclaim; pre-publication hygiene (README, LICENSE, stale statuses, dangling scaffold refs). |
| P4 (round 2) | `f2d37ba` | pi | ACCEPTED | 2026-07-19 | Def 1.9(ii) honestly relabeled raw-degree variant; publication hygiene complete. P4 gate closed; repository made public at this gate. |
| P0 (user-directed PNT/credential amendment) | `1b7aca9` | project owner | DIRECTED AMENDMENT | 2026-07-19 | Keep Proposition 1.6 conditional with PrimeNumberTheoremAnd as the out-of-scope discharge path (issue #6); add tracked-file credential-pattern rejection and a synthetic negative test. |
| P0 PNT/credential amendment (round 1) | `1b7aca9` | pi | ACCEPTED | 2026-07-19 | PNT scope and credential audit passed; the review-log self-reference is corrected in the P5 fix round. |
| P5 (round 1) | `adec501` | pi | CHANGES REQUESTED | 2026-07-19 | Items 1, 3, and 5 accepted; item 2 lacked a constructed normalized order and positivity proof, and item 4 proved no summability statement. P6 remained forbidden pending correction. |
| P5 (round 2) | `ade49ff` | pi | ACCEPTED | 2026-07-19 | Items 2 and 4 strengthened with constructed normalized order (ord(p)=1, 0<e) and genuine log/exp summability proofs for arbitrary finite extensions; reviewer concurs five-GO. P5 gate closed; P6 authorized. |
