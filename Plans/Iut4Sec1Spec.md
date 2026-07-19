# IUT IV Section 1: phase-gated implementation specification

Date: 2026-07-19

## 1. Objective and source of truth

Formalize Section 1, “Log-volume Estimates,” of Mochizuki’s *Inter-universal
Teichmüller Theory IV* (`references/iut4.pdf`, pp. 9–39 of the paper), covering
Propositions 1.1–1.8, Definition 1.9, and Theorem 1.10. The repository must also
contain a Verso blueprint and a `leanprover/comparator` challenge/solution pair.

The mathematical source of truth is the paper, checked against
`references/iut4-section1.txt`; `references/iut4.txt` is only a searchable
extraction. The finished `proetale` project at
`/Users/dagur/leanprojects/anabelian/.lake/packages/proetale` is the repository
shape to copy for Verso and comparator infrastructure.

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
* The unconditional Chebyshev-strength prime-counting bound in §2.3. The exact
  `4 / 3` result of Proposition 1.6 is conditional for the reason stated there.
* The finite-group and linear-algebra lemmas isolated from Proposition 1.8.
  Elliptic/abelian geometry outside current mathlib is conditional under §2.3.
* Definition 1.9 and all elementary assembly in Theorem 1.10 after every
  interface/certificate argument has been supplied.

A helper structure may package ambient operations and their standard laws. It
may not contain an advertised proposition under another name.

### 2.2 Imported-IUT interfaces: exact signatures

There are exactly five imported-IUT structures. Their ambient carriers and all
containers are defined first in `Iut4Sec1/IUT/Carriers.lean`; the interfaces in
`Iut4Sec1/IUT/Interfaces.lean` do not get to choose them. In particular:

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

This is a clearly named external, non-IUT assumption. Proposition 1.6 is proved
as `proposition16_of_primeCountingCertificate`; its `n₀`, `ηprm`, exact
`4 / 3` nth-prime bound, and exact `4 / 3` prime-counting bound are derived from
`PrimeCountingCertificate.pnt`, rather than stored as certificate fields.

The same phase also proves an unconditional theorem
`eventually_primeCounting_le_logFour_add` directly from
`Chebyshev.eventually_primeCounting_le`, for a specified positive rational
`ε` (initially `1 / 100`). This is real proved mathematics but is not substituted
for Proposition 1.6 and is not used to claim the paper's exact statement.

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

`Iut4Sec1/Elliptic/ReductionInterface.lean` may therefore define a family

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
* `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` defines integral and
  minimal Weierstrass equations and good reduction. The abelian-variety,
  moduli/descent, semi-abelian/Néron, Tate-module, and inertia APIs listed in
  §2.3 were not found.

## 3. Comparator core and justification

The comparator core is the finite-sum ramification-error estimate used in
Proposition 1.4(iii):
`Iut4Sec1.nonarchimedean_logError_sum_le`.

```lean
noncomputable def nonarchimedeanLogError (p e : ℕ) : ℝ :=
  ((⌈(e : ℝ) / (p - 2 : ℕ)⌉ : ℤ) : ℝ) / e - 1 / e

theorem nonarchimedean_logError_sum_le {ι : Type*} [DecidableEq ι]
    (p : ℕ) (I Istar : Finset ι) (e : ι → ℕ)
    (hp : p.Prime) (hp2 : 2 < p) (hIstar : Istar ⊆ I)
    (he : ∀ i ∈ I, 0 < e i)
    (hsmall : ∀ i ∈ I, i ∉ Istar → e i ≤ p - 2) :
    ∑ i ∈ I, nonarchimedeanLogError p (e i) ≤
      4 * (Istar.card : ℝ) / p := by
  sorry
```

The final line is present only in `Comparator/Challenge.lean`. For the pointwise
bound put `d = p - 2 > 0`. Positivity of `e` gives
`ceil (e / d) - 1 < e / d`, hence the error is `< 1 / d ≤ 4 / p` for
`p ≥ 3`. If `e ≤ d`, then `0 < e / d ≤ 1`, so the ceiling is exactly `1` and
the error is zero. This covers `e = 1`, `e = p - 1`, and arbitrarily large `e`.
Summing over the complement of the small indices gives the stated estimate.

This is the self-contained arithmetic core of Proposition 1.4(iii), not the
overall mathematical headline of Section 1. The challenge imports `Mathlib`
only.

Comparator configuration:

* challenge module: `Challenge`;
* solution module: `Solution`;
* theorem: `Iut4Sec1.nonarchimedean_logError_sum_le`;
* permitted axioms: at most `propext`, `Quot.sound`, and `Classical.choice`,
  reduced if the final audit permits fewer.

The challenge permanently keeps its independent copied declaration. The
solution keeps a copied declaration only in P2, while the project declaration
does not exist. P3 adds the project theorem and, in the same phase, replaces the
solution copy by a module that only imports/re-exports the project theorem. No
phase imports or declares two constants with the same name in one environment.

## 4. Repository conventions, trust audit, and phase gates

* Work directly on `main`, one reviewed phase-sized commit at a time, with
  message `P<n>: <summary>`. Do not push unless instructed.
* Every phase ends with `lake build` and `git diff --check`. Blueprint phases
  also build and generate the site.
* Keep `Iut4Sec1.lean` as the import root and update it with each public module.
* Do not commit `.lake/`, `.pi/`, `blueprint-verso/.lake/`, or generated
  `blueprint-verso/_out/`.
* `Comparator/Challenge.lean` has the sole reviewed placeholder exception: one
  occurrence of `sorry` in the challenge theorem. There are no other reviewed
  exceptions unless a later review records an exact file, line, token, and
  reason. In particular, the initial reviewed-exception list for `axiom`,
  `constant`, `admit`, `native_decide`, `Lean.ofReduceBool`, `ofReduceBool`,
  `implemented_by`, and `unsafe` is empty.
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
that this file has exactly one `sorry` occurrence and none of the other rejected
tokens. It fails on an untracked Lean file as well, except ignored `.pi/` probe
files during a feasibility phase. Any future exception is a literal allow-list
entry `(path, line, token, reason)` reviewed in the phase that introduces it;
glob or directory exceptions are forbidden.

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

**Checks.**

```bash
lake env lean Iut4Sec1/Basic.lean
lake build Iut4Sec1
lake build
printf 'import Iut4Sec1.Basic\n#print axioms hello\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
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
`scripts/AuditAxioms.lean`, and `scripts/audit_axioms.sh` exactly as §4 specifies.
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

### P4 — Finite combinatorics and Definition 1.9 foundations

**Scope.** Prove Proposition 1.7, (E1)/(E2), positive raw-weight arithmetic, and
normalized weights in `Combinatorics/`. Define finite-support arithmetic
divisors, support, effectiveness, degree, normalized degree, pullback, parts,
and normalized local degree in `Global/`, with pullback invariance.

**Gate.** Check positive denominators and empty-index exclusions. Print axioms
for `weighted_average_eq`, `sum_normalizedPacketWeight_eq_one`, and
`normalizedLocalDegree_pullback` and run all audits.

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

Also define fractional powers and `aParam`/`bParam` with the elementary
small-ramification identities.

**Gate.** Reviewer checks constructor universality for the chosen representation
and the nontrivial example. Failure is NO-GO, not permission to add conclusion
fields.

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
equivalences preserving the log lattice.

**Gate.** Floors/ceilings and fractional exponents match the paper; no desired
inclusion is a structure field.

### P11 — Haar-volume prerequisite and Proposition 1.4

**Scope.** Construct normalized additive Haar log-volume for P6 fields; prove
integer-ring and `p`-scaling normalization, finite direct-sum/tensor laws,
torsion quotient contribution, and all parts of Proposition 1.4. Use the P3
project theorem for the first numerical sum bound. The comparator solution is
already only a re-export and is unchanged.

**Gate.** Check division by local degree, the exact `m/(ef)` term, both bounds in
1.4(iii), and the `3 + log e` term. Run comparator and all audits.

### P12 — Archimedean metric estimates

**Scope.** Define the eight primitive real-linear isometries of `ℂ`; prove the
two-factor and finite tensor/direct-sum metric comparisons and integral
container statement of Proposition 1.5.

**Gate.** Document squared-norm convention, factor `2^(|I|-1)`, number of
complex factors, and all primitive automorphisms.

### P13 — Conditional Proposition 1.6 plus unconditional Chebyshev theorem

**Scope.** Add `PrimeCountingCertificate` with exactly the field in §2.3. Derive
`proposition16_of_primeCountingCertificate`, including both clauses and indexing
`p₁ = 2`. Independently prove
`eventually_primeCounting_le_logFour_add` from the exact mathlib theorem using
`ε = 1 / 100` (or another reviewed explicit positive rational). Do not call the
weaker result Proposition 1.6.

**Gate.** Print every certificate field type; print axioms for both results; the
conditional theorem visibly takes the certificate. Record that the exact
`4 / 3` constant, not the Chebyshev coefficient, feeds P17.

### P14 — Elliptic feasibility gate and honest Proposition 1.8 scope

**Scope.** First create ignored `.pi/probes/` files and a reviewed
`Plans/EllipticFeasibility.md` inventory for polarized abelian varieties, Tate
modules, moduli/level structures, descent, semi-abelian/Néron models, and inertia.
Then prove only feasible finite-group/linear-algebra lemmas. Define the exact
`ReductionUse` type, fixed conclusion predicate, finite `D.reductionUses` set,
`ReductionCertificate`, and conditional wrappers from §2.3. Do not promise unconditional geometric
Proposition 1.8 declarations.

**Gate.** Report GO only for each unconditional lemma actually prototyped.
Blueprint 1.8 lists the unconditional core separately and marks every geometric
clause conditional/partial. Print every certificate field type.

### P15 — Exact five IUT interfaces and statement signature gate

**Scope.** Add `IUT/Carriers.lean` and `IUT/Interfaces.lean` exactly as §2.2.
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

**Additional gate.** Run `#print` on each of the five structures and inspect the
type of every field. Confirm realization proposition fields are containments,
there is no realization log-volume upper bound, Corollary 3.12 has only its
exact equality and `-1 ≤ CTheta`, and normalized-weight sum is a theorem rather
than a field.

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

**Gate.** Only the challenge has its one reviewed placeholder; no public helper
escapes the all-declaration audit; a clean checkout reproduces all products.
The project is described as a conditional Section 1 formalization while any IUT,
prime-counting, or reduction certificate remains.

## 6. Review log

The orchestrator appends one line per verdict. Old verdicts are not rewritten.

| Phase | Commit | Reviewer | Verdict | Date | Notes |
|---|---|---|---|---|---|
| P0 (round 1) | `957878c` | pi | CHANGES REQUESTED | 2026-07-19 | Duplicate comparator declarations, unavailable `4/3` prime API, omitted final inputs, loose interfaces, feasibility, and audit coverage required revision. |
