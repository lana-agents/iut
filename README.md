# iut

Inter-universal Teichmüller theory: the ABC/IUT trunk.

This repository holds the IUT-specific material — the parts of the programme that are
particular to Mochizuki's papers rather than independently established mathematics.
It does **not** verify IUT.

It carries two strands:

* **IUT4 §1 — "Log-volume Estimates."** A Lean 4 formalization of the self-contained
  mathematics in Section 1 of *Inter-universal Teichmüller Theory IV*. Merged here from
  `LANA-Project/iut4-sec1` with its history.
* **The Corollary 3.12 variant.** A project-owner-specified variant of IUT III,
  Corollary 3.12: initial Θ-data (IUT I, Definition 3.1), processions and tensor-packets
  of log-shells, the large volume container, its log-volume, and the holomorphic hull.
* **The implication to ABC.** The proof that the Corollary 3.12 variant implies the ABC
  conjecture, via IUT IV §1 (Theorem 1.10, the `Iut4Sec1` strand) and §2 (Corollaries
  2.2 and 2.3, using [`LANA-Project/genl`](https://github.com/LANA-Project/genl)).
  Tracked as taxis [#1449](https://taxis.lana.merten.dev/issues/1449); the main theorems
  are `Iut.cor312Variant_implies_abc`, `Iut.cor312Variant_implies_abc_concrete`,
  `Iut.cor312Variant_implies_abc_curves` and `Iut.Anabelian.cor312Variant_implies_abc_model`.
* **The anabelian model.** A concrete model of the anabelian interface behind the
  Θ-data (`Iut/Anabelian/`): orbicurves as elliptic curves with level data, cusps as
  torsion quotients, the bad-place predicates from minimal Weierstrass models, and a
  proof that the anabelian part of initial Θ-data exists (IUT I, Definition 3.1(d)–(f);
  taxis [#276](https://taxis.lana.merten.dev/issues/276),
  [#279](https://taxis.lana.merten.dev/issues/279),
  [#1469](https://taxis.lana.merten.dev/issues/1469)). Fundamental groups remain
  explicit residual interfaces.

Mochizuki's *Arithmetic Elliptic Curves in General Position* is **not** developed here;
it lives in [`LANA-Project/genl`](https://github.com/LANA-Project/genl).

## Honesty boundary

Claims imported from IUT I–III, and mathematical infrastructure unavailable in Mathlib,
are kept behind explicit interfaces or certificates rather than introduced as axioms or
hidden inside helper structures. See the [implementation specification and honesty
boundary](Plans/Iut4Sec1Spec.md#2-honesty-boundary).

The certificate interfaces are discharged in separate repositories, so that this one
states its results conditionally:

* [`padic-log-volume`](https://github.com/lana-agents/padic-log-volume) — `p`-adic
  log/exp and normalized Haar log-volume.
* [`elliptic-reduction`](https://github.com/lana-agents/elliptic-reduction) — the
  `ReductionCertificate` for Proposition 1.8(v)–(vii).
* [`prime-counting`](https://github.com/lana-agents/prime-counting) — the
  `PrimeCountingCertificate` for Proposition 1.6.

The Corollary 3.12 strand is a **specification / formal-statement project only**. Proving
the resulting proposition is explicitly out of scope. The formalisation must not silently
identify the variant with Mochizuki's published Corollary 3.12, and must not encode any
disputed implication as a proved theorem. Every assumption and specification boundary
should be visible in the types. The intended statement will differ in some respects from
the formulation printed in the IUT papers; the precise data, hypotheses, definitions and
conclusion are supplied per-issue by the project owner.

## Current scope (IUT4 §1)

The library proves the real-arithmetic error bound used in Proposition 1.4(iii), the
finite weighted-average identity of Proposition 1.7, the elementary range identities
(E1)/(E2), positive finite packet-weight normalization, and the finite-support
arithmetic-divisor foundations of Definition 1.9(i), including normalized global-degree
invariance under pullback.

It also proves a related raw-degree local-ratio invariance theorem. It does **not** claim
Definition 1.9(ii)'s displayed globally normalized quotient: under the implemented
pullback, that numerator is invariant while its local-degree denominator scales by the
extension degree. The blueprint labels this boundary explicitly.

Later Section 1 results remain planned, partial, or conditional as recorded in the
specification. In particular, IUT I–III inputs, the exact prime-counting coefficient
unavailable in the pinned Mathlib release, and missing elliptic or reduction
infrastructure must appear as ordinary theorem arguments when used.

## Corollary 3.12 variant strand (`Iut`)

The `Iut` library states the project-owner-specified variant of IUT III,
Corollary 3.12 (taxis [#33](https://taxis.lana.merten.dev/issues/33)):
`Iut.Corollary312Variant` in [`Iut/Cor312/Statement.lean`](Iut/Cor312/Statement.lean),
a `Prop`-valued definition `−|log(q)| ≤ −|log(Θ)|` that is deliberately left without
proof and without axiom. The stack beneath it:

* **Initial Θ-data** (IUT I, Definition 3.1; taxis #38–#42):
  [`Iut/Cor312/ThetaData/`](Iut/Cor312/ThetaData). Reduction predicates, the field of
  moduli `ℚ(j)`, torsion rationality, the mod-`ℓ` representation pinned to the genuine
  Galois action on `E(F̄)[ℓ]`, and the `ℓ`-torsion field `K` are real Mathlib content;
  orbicurves, fundamental groups and tempered groups enter through the explicit
  interfaces `Iut.AnabelianGeometry` / `Iut.TemperedGeometry` (seams for taxis #7, #10,
  #11, #13; discharge tracked in #276, #279). Bad-place Tate `q`-parameters come from
  [`tate-curves-theta`](https://github.com/lana-agents/tate-curves-theta) (taxis #37).
* **The large volume container, log-volume, and holomorphic hull** (taxis #43–#45):
  [`Iut/Cor312/Container.lean`](Iut/Cor312/Container.lean),
  [`LogVolume.lean`](Iut/Cor312/LogVolume.lean),
  [`HolomorphicHull.lean`](Iut/Cor312/HolomorphicHull.lean) and neighbours. Interface
  amendments made for the concrete instantiation: packet summands are commutative rings
  ([`Iut/Implication/Theorem110.lean`]he tensor products of local fields are products of fields), integral structures are
  sets (the archimedean one is the unit ball), and the packet-volume combination law is
  stated for nonempty components.
* **LHS/RHS** (taxis #34/#35): `−|log(q)|` from the bad-place `q`-orders with the
  `(1/2ℓ)` normalization recorded in IUT IV, and the procession-normalized log-volume of
  the holomorphic hull of the theta-pilot region.

### Concrete instantiation of the inputs (`Iut/Concrete/`)

Every input of the variant except the anabelian interfaces is now given a concrete
implementation, with the standard mathematics it needs isolated in explicit structures
whose fields are the target statements of the sibling projects:

* [`LocalTheory.lean`](Iut/Concrete/LocalTheory.lean) — `Iut.LocalTheory K`: the
  local-field theory of the tensor packets `⊗_j K_{v_j}` of a number field (integral
  structures, log-shells, normalized Haar log-volume, least hull regions, the
  indeterminacy automorphisms of IUT IV Proposition 1.2, and Propositions 1.4(iii),(iv),
  1.5(iii),(iv)). Ramification indices, residue degrees, weights, `ord_p` and the
  different exponents are defined from Mathlib. Delegated to
  [`padic-log-volume`](https://github.com/lana-agents/padic-log-volume) (taxis #4, #278).
* [`Container.lean`](Iut/Concrete/Container.lean) — the container, log-volume data
  (weights `[K_v : ℚ_p]/[K : ℚ]` summing to `1`) and hull system, all proved from
  `LocalTheory`.
* [`ThetaRegion.lean`](Iut/Concrete/ThetaRegion.lean) — `Iut.ThetaLocalData` (the
  `2ℓ`-th roots of the Tate parameters at the bad places of `K`; delegated to
  `tate-curves-theta`), the **concrete theta-pilot region**: the union over the
  indeterminacy automorphisms of the images of `q_{v_j}^{j²}·(R_I)^∼` (IUT IV, Step (v)),
  the concrete `q`-pilot data (`Iut.QPilotInputs`: finiteness of the bad locus, residue
  degrees positive), and `Iut.concreteVariantData`, the assembled bundle.
* [`Invariants.lean`](Iut/Concrete/Invariants.lean) — the Theorem 1.10 invariants of the
  tower `F_mod ⊆ F_tpd ⊆ F ⊆ K` defined from Mathlib: the tripodal field
  `F_tpd = ℚ(j, E[2])`, the normalized different degree `log N(𝔡_L)/[L : ℚ]`, the
  conductor degree, the distinguished primes and `log(d^K_p)`; the tower facts (R4),
  Steps (ii), (iii) form the `Prop`-structure `Iut.TowerArithmetic` (elliptic-reduction).
* [`Existence.lean`](Iut/Concrete/Existence.lean) — **initial Θ-data from an elliptic
  curve**: `Iut.EllipticCurveData.thetaData` builds IUT I, Definition 3.1 data for
  `(E/F, ℓ)` with `V_mod^bad` the places of `F_mod` not over `2ℓ` with multiplicative
  reduction, from `CurveArithmetic` (Prop 1.8 and places of `F/F_mod`), `TateInputs`,
  `ModEllRepData ℓ` and the anabelian existence `Iut.AnabelianExistence`; the local height
  data of the curve; `Iut.CurveInputs` (the inputs of Corollary 2.2 in terms of the curves
  of the points), from which `ConcreteThetaDataExistence` is *proved*.

## Implication strand (`Iut/Implication`, `Iut/Concrete`)

The proof that the Corollary 3.12 variant implies ABC, along IUT IV
(taxis [#1449](https://taxis.lana.merten.dev/issues/1449)). Main theorems, all
sorry-free with standard axioms only:

* `Iut.Theorem110Invariants.theorem110`
  ([`Iut/Implication/Theorem110.lean`](Iut/Implication/Theorem110.lean)) — IUT IV,
  Theorem 1.10, `(1/6)·log(q) ≤ (1 + 20·d_mod/ℓ)·(log d_{F_tpd} + log f_{F_tpd}) +
  20·(e*_mod·ℓ + η_prm)`, from the variant, the local estimates of Steps (iv)–(vii), the
  arithmetic certificate of Steps (ii)–(iii), and the prime-counting bound of
  Proposition 1.6. The procession average (E1), (E2) and the constant tracking of
  Step (viii) are proved.
* `Iut.LocalHeightData.exists_prime_selection`
  ([`PrimeSelection.lean`](Iut/Implication/PrimeSelection.lean)) — Proposition 2.1(ii)
  and the choice of the prime `ℓ` with (P1)–(P3), from Chebyshev bounds.
* `Iut.Corollary22Inputs.c2` ([`Corollary22.lean`](Iut/Implication/Corollary22.lean)) —
  Corollary 2.2(ii),(iii): the inequality (C2) with `ε_E ≤ 1` outside a finite set,
  including the arguments for (P4), (P5) at large height.
* `Iut.cor312Variant_implies_abc` ([`Corollary23.lean`](Iut/Implication/Corollary23.lean))
  — Corollary 2.3 and ABC, via genl's Theorem 2.1 (ii) ⇒ (i).
* `Iut.cor312Variant_implies_abc_concrete` ([`Iut/Concrete/Main.lean`](Iut/Concrete/Main.lean))
  — the same with the variant assumed only for the concrete data bundles, and the local
  estimates of Theorem 1.10 *derived* for the concrete theta-pilot region
  ([`LocalEstimate.lean`](Iut/Concrete/LocalEstimate.lean): Propositions 1.4/1.5, the
  weighted average of Proposition 1.7, and (R4)).
* `Iut.cor312Variant_implies_abc_curves` ([`Iut/Concrete/Existence.lean`](Iut/Concrete/Existence.lean))
  — the same with the existence of initial Θ-data *proved* from the curves of the points
  and the standard providers; the only IUT-theoretic hypothesis left is
  `Iut.AnabelianExistence`.

The ABC target is `Iut.ABC T := T.StatementI` ([`Iut/Abc/Target.lean`](Iut/Abc/Target.lean)),
[GenEll] Theorem 2.1(i) for a height formalism `T` of
[`LANA-Project/genl`](https://github.com/LANA-Project/genl); the concrete height theory is
taxis #1452.

Remaining explicit inputs of the main theorem `Iut.cor312Variant_implies_abc_curves`,
each a structure whose fields are precise target statements (see the taxis issues linked
from #1449):

| Input | Content | Owner |
| --- | --- | --- |
| `Iut.LocalTheory K` | tensor packets, log-shells, Haar log-volume, hulls, Props 1.4/1.5 | padic-log-volume, [#1462](https://taxis.lana.merten.dev/issues/1462) |
| `Iut.ThetaLocalData D LT` | `2ℓ`-th roots of the Tate parameters, `q`-degree base change | tate-curves-theta, [#1464](https://taxis.lana.merten.dev/issues/1464) |
| `Iut.TowerArithmetic D LT TL` | (R4), Steps (ii), (iii) of Theorem 1.10 for the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K` | elliptic-reduction, [#1493](https://taxis.lana.merten.dev/issues/1493) (Prop 1.3: [#1463](https://taxis.lana.merten.dev/issues/1463)) |
| `Iut.PrimeCountingBound`, `Iut.ChebyshevBound` | Propositions 1.6, 2.1(ii) | prime-counting, [#1466](https://taxis.lana.merten.dev/issues/1466) |
| `Iut.CurveInputs T K d`, `Genl.HeightTheory.ProofPackage` | the curves `E_x/F_x` of the points with [GenEll] §§1, 3, Theorem 2.1 inputs; [CanLift] Prop 2.7 | genl, [#1467](https://taxis.lana.merten.dev/issues/1467) |
| `EllipticCurveData.CurveArithmetic` | Prop 1.8: `√−1`, stable reduction, `E[6]` rational, `F/F_mod`, reduction type over `F_mod`, finiteness of the bad locus | elliptic-reduction, [#1495](https://taxis.lana.merten.dev/issues/1495); places of `F/F_mod`: [#1494](https://taxis.lana.merten.dev/issues/1494) |
| `EllipticCurveData.TateInputs` | Tate parameters at the multiplicative places | tate-curves-theta, [#1496](https://taxis.lana.merten.dev/issues/1496) |
| `EllipticCurveData.ModEllRepData ℓ` | the mod-`ℓ` representation on `E[ℓ]` | [#277](https://taxis.lana.merten.dev/issues/277) |
| `Iut.AnabelianExistence AG TG` | IUT I, Definition 3.1(d)–(f): `C̲_K`, `ε`, `V` and the bad-place conditions | **proved** for the anabelian model (`Iut.Anabelian.anabelianExistence`), see below |

## Anabelian model strand (`Iut/Anabelian`)

The interfaces `Iut.AnabelianGeometry` and `Iut.TemperedGeometry` behind the Θ-data are
instantiated by a **linear-algebraic model** (taxis
[#276](https://taxis.lana.merten.dev/issues/276),
[#279](https://taxis.lana.merten.dev/issues/279)):

* [`Model.lean`](Iut/Anabelian/Model.lean) — model orbicurves `(E, ℓ, M, ±)` standing for
  `(E/M) ∖ (E[ℓ]/M)` and its `±`-quotient (the only shapes IUT I, Definition 3.1 uses);
  covers induced by `[n]`, base change, cusps `E(k)[ℓ]/M` (mod `±`), the rank-one
  quotient, the `±`-quotient cartesian squares, the types `(1, ℓ-tors)`,
  `(1, ℓ-tors)^±`; and the residual interface `Iut.Anabelian.EtalePi1Theory` (étale
  fundamental groups, open immersions, cores).
* [`Local.lean`](Iut/Anabelian/Local.lean) — over a valued field: the kernel of
  reduction and the **graph line** `E(k)[ℓ] ∩ E₁(k)` (= `μ_ℓ` under Tate
  uniformization), the **canonical generators** `q^{±1/ℓ}` of the graph quotient
  (`ℓ·v(x(P)) = -v(j)` in minimal models), split multiplicative reduction, the type
  `(1, ℤ/ℓℤ)^±`, theta-root models and the canonical graph cusp.
* [`Geometry.lean`](Iut/Anabelian/Geometry.lean) — the terms `Iut.Anabelian.modelAG` and
  `Iut.Anabelian.modelTG` (with the residual `TemperedPi1Theory`).
* [`Torsion.lean`](Iut/Anabelian/Torsion.lean), [`Linear.lean`](Iut/Anabelian/Linear.lean),
  [`Existence.lean`](Iut/Anabelian/Existence.lean) — the ℓ-torsion is rational over
  `K = F(E[ℓ])`; `SL₂(𝔽_ℓ)` acts transitively on (line, generator of the quotient) pairs;
  **`Iut.Anabelian.anabelianExistence`**: `C̲_K = (E_K, ℓ, ⟨e₁⟩, ±)`, `ε = e₂ mod ⟨e₁⟩`,
  and at each bad place a place of `K` chosen through `SL₂(𝔽_ℓ)` so that the graph line
  is `⟨e₁⟩` and the canonical generators are `±e₂` — the mechanism of (P7) in the proof
  of IUT IV, Corollary 2.2. The final theorem is
  `Iut.Anabelian.cor312Variant_implies_abc_model`.
* [`PlacesOver.lean`](Iut/Cor312/ThetaData/PlacesOver.lean),
  [`TateStructure.lean`](Iut/Cor312/ThetaData/TateStructure.lean),
  [`TateFamily.lean`](Iut/Cor312/ThetaData/TateFamily.lean),
  [`TateTorsion.lean`](Iut/Anabelian/TateTorsion.lean),
  [`LocalInputs.lean`](Iut/Anabelian/LocalInputs.lean) — the arithmetic inputs of the
  existence proof, all proved: places of `K` over `F_mod`, the Galois action on places and
  decomposition groups; and, from the Tate uniformizations carried by the Θ-data
  (`InitialThetaData.tate`: Tate parameter, model change, uniformization pinned by the
  coordinates of the Tate parametrization, Galois-equivariant), the ℓ-torsion of the Tate
  curve (`|E(K_w)[ℓ]| ≤ ℓ²`, graph line = kernel of the residue homomorphism to `ℤ/ℓℤ`,
  canonical generators `±q^{1/ℓ}`), hence the rationality of the local ℓ-torsion, the
  graph line of order `ℓ` and the canonical cosets at the bad places.

Interface amendments made for this (recorded on taxis #1453): the "lies over" relation on
finite places is the prime-ideal relation (the absolute-value form of the delivered
statement was only satisfiable at unramified split primes); `IsTypeOneZModPM`,
`IsThetaRootModel` and `canonicalGraphCusp` take a Tate structure on the local orbicurve
over a complete rank-one valued field, and the local theta data carry the chosen Tate
structures (`tateX`, `tateC`); the Θ-data carry the Tate uniformizations at the places of
the torsion field (`InitialThetaData.tate`).

Residual interfaces of the model, each an explicit structure:

| Input | Content | Owner |
| --- | --- | --- |
| `Iut.Anabelian.EtalePi1Theory` | étale `π₁` of the model orbicurves, open immersions for covers, `k`-cores and their stability | anabelian geometry, [#1527](https://taxis.lana.merten.dev/issues/1527) (#276, #10) |
| `Iut.Anabelian.TemperedPi1Theory` | tempered `π₁` with the comparison to the étale `π₁` | tempered-fundamental-groups, [#1528](https://taxis.lana.merten.dev/issues/1528) (#7) |
| `CurveInputs.tateFamily` (`Iut.TateFamily`) | Galois-equivariant Tate uniformizations of `E_x` over the completions of its ℓ-torsion field at the bad places (Tate's theorem) | tate-curves-theta, [#1582](https://taxis.lana.merten.dev/issues/1582) |

## Comparator suite

[`Comparator/Challenge.lean`](Comparator/Challenge.lean) states ten selected mathlib-only
targets from Section 1. Five currently have project proofs, are re-exported by
`Comparator/Solution.lean`, and are configured for `leanprover/comparator`. The exact
target list and inclusion policy are in [`Comparator/README.md`](Comparator/README.md).

## Blueprint

The Verso blueprint can be served locally with:

```bash
cd blueprint-verso
lake exe vbp build --serve
```

## Libraries

| Library | Contents |
| --- | --- |
| `Iut` | Corollary 3.12 variant, its concrete instantiation, and the implication to ABC |
| `Iut4Sec1` | IUT IV, Section 1 |
| `Challenge` / `Solution` | Comparator suite roots (separate environments) |

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.

## Build and audits

Install [elan](https://github.com/leanprover/elan); it selects the Lean version pinned by
`lean-toolchain`. Then run from the repository root:

```bash
lake exe cache get
lake build
./scripts/check_comparator_signature.sh
./scripts/audit_trust.sh
./scripts/audit_axioms.sh
git diff --check
```

The challenge contains the suite's reviewed proof placeholders. Public project modules and
the Solution re-exports are checked separately by the trust and axiom audits.

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to check that
a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is imported
  ([`Iut/Implication/Theorem110.lean`]mk_all --check`, for both `Iut` and `Iut4Sec1`), and that everything builds with
  warnings as errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#1](https://taxis.lana.merten.dev/issues/1) (programme umbrella); implication strand [#1449](https://taxis.lana.merten.dev/issues/1449): [#3](https://taxis.lana.merten.dev/issues/3), [#1451](https://taxis.lana.merten.dev/issues/1451), [#1453](https://taxis.lana.merten.dev/issues/1453), [#1454](https://taxis.lana.merten.dev/issues/1454), [#1455](https://taxis.lana.merten.dev/issues/1455); statement strand: [#33](https://taxis.lana.merten.dev/issues/33), [#34](https://taxis.lana.merten.dev/issues/34), [#35](https://taxis.lana.merten.dev/issues/35), [#38](https://taxis.lana.merten.dev/issues/38), [#39](https://taxis.lana.merten.dev/issues/39), [#40](https://taxis.lana.merten.dev/issues/40), [#41](https://taxis.lana.merten.dev/issues/41), [#42](https://taxis.lana.merten.dev/issues/42), [#43](https://taxis.lana.merten.dev/issues/43), [#44](https://taxis.lana.merten.dev/issues/44), [#45](https://taxis.lana.merten.dev/issues/45); interface-discharge issues: [#276](https://taxis.lana.merten.dev/issues/276) (anabelian interface), [#277](https://taxis.lana.merten.dev/issues/277) (mod-ℓ torsion and representation), [#278](https://taxis.lana.merten.dev/issues/278) (container/log-volume/hull instantiation), [#279](https://taxis.lana.merten.dev/issues/279) (étale theta, anabelian side)
