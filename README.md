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
  [#1469](https://taxis.lana.merten.dev/issues/1469)). The existence theorem has no
  residual input: fundamental groups and cores are not represented in the interfaces
  (see "Honesty boundary").

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

**Anabelian components of the Θ-data.** The conditions of IUT I, Definition 3.1(d)–(e)
that involve fundamental groups and cores — that `X_K` (equivalently `C̲_K`) admits a
`K`-core, and the profinite étale and tempered fundamental groups of the orbicurves with
their comparison maps and the open immersions attached to the covering diagrams — are
**not** represented in `Iut.AnabelianGeometry` / `Iut.TemperedGeometry`. The reason is
that the statement of the variant (`Iut.Corollary312Variant` and the data it reads) never
consults them: the Θ-data record (`Iut.InitialThetaData`) carries only their combinatorial
consequences at the level of `ℓ`-torsion — the orbicurve types `(1, ℓ-tors)`,
`(1, ℓ-tors)^±`, `(1, ℤ/ℓℤ)^±`, the cartesian covering diagrams, the cusps and the
rank-one quotient, the theta-root models and the canonical graph cusps. Consequently the
variant hypothesis `h312` of the main theorems is quantified over a **larger class of
data** than the printed corollary (data that need not satisfy the core and
fundamental-group conditions); this is a stronger hypothesis, so the implication to ABC
still holds, and the class of data on which the variant is assumed is visible in the
types. Accordingly, no exceptional set of points (the four `j`-invariants of [CanLift],
Proposition 2.7, whose once-punctured curve has no core) appears in the Corollary 2.2
inputs, and the existence of the anabelian part of the Θ-data
(`Iut.Anabelian.anabelianExistence`) is a theorem without residual input.

**Reduction predicates and the cyclic-subgroup bound.** `HasGoodReductionAt`,
`HasMultiplicativeReductionAt`, `HasSplitMultiplicativeReductionAt` and
`HasStableReductionAt` (`Iut/Cor312/ThetaData/GlobalField.lean`) are stated up to a global
change of variables: Mathlib's reduction classes refer to the given Weierstrass model (they
assert its minimality), whereas IUT I, Definition 3.1(a) is a property of the curve. With
the model-bound form, stable reduction everywhere is false for the Legendre models of the
tripod points. Likewise the cyclic-subgroup bound of [GenEll] Lemma 3.5 (`cyclic_bound` in
`Corollary22Inputs`, `CurveInputs`) is stated for primes `ℓ ≥ 7` under (P2), as it is
used; quantified over all primes it fails for the curves of the points, whose 3- and
5-torsion is rational.

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
  orbicurves and their local predicates enter through the explicit interfaces
  `Iut.AnabelianGeometry` / `Iut.TemperedGeometry`, instantiated by the anabelian model
  (#276, #279); fundamental groups and cores are not represented (see "Honesty
  boundary"). Bad-place Tate `q`-parameters come from
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
* [`LocalConstruct/`](Iut/Concrete/LocalConstruct) — the **construction** of
  `Iut.LocalTheory K` (`Theory.lean`, `concreteLocalTheory`): the packets as
  `PiTensorProduct`s of the completions over `ℚ_p`/`ℝ` with their norm topology
  (`Packet.lean`), the order `R_I = ⊗ 𝓞_{v_j}` (`Integral.lean`) and the maximal order
  `(R_I)^∼` as the integral closure of `ℤ_p` — bounded because the packet is reduced
  (formally unramified over `ℚ_p`) and embeds in the product of its residue fields
  (`MaximalOrder.lean`), the projective unit ball `B_I` at `∞` (`Archimedean.lean`), the
  normalized Haar log-volume with its scaling laws (`Haar.lean`, `Volume.lean`), the
  admissible class (`Admissible.lean`), the indeterminacy automorphisms `⊗ σ_j` — finitely
  many, continuous, preserving `(R_I)^∼` (`Indeterminacy.lean`, `ThetaAdmissible.lean`) —
  the `p`-adic logarithm and log-shells of a local field (`PadicLog.lean`), their tensor
  products with the automorphism invariance of IUT IV Proposition 1.2 (`LogShell.lean`),
  the archimedean log-shell `π^{|I|}·B_I` with Proposition 1.5 (`ArchLogShell.lean`), and
  the arithmetic of the number field — places over `p`, `∑ e_v f_v = [K : ℚ]`, the
  different (`Arithmetic.lean`). The residual inputs are the three fields of
  `Iut.LocalConstruct.LocalTheoryFacts K`: `(R_I)^∼ ⊆ 𝓘_I`, existence of least hull
  regions (`HullExists K`), and Proposition 1.4(iii).
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

| Input | Content | Status |
| --- | --- | --- |
| `Iut.LocalTheory K` | tensor packets, log-shells, Haar log-volume, hulls, Props 1.4/1.5 | **constructed** (`Iut.LocalConstruct.concreteLocalTheory`); residual `Prop` `LocalTheoryFacts K` (three fields), padic-log-volume [#1462](https://taxis.lana.merten.dev/issues/1462) |
| `Iut.ThetaLocalData D LT` | `2ℓ`-th roots of the Tate parameters, `q`-degree base change | **constructed** (`Iut.thetaLocalData`), from the rationality of the ℓ- and 2-torsion |
| `Iut.TowerArithmetic D LT TL` | (R4), Steps (ii), (iii) of Theorem 1.10 for the tower `F_mod ⊆ F_tpd ⊆ F ⊆ K` | `Prop`; elliptic-reduction, [#1493](https://taxis.lana.merten.dev/issues/1493) (Prop 1.3: [#1463](https://taxis.lana.merten.dev/issues/1463)) |
| `Iut.ChebyshevBound` | Proposition 2.1(ii) | **proved** (`Iut.chebyshevBoundExplicit`, threshold `10^12`, from Mathlib's Chebyshev bounds) |
| `Iut.PrimeCountingBound` | Proposition 1.6 | `Prop` `Iut.PrimeCountingHyp`; prime-counting, [#1466](https://taxis.lana.merten.dev/issues/1466) |
| `Iut.CurveInputs T K d` | the curves `E_x/F_x` of the points with [GenEll] §§1, 3 inputs | **constructed for the tripod** (`Iut.Tripod.curveInputs`); residual `Prop`s `CurveProps`, `CurveFactsProp`, see below |
| `Genl.HeightTheory.ProofPackage` | [GenEll] Theorem 2.1 (ii) ⇒ (i) | not needed for the tripod target `StatementII` |
| `EllipticCurveData.CurveArithmetic` | Prop 1.8 | six of ten fields **proved** (`CurveArithmetic.ofCore`); `√−1`, stable reduction, `E[6]` rational, `F/F_mod` Galois of degree prime to `ℓ` remain `Prop`s |
| `EllipticCurveData.TateInputs` | Tate parameters at the multiplicative places | **constructed** (`EllipticCurveData.tateInputs`) |
| `EllipticCurveData.ModEllRepData ℓ` | the mod-`ℓ` representation on `E[ℓ]` | **constructed** (`modEllRepData`) from `E[ℓ] ≅ (ℤ/ℓ)²` ([#277](https://taxis.lana.merten.dev/issues/277)) |
| `Iut.AnabelianExistence AG TG` | IUT I, Definition 3.1(d)–(f): `C̲_K`, `ε`, `V` and the bad-place conditions | **proved** for the anabelian model (`Iut.Anabelian.anabelianExistence`), with no residual input; see below |


### The tripod theorem with propositional inputs (`Iut/Tripod/`)

`Iut.Tripod.abc_of_variant` ([`Iut/Tripod/Main.lean`](Iut/Tripod/Main.lean)) states the
implication for the concrete tripod `ℙ¹ ∖ {0,1,∞}`: every object is constructed in this
repository and every hypothesis is a proposition about the constructed objects.

* [`Basic.lean`](Iut/Tripod/Basic.lean), [`Northcott.lean`](Iut/Tripod/Northcott.lean) —
  the height formalism `Iut.Tripod.tripodTheory`: points `λ ∈ ℚ̄ ∖ {0,1}`, `ptLE d` by the
  degree of the minimal polynomial, `htCan` the absolute logarithmic Weil height (Mathlib),
  `logDiff` the normalized log-discriminant of `ℚ(λ)`, `logCond` the normalized conductor
  of `λ` with respect to `{0,1,∞}`, and the valuation-bounded compactly bounded subsets
  `CompactlyBounded` (finite places over a finite set of primes containing `2`, and all
  archimedean places, bounded). Northcott over all number fields of degree `≤ d` is
  **proved** (`northcottHyp`, by bounding the coefficients of minimal polynomials). The
  target is `tripodTheory.StatementII`: ABC for points of bounded degree in a compactly
  bounded subset.
* [`Legendre.lean`](Iut/Tripod/Legendre.lean), [`CurveOf.lean`](Iut/Tripod/CurveOf.lean),
  [`TwoTorsion.lean`](Iut/Tripod/TwoTorsion.lean) — the Legendre curve
  `E_λ : y² = x(x−1)(x−λ)` over `F_λ = ℚ(λ, √−1, √λ, √(1−λ), E_λ[3], E_λ[5])` (the two
  extra square roots make `F_λ/ℚ(j)` Galois: the conjugates of `λ` give the twists of
  `E_λ` by `λ` and `1−λ`), its four rational 2-torsion points.
* [`CurveFacts.lean`](Iut/Tripod/CurveFacts.lean),
  [`TorsionDegree.lean`](Iut/Tripod/TorsionDegree.lean),
  [`Providers.lean`](Iut/Tripod/Providers.lean) — proved: `√−1 ∈ F_λ`, `E[6]` rational,
  `[ℚ(j) : ℚ] ≤ deg λ`, `[F_λ : ℚ] ≤ 552960·deg λ` (the torsion fields have degree
  `≤ |GL₂(𝔽_ℓ)|`, by the Galois correspondence), `log-diff = ` the different degree of the
  tripodal field `ℚ(λ)`; the curve-level data (Tate parameters, mod-`ℓ` representations,
  finiteness of torsion) from the propositions `Iut.Tripod.CurveProps` (`E_λ[n] ≅ (ℤ/n)²`,
  stable reduction of `E_λ/F_λ`, `F_λ/ℚ(j)` Galois of degree prime to `ℓ`); the remaining
  facts of Corollary 2.2 as the `Prop` structure `CurveFactsProp` (the height comparison
  `(1/6)·log q_∀ ≈ h(λ)` of [GenEll] Prop 3.4, the cyclic-subgroup bound of [GenEll]
  Lemma 3.5 for `ℓ ≥ 7` under (P2), the `SL₂`-image lemma); the `2`-adic bound
  (`Iut.Tripod.twoAdicBound`, with `B = 4c` on `CompactlyBounded` sets) and the conductor
  comparisons `log-cond_{F_tpd} ≤ log-cond(λ) ≤ log-cond_{F_tpd} + log 2ℓ`
  (`logCondGe`, `logCondLe`, [`TwoAdic.lean`](Iut/Tripod/TwoAdic.lean),
  [`LogCond.lean`](Iut/Tripod/LogCond.lean)) are **proved**. These were audited for satisfiability with the repository's exact
  normalisations; the audit forced two corrections recorded in the honesty boundary (the
  reduction predicates up to a change of variables, and the restriction of the
  cyclic-subgroup bound to `ℓ ≥ 7`).

Final statement (hypotheses only): `CurveProps`, `∀ K d, ∃ T_K, CurveFactsProp … K d T_K`,
`∀ K, LocalTheoryFacts K`, the tower arithmetic for the constructed local theory and theta
data, `PrimeCountingHyp`, and the variant `h312`; conclusion `tripodTheory.StatementII`.
`StatementI` (all hyperbolic curves) additionally needs heights on curves and the
coverings of [GenEll] Theorem 2.1, which remain in genl's scope.

## Anabelian model strand (`Iut/Anabelian`)

The interfaces `Iut.AnabelianGeometry` and `Iut.TemperedGeometry` behind the Θ-data are
instantiated by a **linear-algebraic model** (taxis
[#276](https://taxis.lana.merten.dev/issues/276),
[#279](https://taxis.lana.merten.dev/issues/279)):

* [`Model.lean`](Iut/Anabelian/Model.lean) — model orbicurves `(E, ℓ, M, ±)` standing for
  `(E/M) ∖ (E[ℓ]/M)` and its `±`-quotient (the only shapes IUT I, Definition 3.1 uses);
  covers induced by `[n]`, base change, cusps `E(k)[ℓ]/M` (mod `±`), the rank-one
  quotient, the `±`-quotient cartesian squares, the types `(1, ℓ-tors)`,
  `(1, ℓ-tors)^±`.
* [`Local.lean`](Iut/Anabelian/Local.lean) — over a valued field: the kernel of
  reduction and the **graph line** `E(k)[ℓ] ∩ E₁(k)` (= `μ_ℓ` under Tate
  uniformization), the **canonical generators** `q^{±1/ℓ}` of the graph quotient
  (`ℓ·v(x(P)) = -v(j)` in minimal models), split multiplicative reduction, the type
  `(1, ℤ/ℓℤ)^±`, theta-root models and the canonical graph cusp.
* [`Geometry.lean`](Iut/Anabelian/Geometry.lean) — the closed terms
  `Iut.Anabelian.modelAG : Iut.AnabelianGeometry` and
  `Iut.Anabelian.modelTG : Iut.TemperedGeometry modelAG`.
* [`Torsion.lean`](Iut/Anabelian/Torsion.lean), [`Linear.lean`](Iut/Anabelian/Linear.lean),
  [`Existence.lean`](Iut/Anabelian/Existence.lean) — the ℓ-torsion is rational over
  `K = F(E[ℓ])`; `SL₂(𝔽_ℓ)` acts transitively on (line, generator of the quotient) pairs;
  **`Iut.Anabelian.anabelianExistence`**: `C̲_K = (E_K, ℓ, ⟨e₁⟩, ±)`, `ε = e₂ mod ⟨e₁⟩`,
  and at each bad place a place of `K` chosen through `SL₂(𝔽_ℓ)` so that the graph line
  is `⟨e₁⟩` and the canonical generators are `±e₂` — the mechanism of (P7) in the proof
  of IUT IV, Corollary 2.2. `anabelianExistence : Iut.AnabelianExistence modelAG modelTG`
  has no hypotheses. The final theorem is
  `Iut.Anabelian.cor312Variant_implies_abc_model`, whose remaining inputs are the curve
  inputs of Corollary 2.2, the universal providers, the analytic inputs and the variant
  `h312`.
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

* [`VariableChangePoint.lean`](Iut/Cor312/ThetaData/VariableChangePoint.lean),
  [`UltrametricSqrt.lean`](Iut/Cor312/ThetaData/UltrametricSqrt.lean),
  [`ReductionNorm.lean`](Iut/Cor312/ThetaData/ReductionNorm.lean),
  [`TateIsomorphism.lean`](Iut/Cor312/ThetaData/TateIsomorphism.lean),
  [`TateStructureOfIso.lean`](Iut/Cor312/ThetaData/TateStructureOfIso.lean),
  [`TateStructureUnique.lean`](Iut/Cor312/ThetaData/TateStructureUnique.lean),
  [`TateStructureTransport.lean`](Iut/Cor312/ThetaData/TateStructureTransport.lean),
  [`GalCompletion.lean`](Iut/Cor312/ThetaData/GalCompletion.lean),
  [`BadPlaceNorm.lean`](Iut/Cor312/ThetaData/BadPlaceNorm.lean),
  [`TateFamilyGalois.lean`](Iut/Cor312/ThetaData/TateFamilyGalois.lean),
  [`TateFamilyOfSplit.lean`](Iut/Cor312/ThetaData/TateFamilyOfSplit.lean) — **Tate's
  theorem and the Tate family, proved** (taxis #1582): points along changes of variables
  form a group isomorphism; Hensel's lemma for square roots; Mathlib's reduction classes
  read as norm conditions on the completion; an elliptic curve over a complete ultrametric
  field with `‖2‖ = 1` and split multiplicative reduction is a Tate curve `E_q` after a
  change of variables (short normal forms with equal `j` differ by a scaling whose square
  is `c₄c₆(E)/c₄c₆(E_q)` up to squares, a unit that is a square modulo the maximal ideal
  because `−c₄c₆` is the discriminant of the tangent quadratic at the node); Tate
  structures on such curves, their uniqueness up to sign (`Aut(E_q) = ±1`) and transport
  along isometric isomorphisms; the isometry `K_w ≃ K_{σw}` extending `σ ∈ Gal(K/F)`; and
  the Galois equivariance of the graph lines and canonical generators, which holds for any
  choice of Tate structures by uniqueness. The Tate family of the Θ-data is
  **constructed** (`EllipticCurveData.tateFamily`, `Iut.tateFamilyOfTorsion`) from the
  multiplicative reduction of `E` at the places of `F` over `V_mod^bad` and the rationality
  of the ℓ-torsion over `K = F(E[ℓ])`, with no further input: the reduction at a place `w`
  of `K` is split because `−c₄c₆` is a square in `K_w`
  ([`SqrtAtBadPlace.lean`](Iut/Cor312/ThetaData/SqrtAtBadPlace.lean)) — in
  `K' = K(√(−c₄c₆))` ([`QuadraticExtension.lean`](Iut/Cor312/ThetaData/QuadraticExtension.lean))
  the curve is a Tate curve over the completion at a place `w'` over `w`; if the conjugation
  fixes `w'` it acts on that completion fixing the curve and all its ℓ-torsion, so by the
  sign theorem ([`TateSign.lean`](Iut/Cor312/ThetaData/TateSign.lean): an isometric
  automorphism fixing all the ℓ-torsion fixes the Tate structure, hence a square root of
  `−c₄c₆`) it would fix `√(−c₄c₆)`, which it negates; otherwise `w` splits in `K'`, the
  residue degree is `1` ([`ValuationTransfer.lean`](Iut/Cor312/ThetaData/ValuationTransfer.lean):
  valuations along extensions of number fields, `Σ e f = [K' : K]`), `−c₄c₆` is a square
  modulo `w`, and Hensel's lemma applies. In
  tate-curves-theta (now at `ca6c227`) the hypothesis `‖12‖ = 1` of the Tate uniformization
  was weakened to `‖2‖ = 1 ∧ 12 ≠ 0` (residue characteristic `3` occurs in `V_mod^bad`), and
  the naturality of the Tate coordinates under base change was added.

Interface amendments made for this (recorded on taxis #1453): the "lies over" relation on
finite places is the prime-ideal relation (the absolute-value form of the delivered
statement was only satisfiable at unramified split primes); `IsTypeOneZModPM`,
`IsThetaRootModel` and `canonicalGraphCusp` take a Tate structure on the local orbicurve
over a complete rank-one valued field, and the local theta data carry the chosen Tate
structures (`tateX`, `tateC`); the Θ-data carry the Tate uniformizations at the places of
the torsion field (`InitialThetaData.tate`).

The model has **no residual interface**: the Tate family of the Θ-data is proved (see
above), and the former residual interfaces `Iut.Anabelian.EtalePi1Theory` (étale `π₁` of
the model orbicurves, open immersions for covers, `k`-cores and their stability;
[#1527](https://taxis.lana.merten.dev/issues/1527)) and `Iut.Anabelian.TemperedPi1Theory`
(tempered `π₁` with the comparison to the étale `π₁`;
[#1528](https://taxis.lana.merten.dev/issues/1528)) were removed together with the
corresponding fields of `Iut.AnabelianGeometry` / `Iut.TemperedGeometry`, on the ground
that the statement of the variant never reads them (see "Honesty boundary", *Anabelian
components of the Θ-data*).

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
