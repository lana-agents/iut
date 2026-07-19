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
shape to copy for the Verso and comparator infrastructure.

This specification uses conditional Lean theorems where Section 1 imports data
or results from IUT I–III. Such a theorem says exactly which input package is
assumed. It must never be presented as an unconditional formalization of the
imported IUT result.

## 2. Honesty boundary

### 2.1 Mathematics to prove in this repository

The following content is ordinary mathematics and is not supplied as an IUT
hypothesis.

* Real/integer ceiling and floor estimates used in Proposition 1.2 and
  Proposition 1.4.
* Finite sums, products, weighted averages (Proposition 1.7), and the elementary
  averages (E1), (E2) in the proof of Theorem 1.10.
* The mixed-characteristic local-field algebra in Propositions 1.1–1.4:
  differents, normalization of finite tensor products, the convergent `p`-adic
  logarithm/exponential estimates, normalized additive log-volume, and their
  numerical bounds. General finite extensions of `ℚ_[p]` require repository
  infrastructure on top of mathlib, but the desired conclusions may not be put
  into a structure field merely to make the propositions immediate.
* The Hermitian/tensor-product calculations of Proposition 1.5.
* The eventual prime-counting estimate of Proposition 1.6, using mathlib’s
  Chebyshev/prime-counting asymptotics.
* The group-theoretic and elliptic-curve descent statements of Proposition 1.8,
  to the extent supported by actual definitions and proofs. Reduction-theory
  consequences that are not presently represented in mathlib must remain
  explicitly conditional as described below; they are not silently asserted.
* Arithmetic divisors, support, (normalized) degree, pullback, and local degree
  from Definition 1.9.
* All numerical assembly in the proof of Theorem 1.10 after the imported IUT
  containment and Corollary 3.12 inputs have been supplied.

Every theorem in this list must have a proof term checked by Lean. A helper
structure may package ambient operations and their algebraic laws, but may not
contain the proposition being advertised under a renamed field.

### 2.2 Imported-IUT interface boundary

Section 1.10 quantifies over objects built in IUT I–III: initial Θ-data,
log-shells on prime-strips, tensor packets, Θ-pilot objects, processions,
mono-analytic log-volumes, multiradial representations, holomorphic hulls,
Kummer isomorphisms, and indeterminacies (Ind1)–(Ind3). Mathlib has no meanings
for these names. They will be represented only by the following explicit Lean
structures in `Iut4Sec1/IUT/Interfaces.lean`.

1. `Iut4Sec1.IUT.InitialThetaData`: the number-field/place index types, odd prime
   `ℓ`, the fields/invariant values used in the displayed estimate, good/bad and
   distinguished place predicates, and the stated finiteness/positivity/Galois
   conditions. Fields are data or ordinary hypotheses; this structure does not
   contain the conclusion of Theorem 1.10.
2. `Iut4Sec1.IUT.LogShellPacket`: local log-shell carriers and their rational
   tensor packet, integral container, local `logVolume`, scaling, monotonicity,
   finite direct-sum/tensor compatibility, and normalization laws. These laws
   stand for the mono-analytic log-volume and prime-strip constructions of IUT
   III. They are fields of each supplied packet, never global axioms.
3. `Iut4Sec1.IUT.ThetaPilotRealization`: the possible images of a Θ-pilot object,
   its holomorphic hull, local realization maps, and explicit containment
   hypotheses for the effects of (Ind1), (Ind2), and (Ind3). The containment is
   labeled as imported IUT III input, rather than called Proposition 1.4.
4. `Iut4Sec1.IUT.ProcessionNormalization`: the finite `j ∈ F_ℓ^⋇` indexing,
   packet weights, normalized-weight identity, and the rule identifying the
   procession-normalized global log-volume with the weighted local sum.
5. `Iut4Sec1.IUT.Corollary312Input`: the real constant `CTheta`, the hypothesis
   `-1 ≤ CTheta`, and the equation/inequality connecting `CTheta * |log q|` to
   the holomorphic-hull log-volume. This is precisely the imported use of
   [IUTchIII], Corollary 3.12.

All final theorem signatures take values of these structures as explicit
arguments. No instance of them is declared globally. The blueprint must tag a
node using these packages as **conditional on IUT I–III interfaces**.

### 2.3 Non-IUT library-gap interface

Proposition 1.8(v)–(vii) uses moduli of elliptic curves with level structure,
semistable models, Néron models, and inertia actions not currently available as
one mathlib API. `Iut4Sec1/Elliptic/ReductionInterface.lean` may define
`Iut4Sec1.Elliptic.ReductionCertificate`, whose fields state semistable/good/
multiplicative reduction consequences for a particular elliptic curve and
place. Results consuming it must be named `..._of_reductionCertificate`; the
unconditional group/descent parts of Proposition 1.8 remain separate. This
package is an explicit local hypothesis, not an axiom and not evidence that the
reduction theorem itself has been formalized. Blueprint item 1.8 remains
“conditional/partial” until these fields are replaced by proofs.

No other unproved mathematical claim may be moved into an interface. If a later
phase discovers another missing prerequisite, stop at the phase gate and amend
this specification in a reviewed `P<n>: revise interface boundary` commit.

## 3. Comparator headline and justification

The comparator headline is the finite-sum ramification-error estimate used in
Proposition 1.4(iii):

`Iut4Sec1.nonarchimedean_logError_sum_le`.

For `p > 2`, define

`nonarchimedeanLogError p e = ⌈e / (p - 2)⌉ / e - 1 / e`

as a real number. The exact challenge declarations are:

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

(The `by sorry` occurs only in the challenge and the temporary P2 solution.) For
positive ramification indices `e i`, this error is at most `4 / p`; it vanishes
when `e i ≤ p - 2`. Therefore the sum is at most `4 * |Istar| / p` when every
index outside `Istar` has small ramification. The challenge uses `import Mathlib`
only.

This is the numerical core of the first normalized log-volume bound in
Proposition 1.4(iii). It is fully self-contained and has no Θ-pilot/log-shell
vocabulary, no imported IUT theorem, and no ad hoc local-field interface. That
makes it a more honest comparator headline than Theorem 1.10. It is also more
substantial and closer to the paper’s headline local estimate than merely
restating the normalization `μlog(pR) = -log p`.

Comparator configuration:

* challenge module: `Challenge`
* solution module: `Solution`
* theorem name:
  `Iut4Sec1.nonarchimedean_logError_sum_le`
* permitted axioms after the solution is filled: exactly `propext`,
  `Quot.sound`, and `Classical.choice` (remove any unused permission if
  comparator accepts a smaller list)

## 4. Repository conventions and guardrails

* Never add a Lean `axiom` declaration.
* No `sorry` is allowed in tracked files except
  `Comparator/Challenge.lean`. `Comparator/Solution.lean` may contain `sorry`
  only from P2 through P9; P10 removes it. Comments and documentation should not
  use `sorry` as a fake implementation marker; use “not started” text.
* `#print axioms` for repository theorems must not contain `sorryAx` or an
  undeclared project axiom. The challenge is expected to print `sorryAx`.
  Before P10 the solution stub is also expected to print `sorryAx`; after P10 it
  may use only the comparator permitted axioms.
* Every phase finishes with `lake build` green and `git diff --check` clean.
  Nested blueprint phases additionally build and generate the Verso site.
* Keep `Iut4Sec1.lean` as the project import root and update it in the same phase
  as each new public module.
* Update blueprint `lean :=` links only after the linked declaration exists.
  Otherwise retain an explicit “Status: not started” or conditional-interface
  annotation.
* Append one entry to `Plans/Iut4Sec1WorkLog.md` per phase, including checks and
  commit hash. Record the reviewer verdict in the Review log below.
* Work directly on `main`. Use one phase-sized commit per accepted phase with
  message `P<n>: <summary>`. Do not push unless separately instructed.
* Do not commit `.lake/`, `.pi/`, `blueprint-verso/.lake/`, or generated
  `blueprint-verso/_out/`.
* A reviewer must accept each phase before work on the next phase begins.

The standard no-placeholder audit (with the P2–P9 solution exception) is:

```bash
! rg -n '^\s*axiom\b' --glob '*.lean' .
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' --glob '!Comparator/Solution.lean' .
```

From P10 onward, omit the second exclusion:

```bash
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' .
```

## 5. Phases

### P0 — Bootstrap repository, references, plans, and specification

**Scope**

* Commit the existing scaffold: `.github/`, `.gitignore`, `README.md`,
  `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `Iut4Sec1.lean`, and
  `Iut4Sec1/Basic.lean` (`hello` remains only a scaffold declaration).
* Commit `references/iut4.pdf`, `references/iut4.txt`, and
  `references/iut4-section1.txt` unchanged.
* Add this file and `Plans/Iut4Sec1WorkLog.md`.
* Do not add formalization, blueprint, or comparator code.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Basic.lean
lake build Iut4Sec1
lake build
printf 'import Iut4Sec1.Basic\n#print axioms hello\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
git status --short --ignored
```

Expected: all Lean/Lake commands succeed; `.lake/` and `.pi/` are the only
project-local ignored directories of note; there are no untracked tracked-worthy
files after the P0 commit.

**Review focus**

* Sources are present and unchanged.
* The honesty boundary and comparator choice are explicit.
* `.gitignore` excludes `.lake/` and `.pi/`.
* No implementation work has leaked into P0.

**Gate:** P0 may be committed by the spec author as the bootstrap commit. A
reviewer must accept P0 before P1 starts.

### P1 — Verso blueprint scaffold for items 1.1–1.10

**Scope**

Create a nested package adapted from `proetale/blueprint-verso`:

* `blueprint-verso/.gitignore`
* `blueprint-verso/lakefile.toml`, `lake-manifest.json`, `lean-toolchain`
* `blueprint-verso/Iut4Sec1Blueprint.lean`
* `blueprint-verso/Iut4Sec1Blueprint/Blueprint.lean`
* `blueprint-verso/Iut4Sec1Blueprint/TexPrelude.lean`
* `blueprint-verso/Iut4Sec1BlueprintMain.lean`
* `blueprint-verso/scripts/ci-pages.sh`
* ten chapter files:
  `Chapters/Proposition11.lean`, `Proposition12.lean`,
  `Proposition13.lean`, `Proposition14.lean`, `Proposition15.lean`,
  `Proposition16.lean`, `Proposition17.lean`, `Proposition18.lean`,
  `Definition19.lean`, and `Theorem110.lean`.
* `.github/workflows/verso-blueprint.yml` adapted to this package.

Each chapter contains a faithful short statement and dependency notes. Every
node is either linked to a declaration that already exists or says
`Status: not started`; no guessed `lean :=` names. Item 1.10 prominently states
that its eventual Lean theorem is conditional on the Section 2.2 interfaces.

**Narrow checks**

```bash
(cd blueprint-verso && lake update)
(cd blueprint-verso && lake build Iut4Sec1Blueprint)
(cd blueprint-verso && lake env lean Iut4Sec1Blueprint/Blueprint.lean)
./blueprint-verso/scripts/ci-pages.sh
test -f blueprint-verso/_out/site/html-multi/index.html
test -f blueprint-verso/_out/site/html-multi/-verso-data/blueprint-manifest.json
lake build
printf 'import Iut4Sec1.Basic\n#print axioms hello\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Package shape follows the template without importing template project names.
* Exactly ten chapter entries mirror 1.1–1.10 and use accurate statements.
* Not-started and conditional status is visible rather than hidden by links.
* Nested toolchain is compatible with root Lean 4.32.0 and generated files are
  ignored.

**Gate:** reviewer must accept before P2.

### P2 — Comparator challenge and infrastructure

**Scope**

* Add `Comparator/README.md` explaining the chosen Proposition 1.4(iii) core.
* Add `Comparator/Challenge.lean`, with exactly `import Mathlib`, a local copy of
  `Iut4Sec1.nonarchimedeanLogError`, and theorem
  `Iut4Sec1.nonarchimedean_logError_sum_le` ending in the sole challenge
  `sorry`.
* Add `Comparator/Solution.lean`, importing `Iut4Sec1`, copying the identical
  definition/signature, and temporarily ending the theorem in `sorry`.
* Add `Comparator/config.json` with the module/theorem names and permitted axioms
  from Section 3.
* Add `Challenge` and `Solution` `lean_lib` stanzas to `lakefile.toml`; include
  both in `defaultTargets`.
* Add `CheckDecls.lean` and a `checkdecls` executable stanza that excludes the
  duplicate `Challenge`/`Solution` roots, following the template.
* Add `.github/workflows/comparator.yml` adapted from the template.

No project proof of the challenge theorem is added in this phase.

**Narrow checks**

```bash
lake env lean Comparator/Challenge.lean
lake env lean Comparator/Solution.lean
lake build Challenge
lake build Solution
lake build checkdecls
lake build
printf 'import Challenge\n#print axioms Iut4Sec1.nonarchimedean_logError_sum_le\n' > /tmp/Iut4Sec1ChallengeAxioms.lean
lake env lean /tmp/Iut4Sec1ChallengeAxioms.lean
git diff --check
```

Expected: both comparator modules build independently; the printed challenge
axioms include `sorryAx`; duplicate declarations are never imported together.

**Review focus**

* Challenge imports `Mathlib` only and has no dependency on this repository.
* Challenge and solution statements are textually identical modulo imports/docs.
* Config points at the one exact theorem name.
* Local `checkdecls` excludes only the duplicate comparator roots.

**Gate:** reviewer must accept before P3.

### P3 — Real ramification-error arithmetic

**Scope**

* Add `Iut4Sec1/Real/LogError.lean` with declarations:
  `nonarchimedeanLogError`, `nonarchimedeanLogError_nonneg`,
  `nonarchimedeanLogError_eq_zero_of_le`,
  `nonarchimedeanLogError_le_four_div`, and
  `nonarchimedean_logError_sum_le`.
* The last declaration has exactly the comparator signature.
* Update `Iut4Sec1.lean` and blueprint items 1.2/1.4 with valid links.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Real/LogError.lean
lake build Iut4Sec1.Real.LogError
lake build
printf 'import Iut4Sec1.Real.LogError\n#print axioms Iut4Sec1.nonarchimedean_logError_sum_le\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
! rg -n '^\s*axiom\b' --glob '*.lean' .
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' --glob '!Comparator/Solution.lean' .
git diff --check
```

Expected: no `sorryAx` in the project theorem; only standard logical axioms, if
any, are printed.

**Review focus**

* Casts, ceiling, division by positive `e`, and `p > 2` are handled explicitly.
* The bad-index set bound matches Proposition 1.4(iii), not a weakened informal
  paraphrase.
* Comparator signature stability is preserved.

**Gate:** reviewer must accept before P4.

### P4 — Finite packet combinatorics and weighted averages

**Scope**

* Add `Iut4Sec1/Combinatorics/WeightedAverage.lean`:
  `tupleWeight`, `tupleValue`, `weightSum_pow`,
  `weighted_component_sum`, and `weighted_average_eq` (Proposition 1.7).
* Add `Iut4Sec1/Combinatorics/FiniteSums.lean`:
  `sum_range_id_div`, `sum_range_sq_div` (E1/E2), and the forms indexed by
  `Fin ((ℓ - 1) / 2)` used later.
* Update imports and blueprint items 1.7/1.10.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Combinatorics/WeightedAverage.lean
lake env lean Iut4Sec1/Combinatorics/FiniteSums.lean
lake build Iut4Sec1.Combinatorics.WeightedAverage
lake build Iut4Sec1.Combinatorics.FiniteSums
lake build
printf 'import Iut4Sec1.Combinatorics.WeightedAverage\n#print axioms Iut4Sec1.weighted_average_eq\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

Expected: no `sorryAx` or project axioms.

**Review focus**

* Denominators are proved positive from nonempty/positive weights.
* The theorem includes both equal weighted sums stated in Proposition 1.7.
* Empty finite-type edge cases cannot enter through hidden defaults.

**Gate:** reviewer must accept before P5.

### P5 — Mixed-characteristic local-field model and invariants

**Scope**

* Add `Iut4Sec1/LocalField/Basic.lean` defining
  `MixedCharLocalFieldData`, `ringOfIntegers`, normalized `ord`,
  `ramificationIndex`, `residueDegree`, and `differentOrder`.
  The structure packages a finite extension of `ℚ_[p]`, valuation/ring data, and
  compatibility laws; it contains no Proposition 1.1–1.4 conclusion.
* Add `Iut4Sec1/LocalField/FractionalPowers.lean` defining choice-independent
  fractional ideals `pFractionalIdeal` and proving
  `pFractionalIdeal_eq_of_ord_eq`, multiplication, and inclusion/order lemmas.
* Add `Iut4Sec1/LocalField/Parameters.lean` defining `aParam`, `bParam`, family
  sums, and proving `aParam_eq_inv`, `bParam_eq_neg_inv`, and
  `aParam_eq_neg_bParam` in the small-ramification case.
* Update imports and blueprint item 1.2.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/Basic.lean
lake env lean Iut4Sec1/LocalField/FractionalPowers.lean
lake env lean Iut4Sec1/LocalField/Parameters.lean
lake build Iut4Sec1.LocalField.Parameters
lake build
printf 'import Iut4Sec1.LocalField.Parameters\n#print axioms Iut4Sec1.aParam_eq_neg_bParam\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* `ord(p) = 1`, positivity of `e`, and all scalar coercions are fields/laws with
  mathematical meaning, not conclusions smuggled into data.
* Fractional-power notation is choice independent.
* Definitions agree exactly with Proposition 1.2 for `p = 2` and `p > 2`.

**Gate:** reviewer must accept before P6.

### P6 — `p`-adic logarithm and exponential estimates

**Scope**

* Add `Iut4Sec1/LocalField/PadicLog.lean`: convergent `padicLog` and `padicExp`
  on the required valuation balls, inverse/map laws, and unit-log image.
* Add `Iut4Sec1/LocalField/LogLattice.lean` with `unitLogLattice` and the two
  inclusions `pPow_a_le_unitLogLattice` and
  `unitLogLattice_le_pPow_neg_b`; prove `unitLogLattice_eq` in the
  `p > 2`, `e ≤ p - 2` case (Proposition 1.2(i)).
* Do not introduce a `LogExpPackage` hypothesis. If mathlib analytic support is
  insufficient, stop and amend the spec rather than assuming these inclusions.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/PadicLog.lean
lake env lean Iut4Sec1/LocalField/LogLattice.lean
lake build Iut4Sec1.LocalField.LogLattice
lake build
printf 'import Iut4Sec1.LocalField.LogLattice\n#print axioms Iut4Sec1.pPow_a_le_unitLogLattice\n#print axioms Iut4Sec1.unitLogLattice_le_pPow_neg_b\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Convergence domains and strict/non-strict valuation inequalities match the
  classical log/exp radii.
* No circular use of Proposition 1.2(i).
* The torsion kernel of logarithm is handled where needed.

**Gate:** reviewer must accept before P7.

### P7 — Multiple tensor products and differents (Proposition 1.1)

**Scope**

* Add `Iut4Sec1/LocalField/TensorPacket.lean` defining the finite iterated tensor
  ring/module, reduced total quotient ring, and `tensorNormalization`.
* Add `Iut4Sec1/LocalField/DifferentTensor.lean` proving
  `different_smul_twoFactor_normalization_le`, the induction lemma
  `different_smul_tensorNormalization_le`, and public theorem
  `multipleTensorProducts_and_differents` (Proposition 1.1).
* Prove independence from generators through fractional ideals, not unspecified
  elements.
* Update imports and blueprint item 1.1.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/TensorPacket.lean
lake env lean Iut4Sec1/LocalField/DifferentTensor.lean
lake build Iut4Sec1.LocalField.DifferentTensor
lake build
printf 'import Iut4Sec1.LocalField.DifferentTensor\n#print axioms Iut4Sec1.multipleTensorProducts_and_differents\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Tensor products are over `ℤ_[p]` and normalization is of the reduced ring in
  its total ring of fractions.
* The distinguished-index exponent omits exactly that index.
* Faithfully-flat descent/two-factor different argument is actually proved.

**Gate:** reviewer must accept before P8.

### P8 — Differents and logarithms (Proposition 1.2)

**Scope**

* Add `Iut4Sec1/LocalField/DifferentsAndLogarithms.lean` with
  `tensorUnitLogLattice`, its finite tensor-product inclusions, and public
  theorems `differentsAndLogarithms_ii`, `_iii`, and `_iv`.
* Automorphisms are explicit `ℚ_[p]`-linear equivalences preserving
  `tensorUnitLogLattice`; all fractional-ideal exponents and floors are typed.
* Update imports and blueprint item 1.2.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/DifferentsAndLogarithms.lean
lake build Iut4Sec1.LocalField.DifferentsAndLogarithms
lake build
printf 'import Iut4Sec1.LocalField.DifferentsAndLogarithms\n#print axioms Iut4Sec1.differentsAndLogarithms_ii\n#print axioms Iut4Sec1.differentsAndLogarithms_iv\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Preservation of the log lattice is the exact hypothesis on `φ`.
* Floor/ceiling rounding directions match the paper.
* Parts (iii)/(iv) are consequences of prior inclusions, not new assumptions.

**Gate:** reviewer must accept before P9.

### P9 — Estimates of differents (Proposition 1.3)

**Scope**

* Add `Iut4Sec1/LocalField/DifferentEstimates.lean` with tower invariants,
  `differentOrder_lower_bound`, `differentOrder_eq_of_tame`, and
  `differentOrder_upper_bound_of_galois` corresponding to 1.3(i)/(ii).
* The upper bound includes the `p`-primary exponent of the extension degree and
  all Galois/tame hypotheses explicitly.
* Update imports and blueprint item 1.3.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/DifferentEstimates.lean
lake build Iut4Sec1.LocalField.DifferentEstimates
lake build
printf 'import Iut4Sec1.LocalField.DifferentEstimates\n#print axioms Iut4Sec1.differentOrder_lower_bound\n#print axioms Iut4Sec1.differentOrder_upper_bound_of_galois\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Normalization of different orders in towers is consistent with `ord(p)=1`.
* Equality is restricted to tame ramification.
* The Kummer/induction argument does not assume the desired upper bound.

**Gate:** reviewer must accept before P10.

### P10 — Normalized nonarchimedean log-volume and comparator solution

**Scope**

* Add `Iut4Sec1/LocalField/LogVolume.lean` defining normalized additive Haar
  `logVolume`, proving `logVolume_ringOfIntegers`, `logVolume_p_smul`, finite
  direct-sum/tensor compatibility, and `logVolume_unitLogLattice`
  (Proposition 1.4(i)/(ii)).
* Add `Iut4Sec1/LocalField/NormalizedEstimate.lean` proving
  `nonarchimedean_normalized_logVolume_first`, `_second`,
  `different_add_a_lower_bound`, and `unramified_logVolume_estimate`
  (Proposition 1.4(iii)/(iv)).
* Replace the `sorry` in `Comparator/Solution.lean` by an application of
  `Iut4Sec1.nonarchimedean_logError_sum_le`; keep the copied challenge
  definition/signature unchanged.
* Update imports and blueprint item 1.4.

**Narrow checks**

```bash
lake env lean Iut4Sec1/LocalField/LogVolume.lean
lake env lean Iut4Sec1/LocalField/NormalizedEstimate.lean
lake env lean Comparator/Solution.lean
lake build Iut4Sec1.LocalField.NormalizedEstimate
lake build Challenge
lake build Solution
lake build
printf 'import Iut4Sec1.LocalField.NormalizedEstimate\n#print axioms Iut4Sec1.nonarchimedean_normalized_logVolume_first\n#print axioms Iut4Sec1.unramified_logVolume_estimate\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' .
git diff --check
```

If comparator tooling is installed, also run exactly:

```bash
lake env "$COMPARATOR_BIN" Comparator/config.json
```

Expected: solution has no `sorryAx` and comparator reports only permitted
axioms.

**Review focus**

* Haar measure normalization divides by local degree as in 1.4(i).
* Torsion quotient contributes `m/(ef)` exactly in 1.4(ii).
* Both bounds in 1.4(iii), including the `3 + log e` term, are present.
* Comparator proof uses the project theorem rather than reproving a divergent
  statement.

**Gate:** reviewer must accept before P11.

### P11 — Archimedean metric estimates (Proposition 1.5)

**Scope**

* Add `Iut4Sec1/Archimedean/PrimitiveAutomorphism.lean` defining the eight
  primitive real-linear isometries of `ℂ` and preservation lemmas.
* Add `Iut4Sec1/Archimedean/TensorMetric.lean` with
  `complexTensorEquivProd`, `complexTensor_metric_factor`,
  `multipleComplexTensor_decomposition`,
  `multipleComplexTensor_metric_factor`, and
  `tensor_mem_scaled_integralStructure` (1.5(i)–(iv)).
* Update imports and blueprint item 1.5.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Archimedean/PrimitiveAutomorphism.lean
lake env lean Iut4Sec1/Archimedean/TensorMetric.lean
lake build Iut4Sec1.Archimedean.TensorMetric
lake build
printf 'import Iut4Sec1.Archimedean.TensorMetric\n#print axioms Iut4Sec1.multipleComplexTensor_metric_factor\n#print axioms Iut4Sec1.tensor_mem_scaled_integralStructure\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* The metric factor is `2^(|I|-1)` (squared norm convention is documented).
* The direct sum has `2^(|I|-1) * |V|^|I|` complex factors.
* Primitive automorphism invariance covers conjugation and multiplication by
  fourth roots of unity.

**Gate:** reviewer must accept before P12.

### P12 — Prime number estimate (Proposition 1.6)

**Scope**

* Add `Iut4Sec1/NumberTheory/PrimeCounting.lean` with `nthPrime`,
  `eventually_n_le_four_mul_nthPrime_div`, `etaPrm`, and
  `primeCounting_le_four_mul_div_log` in the natural-number and real forms used
  by Theorem 1.10.
* Derive the existential constant from mathlib asymptotics; do not assume PNT as
  a structure field.
* Update imports and blueprint item 1.6.

**Narrow checks**

```bash
lake env lean Iut4Sec1/NumberTheory/PrimeCounting.lean
lake build Iut4Sec1.NumberTheory.PrimeCounting
lake build
printf 'import Iut4Sec1.NumberTheory.PrimeCounting\n#print axioms Iut4Sec1.primeCounting_le_four_mul_div_log\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Indexing of the first prime (`2`) has no off-by-one error.
* Positivity of `log η` and threshold enlargement are explicit.
* The final estimate counts primes `≤ η`.

**Gate:** reviewer must accept before P13.

### P13 — Elliptic torsion, descent, and reduction boundary (Proposition 1.8)

**Scope**

* Add `Iut4Sec1/Elliptic/SerreCriterion.lean` with the finite-order linear
  algebra core and `polarizedAutomorphism_injective_on_torsion` under explicit
  abelian-variety/Tate-module hypotheses (1.8(i)).
* Add `Iut4Sec1/Elliptic/Descent.lean` with
  `automorphismGroup_exact`, `minimalFieldOfDefinition`,
  `models_equiv_sections`, `twoTorsionRepresentation_factors`, and
  `models_isomorphic_of_rational_torsion` (1.8(ii)–(iv)).
* Add `Iut4Sec1/Elliptic/ReductionInterface.lean` defining only
  `ReductionCertificate` and conditional declarations
  `semistableReduction_of_reductionCertificate`,
  `legendreModel_of_reductionCertificate`, and
  `inertia_of_reductionCertificate` for 1.8(v)–(vii).
* Update imports and blueprint item 1.8, marking (v)–(vii) conditional/partial.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Elliptic/SerreCriterion.lean
lake env lean Iut4Sec1/Elliptic/Descent.lean
lake env lean Iut4Sec1/Elliptic/ReductionInterface.lean
lake build Iut4Sec1.Elliptic.Descent
lake build Iut4Sec1.Elliptic.ReductionInterface
lake build
printf 'import Iut4Sec1.Elliptic.Descent\n#print axioms Iut4Sec1.models_isomorphic_of_rational_torsion\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* The paper’s hypotheses (`ℓ ≥ 3`, invertibility, rational torsion, and
  `Aut = {±1}` where used) are not dropped.
* Conditional reduction wrappers are clearly named and do not masquerade as
  unconditional proofs.
* No IUT-specific concept has entered Proposition 1.8.

**Gate:** reviewer must accept before P14.

### P14 — Arithmetic divisors and normalized degrees (Definition 1.9)

**Scope**

* Add `Iut4Sec1/Global/ArithmeticDivisor.lean` defining `Place`,
  `ArithmeticDivisor`, `support`, `Effective`, `degree`, `normalizedDegree`, and
  `pullback` for a number field.
* Add `Iut4Sec1/Global/LocalDegree.lean` defining `part`, `normalizedLocalDegree`
  and proving `normalizedDegree_pullback` and
  `normalizedLocalDegree_pullback`.
* Definitions must distinguish nonarchimedean weight `log q_v` from
  archimedean weight `1` exactly as 1.9.
* Update imports and blueprint item 1.9.

**Narrow checks**

```bash
lake env lean Iut4Sec1/Global/ArithmeticDivisor.lean
lake env lean Iut4Sec1/Global/LocalDegree.lean
lake build Iut4Sec1.Global.LocalDegree
lake build
printf 'import Iut4Sec1.Global.LocalDegree\n#print axioms Iut4Sec1.normalizedDegree_pullback\n#print axioms Iut4Sec1.normalizedLocalDegree_pullback\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Arithmetic divisors have finite support by construction.
* Pullback multiplicities and local degrees give extension-invariant normalized
  degree.
* Archimedean and nonarchimedean places cannot be confused by coercions.

**Gate:** reviewer must accept before P15.

### P15 — Explicit IUT interfaces and Theorem 1.10 statement

**Scope**

* Add `Iut4Sec1/IUT/Interfaces.lean` with exactly the five structures listed in
  Section 2.2 and explanatory docstrings naming the imported paper results.
* Add `Iut4Sec1/ThetaPilot/Setup.lean` defining `dmod`, `emod`, `dmodStar`,
  `emodStar`, different/q/conductor divisors, distinguished places, and the
  local/global logarithmic quantities from Theorem 1.10, and proving
  `emodStar_le_dmodStar`.
* Add `Iut4Sec1/ThetaPilot/Statement.lean` with the proposition-valued
  definition `ThetaPilotEstimateStatement`, whose explicit arguments are
  `InitialThetaData`, `ThetaPilotRealization`,
  `ProcessionNormalization`, and `Corollary312Input`, and whose body is the
  exact upper bound for `CTheta` followed by the two final inequalities. Do not
  declare `logVolumeEstimatesForThetaPilotObjects` yet and do not use `sorry`;
  the proved theorem is added in P17.
* Update imports and blueprint 1.10 to link the proposition alias and label the
  interface boundary.

**Narrow checks**

```bash
lake env lean Iut4Sec1/IUT/Interfaces.lean
lake env lean Iut4Sec1/ThetaPilot/Setup.lean
lake env lean Iut4Sec1/ThetaPilot/Statement.lean
lake build Iut4Sec1.ThetaPilot.Statement
lake build
printf 'import Iut4Sec1.ThetaPilot.Statement\n#print axioms Iut4Sec1.emodStar_le_dmodStar\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
! rg -n '^\s*axiom\b' --glob '*.lean' .
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' .
git diff --check
```

**Review focus**

* Every imported IUT notion is visible in an explicit argument structure.
* No structure field is the final Theorem 1.10 inequality.
* The displayed constants and both final inequalities match the paper.
* A proposition alias is not falsely described as a proved theorem.

**Gate:** reviewer must accept before P16.

### P16 — Local-to-global Θ-pilot estimate assembly

**Scope**

* Add `Iut4Sec1/ThetaPilot/LocalBounds.lean` proving the distinguished
  nonarchimedean, unramified nonarchimedean, and archimedean local upper bounds
  from Propositions 1.4/1.5 plus explicit interface containments.
  Declarations: `distinguishedLocalBound`, `unramifiedLocalBound`,
  `archimedeanLocalBound`.
* Add `Iut4Sec1/ThetaPilot/ProcessionAverage.lean` proving
  `weightedPacketBound` and `processionNormalizedBound` using P4.
* Add `Iut4Sec1/ThetaPilot/GlobalBounds.lean` proving the paper’s Step (ii)/(iii)
  different/conductor estimates and prime-sum bound:
  `differentConductor_mono`, `differentConductor_extension_bound`,
  `distinguishedRamification_bound`, and `smallPrimeSum_bound`.
* Update imports and blueprint dependencies without claiming Theorem 1.10 is
  complete.

**Narrow checks**

```bash
lake env lean Iut4Sec1/ThetaPilot/LocalBounds.lean
lake env lean Iut4Sec1/ThetaPilot/ProcessionAverage.lean
lake env lean Iut4Sec1/ThetaPilot/GlobalBounds.lean
lake build Iut4Sec1.ThetaPilot.GlobalBounds
lake build
printf 'import Iut4Sec1.ThetaPilot.GlobalBounds\n#print axioms Iut4Sec1.processionNormalizedBound\n#print axioms Iut4Sec1.smallPrimeSum_bound\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
git diff --check
```

**Review focus**

* Local cases are exhaustive and use the proper earlier proposition.
* Weighted normalization is Proposition 1.7’s normalization, not an unweighted
  average.
* Constants `12`, `20`, `56`, `1/6`, and the `ℓ` factors are traceable to the
  paper’s displayed calculations.
* Imported containment is used only through explicit interface arguments.

**Gate:** reviewer must accept before P17.

### P17 — Conditional proof of Theorem 1.10 and final audit

**Scope**

* Complete `Iut4Sec1/ThetaPilot/Statement.lean` with theorem
  `logVolumeEstimatesForThetaPilotObjects :
  ThetaPilotEstimateStatement data realization procession cor312`.
* Prove the stated upper bound for `CTheta`, then derive both final inequalities
  using `Corollary312Input.lower_bound` and prior arithmetic bounds.
* Update all ten Verso chapters: every completed declaration receives a valid
  `lean :=` link; conditional/partial nodes retain their status labels. Generate
  the final blueprint site.
* Update `Comparator/README.md`, root `README.md`, and work log with final build,
  comparator, interface-boundary, and coverage status.

**Narrow checks**

```bash
lake env lean Iut4Sec1/ThetaPilot/Statement.lean
lake build Iut4Sec1.ThetaPilot.Statement
lake build Challenge Solution
lake build
printf 'import Iut4Sec1.ThetaPilot.Statement\n#print axioms Iut4Sec1.logVolumeEstimatesForThetaPilotObjects\n' > /tmp/Iut4Sec1Axioms.lean
lake env lean /tmp/Iut4Sec1Axioms.lean
(cd blueprint-verso && lake build Iut4Sec1Blueprint)
./blueprint-verso/scripts/ci-pages.sh
! rg -n '^\s*axiom\b' --glob '*.lean' .
! rg -n '\bsorry\b' --glob '*.lean' --glob '!Comparator/Challenge.lean' .
git diff --check
git status --short --ignored
```

If comparator tooling is installed:

```bash
lake env "$COMPARATOR_BIN" Comparator/config.json
```

Expected: final theorem has no `sorryAx` or project axiom; any assumptions are
ordinary explicit structure arguments. Root and nested builds are green. Only
Challenge contains `sorry`.

**Review focus**

* The theorem is conditional exactly where the paper imports IUT I–III.
* No unconditional claim is made for Proposition 1.8(v)–(vii) while the
  reduction certificate remains.
* `#print axioms`, comparator config, blueprint links, and source theorem names
  agree.
* Blueprint accurately distinguishes proved, conditional, partial, and
  not-started status.
* Repository is reproducible from a clean checkout.

**Gate:** reviewer must accept P17 before the project is declared complete.

## 6. Review log

The orchestrator appends one line per verdict. Do not rewrite old verdicts.

| Phase | Commit | Reviewer | Verdict | Date | Notes |
|---|---|---|---|---|---|
| P0 | pending | pending | pending | — | Bootstrap/spec awaiting review. |
