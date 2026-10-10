# Comparator: the Corollary 3.12 variant implies the classical ABC conjecture

This directory is a [`leanprover/comparator`](https://github.com/leanprover/comparator)
challenge/solution pair for the main theorem of the project, `Iut.classicalABC_of_variant`
(`Iut/MainTheorem.lean`).

## The challenge

`Challenge.lean` has one theorem and one proof placeholder:

```lean
theorem Iut.classicalABC_of_cor312Variant :
    Cor312VariantHolds →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a b c : ℕ, 0 < a → 0 < b → Nat.Coprime a b → a + b = c →
        (c : ℝ) ≤ C * ((UniqueFactorizationMonoid.radical (a * b * c) : ℕ) : ℝ) ^ (1 + ε) := by
  sorry
```

* The conclusion is the classical ABC conjecture (Masser–Oesterlé), written out in Mathlib
  terms: `Real.rpow`, `Nat.Coprime`, and `UniqueFactorizationMonoid.radical` on `ℕ`, the
  product of the distinct prime factors. This is the body of the project definition
  `Iut.ClassicalABC` (`Iut/Abc/Classical.lean`), but the challenge does not import that
  definition, so the reader does not have to trust it.
* The hypothesis is `Iut.Cor312VariantHolds :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)`
  (`Iut/Concrete/ThetaRegion.lean`). Its vocabulary is a project definition and cannot be
  inlined: it covers the initial Θ-data of IUT I, Definition 3.1, stated about the genuine
  étale and tempered fundamental groups of the model orbicurves (`pi1`,
  `tempered-fundamental-groups`), together with the tensor packets with their log-shells,
  log-volumes and hulls, the theta-pilot region, and the variant inequality.

`config.json` lists this one theorem, has no definition holes, and permits only `propext`,
`Quot.sound` and `Classical.choice`.

## What the challenge trusts

The comparator trusts `Challenge` and its import closure. Besides two Mathlib modules, the
challenge imports only `Iut.Concrete.ThetaRegion`, the module that defines
`Cor312VariantHolds`. Its closure (11224 modules) consists of Lean core, Mathlib and its
dependencies, and these project packages:

| Package | Modules |
| --- | ---: |
| `Iut` (`Iut.Anabelian`, `Iut.Concrete`, `Iut.Cor312`, `Iut.Torsion`, three `Iut.Tower` modules) | 87 |
| `TemperedFundamentalGroups` | 533 |
| `Oka` | 81 |
| `TateCurvesTheta` | 68 |
| `Pi1` | 24 |
| `EllipticCurves` | 24 |

These are the modules that define the statement. No module that proves the implication
needed moving: `Iut.MainTheorem`, `Iut.Tripod`, `Iut.Implication`, `Iut.Abc` and
`Iut.Concrete.Main`, together with the `genl`, `heights`, `belyi` and `orbicurve-cores`
packages, are all outside the closure. No definition was moved or changed for this pair.
`scripts/AuditComparatorChallenge.lean` (run by `scripts/audit_axioms.sh`) checks, in the
challenge's own environment:

* that no module under `Iut.MainTheorem`, `Iut.Tripod`, `Iut.Implication` or `Iut.Abc` is
  imported, and that the proof-chain declarations `Iut.classicalABC_of_variant`,
  `Iut.Tripod.abc_of_variant`, `Iut.Tripod.statementI_of_statementII`,
  `Iut.Tripod.classicalABC_of_statementI` and `Iut.ClassicalABC` are absent;
* that no safe declaration of the closure, Lean's core included, refers to axioms other than
  `propext`, `Classical.choice` and `Quot.sound` (so none refers to `sorryAx`), and that no
  module outside Lean's core declares axioms;
* that the challenge theorem depends on `sorryAx`, from its placeholder, and otherwise only
  on the three standard axioms.

## The solution

`Solution.lean` imports the challenge's modules and `Iut.MainTheorem`. It proves the same
statement with the term `Iut.classicalABC_of_variant`. This type-checks because the
challenge statement is `Cor312VariantHolds → ClassicalABC` with `ClassicalABC` unfolded.
Challenge and Solution are separate Lake roots and are never imported into the same
environment.

## Checks

* `scripts/check_comparator_signature.sh` checks that Challenge and Solution declare the same
  public declarations with identical elaborated types (`pp.all`), and that the config lists
  exactly the shared theorem.
* `scripts/audit_trust.sh` checks that the challenge has exactly one theorem, with exactly one
  placeholder, and no other trust tokens.
* `scripts/audit_axioms.sh` audits the Solution theorem's axioms
  (`scripts/AuditComparatorSolution.lean`) and the trusted closure
  (`scripts/AuditComparatorChallenge.lean`).

### The comparator

The pair is checked with [`leanprover/comparator`](https://github.com/leanprover/comparator)
using `config.json`, which permits only the standard axioms `propext`, `Quot.sound` and
`Classical.choice`. The check was confirmed on 2026-10-10: the comparator accepted the
solution (`Your solution is okay!`).
