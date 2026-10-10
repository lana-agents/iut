# Comparator: the Corollary 3.12 variant implies formal-conjectures' `ABC.abc`

This directory is a [`leanprover/comparator`](https://github.com/leanprover/comparator)
challenge/solution pair. Its target, `Iut.abc_of_cor312Variant`, says that the hypothesis of
the main theorem of the project (`Iut.classicalABC_of_variant`, `Iut/MainTheorem.lean`)
implies the **official** statement of the ABC conjecture of
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
the theorem `ABC.abc` of
[`FormalConjectures/Wikipedia/ABC.lean`](https://github.com/google-deepmind/formal-conjectures/blob/1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89/FormalConjectures/Wikipedia/ABC.lean)
at commit `1646ca16afd6cc7a693d3bdc9f066c4d3cc01a89`.

## The challenge

`Challenge.lean` has one definition, one theorem and one proof placeholder:

```lean
namespace ABC

/--
The radical of `n` denoted is the product of the distinct prime factors of `n`.
-/
def radical (n : ℕ) : ℕ := n.primeFactors.prod id

end ABC

namespace Iut

open ABC

theorem abc_of_cor312Variant :
    Cor312VariantHolds → ∀ ε : ℝ, 0 < ε →
    {(a, b, c) : ℕ × ℕ × ℕ | 0 < a ∧ 0 < b ∧ 0 < c ∧ ({a, b, c} : Set ℕ).Pairwise Nat.Coprime ∧
    a + b = c ∧ (radical <| a * b * c : ℝ)^(1 + ε) < c}.Finite := by
  sorry

end Iut
```

* The conclusion is the statement of formal-conjectures' `ABC.abc`, verbatim: their theorem
  arguments `(ε : ℝ) (hε : 0 < ε)` are written `∀ ε : ℝ, 0 < ε →`, and the set-builder, the
  pairwise coprimality and the coercions are theirs, unchanged. Their definition
  `ABC.radical` (the product of the distinct prime factors) is copied verbatim, with the same
  name, docstring and body. The copied code is "Copyright 2025 The Formal Conjectures
  Authors", licensed under the Apache License, Version 2.0; `Challenge.lean` carries the full
  notice.
* The hypothesis is `Iut.Cor312VariantHolds :=
  ∀ D : InitialThetaData.{0}, Corollary312Variant (concreteVariantData D)`
  (`Iut/Concrete/ThetaRegion.lean`). Its vocabulary is a project definition and cannot be
  inlined: it covers the initial Θ-data of IUT I, Definition 3.1, stated about the genuine
  étale and tempered fundamental groups of the model orbicurves (`pi1`,
  `tempered-fundamental-groups`), together with the tensor packets with their log-shells,
  log-volumes and hulls, the theta-pilot region, and the variant inequality.

`config.json` lists this one theorem, has no definition holes, and permits only `propext`,
`Quot.sound` and `Classical.choice`. `ABC.radical` is not a definition hole: the comparator
compares every constant that the statement uses, and that is not a listed target, between
Challenge and Solution in full (type and value), so the Solution must declare `ABC.radical`
identically, and does.

## What the challenge trusts

The comparator trusts `Challenge` and its import closure. Besides the Mathlib module
`Mathlib.Analysis.SpecialFunctions.Pow.Real` (whose closure provides `Real.rpow`,
`Set.Finite`, `Set.Pairwise`, `Nat.Coprime` and `Nat.primeFactors`), the challenge imports
only `Iut.Concrete.ThetaRegion`, the module that defines `Cor312VariantHolds`. Its closure
(11224 modules) consists of Lean core, Mathlib and its dependencies, and these project
packages:

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
  `Iut.Tripod.classicalABC_of_statementI`, `Iut.ClassicalABC`,
  `Iut.formalConjecturesABC_of_variant`, `Iut.classicalABC_iff_abc` and
  `FormalConjecturesABC.abc` are absent;
* that no safe declaration of the closure, Lean's core included, refers to axioms other than
  `propext`, `Classical.choice` and `Quot.sound` (so none refers to `sorryAx`), that the same
  holds for the declarations of `Challenge` other than the theorem (`ABC.radical` and the
  matcher of the set-builder), and that no module outside Lean's core declares axioms;
* that the challenge theorem depends on `sorryAx`, from its placeholder, and otherwise only
  on the three standard axioms.

## The solution

`Solution.lean` imports the challenge's modules and `Iut.Abc.FormalConjectures`. It declares
`ABC.radical` exactly as the challenge does and proves the same statement with the term
`Iut.formalConjecturesABC_of_variant : Cor312VariantHolds → FormalConjecturesABC.abc`
(`Iut/Abc/FormalConjectures.lean`), which derives formal-conjectures' statement from the main
theorem `Iut.classicalABC_of_variant` through `Iut.classicalABC_iff_abc`. The project's
verbatim copy `FormalConjecturesABC.abc` has the challenge's statement as its body, with
`FormalConjecturesABC.radical` (the same body as `ABC.radical`) in place of `ABC.radical`, so
the two agree by unfolding definitions and the term type-checks as it stands. Challenge and
Solution are separate Lake roots and are never imported into the same environment.

## Checks

* `scripts/check_comparator_signature.sh` checks that Challenge and Solution declare the same
  public declarations with identical elaborated types (`pp.all`), and that the config lists
  exactly the shared theorem.
* `scripts/audit_trust.sh` checks that the challenge has exactly one theorem
  (`abc_of_cor312Variant`), with exactly one placeholder, and no other trust tokens.
* `scripts/audit_axioms.sh` audits the Solution theorem's axioms
  (`scripts/AuditComparatorSolution.lean`) and the trusted closure
  (`scripts/AuditComparatorChallenge.lean`).

### The comparator

The pair is checked with [`leanprover/comparator`](https://github.com/leanprover/comparator)
using `config.json`, which permits only the standard axioms `propext`, `Quot.sound` and
`Classical.choice`. The check was confirmed on 2026-10-10: the comparator accepted the
solution (`Your solution is okay!`).
