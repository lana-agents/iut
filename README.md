# IUT IV Section 1 formalization

This repository develops a Lean 4 formalization of the self-contained mathematics
in Section 1, “Log-volume Estimates,” of Mochizuki’s *Inter-universal
Teichmüller Theory IV*. It does **not** verify IUT. Claims imported from IUT I–III
and mathematical infrastructure unavailable in mathlib are kept behind explicit
interfaces or certificates rather than introduced as axioms or hidden inside
helper structures. See the [implementation specification and honesty
boundary](Plans/Iut4Sec1Spec.md#2-honesty-boundary).

## Current scope

The current library proves the real-arithmetic error bound used in Proposition
1.4(iii), the finite weighted-average identity of Proposition 1.7, the elementary
range identities (E1)/(E2), positive finite packet-weight normalization, and the
finite-support arithmetic-divisor foundations of Definition 1.9(i), including
normalized global-degree invariance under pullback.

The library also proves a related raw-degree local-ratio invariance theorem. It
does not claim Definition 1.9(ii)'s displayed globally normalized quotient:
under the implemented pullback, that numerator is invariant while its
local-degree denominator scales by the extension degree. The blueprint labels
this boundary explicitly.

Later Section 1 results remain planned, partial, or conditional as recorded in
the specification. In particular, IUT I–III inputs, the exact prime-counting
coefficient unavailable in the pinned mathlib release, and missing elliptic or
reduction infrastructure must appear as ordinary theorem arguments when used.

## Comparator suite

[`Comparator/Challenge.lean`](Comparator/Challenge.lean) states ten selected
mathlib-only targets from Section 1. Five currently have project proofs, are
re-exported by `Comparator/Solution.lean`, and are configured for
`leanprover/comparator`. The exact target list and inclusion policy are in
[`Comparator/README.md`](Comparator/README.md).

## Blueprint

The Verso blueprint can be served locally with:

```bash
cd blueprint-verso
lake exe vbp build --serve
```

Once GitHub Pages is enabled, the hosted blueprint is available at:
<https://lana-project.github.io/iut4-sec1/verso-blueprint/>.

## Build and audits

Install [elan](https://github.com/leanprover/elan); it selects the Lean version
pinned by `lean-toolchain`. Then run from the repository root:

```bash
lake exe cache get
lake build
./scripts/check_comparator_signature.sh
./scripts/audit_trust.sh
./scripts/audit_axioms.sh
git diff --check
```

The challenge contains the suite's reviewed proof placeholders. Public project
modules and the Solution re-exports are checked separately by the trust and
axiom audits.

## GitHub setup

For publication, enable **Settings → Pages → Source: GitHub Actions**. The
comparator workflow is read-only and runs manually through
`workflow_dispatch`.
