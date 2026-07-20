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
  This strand also carries the ABC target statement the programme aims at.

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
| `Iut` | Corollary 3.12 variant and the ABC target statement |
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
  (`mk_all --check`, for both `Iut` and `Iut4Sec1`), and that everything builds with
  warnings as errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#1](https://taxis.lana.merten.dev/issues/1), [#3](https://taxis.lana.merten.dev/issues/3), [#33](https://taxis.lana.merten.dev/issues/33), [#34](https://taxis.lana.merten.dev/issues/34), [#35](https://taxis.lana.merten.dev/issues/35), [#38](https://taxis.lana.merten.dev/issues/38), [#39](https://taxis.lana.merten.dev/issues/39), [#40](https://taxis.lana.merten.dev/issues/40), [#41](https://taxis.lana.merten.dev/issues/41), [#42](https://taxis.lana.merten.dev/issues/42), [#43](https://taxis.lana.merten.dev/issues/43), [#44](https://taxis.lana.merten.dev/issues/44), [#45](https://taxis.lana.merten.dev/issues/45)
