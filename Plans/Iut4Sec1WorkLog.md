# IUT IV Section 1 Work Log

Purpose: preserve concise project context for phased formalization of Section 1 of
Mochizuki’s *Inter-universal Teichmüller Theory IV*.

## How to use this log

- Read `Plans/Iut4Sec1Spec.md` and the latest entry before starting a phase.
- Append one entry after each phase; do not rewrite prior entries.
- Record the exact checks, reviewer verdict, and commit identifier.
- Verify mathematical and Lean details from source files rather than treating
  this log as authority.

## Project overview

- Lean/mathlib: Lean 4.32.0, mathlib v4.32.0.
- Source: `references/iut4.pdf`; Section 1 extraction:
  `references/iut4-section1.txt`.
- Main library: `Iut4Sec1/`, imported by `Iut4Sec1.lean`.
- Planned auxiliary products: `blueprint-verso/` and `Comparator/`.
- Trust boundary: no global axioms. Theorem 1.10 will take explicit structures
  for IUT I–III log-shell/Θ-pilot/procession/mono-analytic inputs. See the spec’s
  “Honesty boundary.”

## Current status / open questions

- P0 specification and repository bootstrap are complete locally and await
  reviewer acceptance before P1.
- The comparator headline is the self-contained ramification-error sum bound
  from the numerical core of Proposition 1.4(iii).
- Proposition 1.8(v)–(vii) requires an explicit conditional reduction
  certificate until missing moduli/Néron-model infrastructure is formalized.

## Work log

### 2026-07-19 — P0 specification-authoring run

- Goal: inspect the paper, template repository, and scaffold; write the
  phase-gated implementation specification; initialize and commit the repo.
- Changed: added `Plans/Iut4Sec1Spec.md` and this work log; retained the existing
  scaffold and reference files unchanged.
- Decisions: separated self-contained local/measure arithmetic from explicit
  IUT I–III interfaces; selected
  `Iut4Sec1.nonarchimedean_logError_sum_le` for comparator.
- Checks: `lake env lean Iut4Sec1/Basic.lean`, `lake build Iut4Sec1`,
  `lake build`, `git diff --check`, and final status audit (recorded at handoff).
- Commit: `P0: bootstrap repository and specification` (see `git log -1`).
- Next: reviewer accepts P0, then an implementer starts P1 only.

### 2026-07-19 — P0 specification revision after review round 1

- Goal: resolve all seven findings in `.pi/parallel-review.md` without starting
  any implementation phase.
- Changed: rewrote `Plans/Iut4Sec1Spec.md`; recorded the round-1 verdict in its
  Review log. No file outside `Plans/` changed.
- Decisions: P3 simultaneously adds the comparator theorem and turns Solution
  into a re-export; exact Proposition 1.6 uses an explicit non-IUT
  `PrimeCountingCertificate` while Chebyshev yields a weaker unconditional
  theorem; the final signature carries all five IUT packages, the finite
  `ReductionCertificate` family, and `PrimeCountingCertificate`; local-field
  and elliptic work now has reviewed GO/NO-GO prototype gates.
- API recheck: confirmed mathlib v4.32.0's
  `Chebyshev.eventually_primeCounting_le` coefficient `log 4 + ε`, local
  completion/DVR support, lack of the required general p-adic log/exp package,
  the scope of the Dedekind different API, and the limited Weierstrass good
  reduction API.
- Checks: `lake build` and `git diff --check` passed; only `.lake/` and `.pi/`
  are ignored.
- Commit: `P0: revise specification per review round 1` (this commit; see
  `git log -1`).
- Next: obtain P0 review round 2 acceptance; do not begin P1 before that gate.
