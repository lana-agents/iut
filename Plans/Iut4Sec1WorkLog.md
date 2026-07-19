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
