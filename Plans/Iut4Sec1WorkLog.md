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

- P0 specification and repository bootstrap are accepted.
- P1 is complete locally through the review-round-2 fixes and awaits re-review
  before P2.
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

### 2026-07-19 — P1 Verso scaffold and trust-audit infrastructure

- Goal/status: completed P1 only; no comparator or mathematical formalization
  from P2 or later was added.
- Changed: added the self-contained `blueprint-verso/` package at Lean 4.32.0,
  ten source-faithful nodes for items 1.1--1.10, site-generation scripts and
  workflows, and the three trust-audit files under `scripts/`.
- Honesty labels: item 1.6 is conditional on `PrimeCountingCertificate`; item
  1.8 is conditional/partial and labels clauses (v)--(vii) with
  `ReductionCertificate`; item 1.10 labels the five IUT I--III packages,
  `PrimeCountingCertificate`, and the `ReductionCertificate` family as explicit
  conditions.
- Negative-test evidence: temporarily added the ignored
  `.pi/probes/Iut4Sec1/TrustProbe.lean`, imported it through a temporary symlink,
  and gave `contaminatedPublicDeclaration` a placeholder proof. The all-public
  audit exited 1 and reported
  `contaminatedPublicDeclaration\tsorryAx` followed by
  `disallowed logical dependencies: contaminatedPublicDeclaration: sorryAx`.
  The probe, symlink, and temporary root import were removed, and the clean root
  was rebuilt.
- Checks: `(cd blueprint-verso && lake update)`; `(cd blueprint-verso && lake
  build Iut4Sec1Blueprint)`; `./blueprint-verso/scripts/ci-pages.sh`; explicit
  checks for `index.html`, `blueprint-manifest.json`, and
  `blueprint-html-cache.json` (the manifest contains ten previews); root `lake
  build`; `./scripts/audit_trust.sh`; `./scripts/audit_axioms.sh`; and `git diff
  --check` all passed. Only `.lake/`, `.pi/`, `blueprint-verso/.lake/`, and
  `blueprint-verso/_out/` appear in ignored status.
- Commit: `P1: add Verso scaffold and trust audits` (this phase commit; see
  `git log -1` for its local hash).
- Next: submit P1 for review; do not start P2 before acceptance.

### 2026-07-19 — P1 review round 1 fixes

- Goal/status: resolved findings 1--4 from `.pi/parallel-review.md`; P1 now
  awaits re-review, and no P2 work was started.
- Changed: made PR blueprint builds unprivileged (`pull_request`,
  `contents: read`), restricted `contents: write` to the push-to-main deploy
  job, and removed the obsolete PR-preview deploy/cleanup paths. Reworked
  `scripts/audit_trust.sh` to use literal `(path, line, token, reason)` records,
  reject glob/directory exceptions, and reject ignored `.pi/**/*.lean` outside
  explicit P5/P14 probe mode. Restored the distinguished
  `i^\dagger \in I` and `\lambda \in (1/e_{i^\dagger})\mathbb Z` hypothesis in
  Proposition 1.4(iii), and corrected the current-status section above.
- Feasibility-mode policy: ignored Lean files are allowed only below
  `.pi/probes/` when the audit is invoked with
  `AUDIT_FEASIBILITY_PHASE=P5` or `AUDIT_FEASIBILITY_PHASE=P14`; any such use
  must be recorded in the phase work-log entry. Feasibility mode was not
  enabled during this P1 fix round; `AUDIT_FEASIBILITY_PHASE=P1` was checked
  and rejected with exit 1.
- Required negative test: created ignored
  `.pi/P1ReviewerTrustEvasion.lean` containing `axiom X : False`. The audit
  exited 1 with:

  ```text
  audit_trust: ignored .pi Lean source is not permitted outside explicit P5/P14 feasibility mode: .pi/P1ReviewerTrustEvasion.lean
  audit_trust: rejected token: .pi/P1ReviewerTrustEvasion.lean:1: axiom
  audit_trust: trust audit failed
  ```

  The probe was deleted, and the clean trust audit passed again.
- Checks: `(cd blueprint-verso && lake build Iut4Sec1Blueprint)`,
  `./blueprint-verso/scripts/ci-pages.sh`, nonempty site/manifest/cache checks
  with exactly ten manifest previews and ten cache entries, root `lake build`,
  `./scripts/audit_trust.sh`, `./scripts/audit_axioms.sh`, and both range/current
  `git diff --check` checks passed.
- Commit: `P1: address review round 1 findings` (this fix-round commit; see
  `git log -1` for its local hash).
- Next: request P1 re-review; do not begin P2 until acceptance.

### 2026-07-19 — P1 review round 2 fixes

- Goal/status: fixed only the two new findings in `.pi/parallel-review.md`:
  write/OIDC privileges in pull-request Lean CI and symlink evasion under the
  `.pi` trust-audit boundary. No blueprint or P2 files changed.
- Changed: `.github/workflows/lean_action_ci.yml` now gives the PR-capable
  `build` job only `contents: read`; the Pages/OIDC-enabled `deploy-docs` job
  runs only after a successful build on a push to `refs/heads/main`.
  `scripts/audit_trust.sh` now rejects every symlink below `.pi` before
  considering P5/P14 feasibility exceptions.
- Permanent symlink negative-test evidence: linked the ignored
  `.pi/P1SymlinkEvasion.lean` to a temporary file containing
  `axiom X : False`. The audit exited 1 with:

  ```text
  audit_trust: symlink is not permitted under .pi: .pi/P1SymlinkEvasion.lean
  audit_trust: trust audit failed
  ```

  A non-Lean-named symlink at `.pi/probes/P1NonLeanSymlinkEvasion` also exited
  1 under `AUDIT_FEASIBILITY_PHASE=P5`, confirming that feasibility mode does
  not bypass the all-symlink rejection. Both probes and targets were removed;
  the clean trust audit then passed.
- Checks: root `lake build`, `./scripts/audit_trust.sh`,
  `./scripts/audit_axioms.sh`, `bash -n scripts/audit_trust.sh`, and
  `git diff --check` all passed. The blueprint site was not rebuilt because no
  blueprint files changed.
- Commit: `P1: address review round 2 findings` (this fix-round commit; see
  `git log -1` for its local hash).
- Next: request P1 re-review; do not begin P2 until acceptance.

### 2026-07-19 — P2 comparator challenge and temporary independent solution

- Goal/status: completed P2 only. Added the mathlib-only comparator challenge
  and temporary independent solution for
  `Iut4Sec1.nonarchimedean_logError_sum_le`; no P3 project theorem or solution
  re-export was started.
- Changed: added `Comparator/{README.md,Challenge.lean,Solution.lean,config.json}`,
  separate `Challenge`/`Solution` Lake roots, the duplicate-root-aware
  `CheckDecls.lean` executable, and the read-only comparator workflow. Extended
  the axiom audit to inspect `Solution` in its own environment.
- Identity/security: after stripping imports and module documentation, the two
  comparator declaration bodies are byte-identical (527 bytes). Neither root
  imports `Iut4Sec1`, and no file imports both. The workflow has only
  `contents: read` permission and no write or OIDC credentials.
- Temporary exception: `scripts/audit_trust.sh` has the literal P2 record
  `Comparator/Solution.lean|21|sorry|Temporary P2 independent-solution placeholder; remove in P3 when Solution re-exports the project theorem`.
  The separate solution logical-dependency audit likewise permits its one
  temporary `sorryAx` dependency. Both allowances expire in P3.
- Checks: `lake env lean Comparator/Challenge.lean`; `lake env lean
  Comparator/Solution.lean`; `lake build Challenge`; `lake build Solution`;
  `lake build checkdecls`; `lake build`; challenge `#print axioms` (listed
  `sorryAx`, with the three permitted standard axioms); `./scripts/audit_trust.sh`;
  `./scripts/audit_axioms.sh`; `git diff --check`; and
  `git diff --cached --check` all passed. A smoke test of `lake exe checkdecls`
  against `hello` also passed.
- Commit: `P2: add comparator challenge infrastructure` (local phase commit;
  use `git log -1 --format=%h` for its hash).
- Next: submit P2 for review. P3 must simultaneously add the project proof,
  replace `Solution.lean` by the specified re-export, and remove both temporary
  P2 allowances.

### 2026-07-19 — P3 comparator arithmetic and solution re-export

- Goal/status: completed P3 only. Proved the finite-sum ramification-error
  comparator theorem and did not begin P4.
- Changed: added `Iut4Sec1/Real/LogError.lean` with the ceiling-error definition,
  three pointwise lemmas, and `nonarchimedean_logError_sum_le`; imported it from
  `Iut4Sec1.lean`; replaced `Comparator/Solution.lean` by a direct project import
  and `#check`; removed the P2 trust/logical-dependency allowances; and added
  `scripts/check_comparator_signature.sh` with isolated Challenge/Solution
  fixtures. Added declaration links only to blueprint items 1.2 and 1.4 and the
  root package path dependency needed to resolve them.
- Proof route: positivity gives a positive ratio and ceiling at least one;
  `Int.ceil_lt_add_one` gives error strictly below `1/(p-2)`, which is at most
  `4/p`; the error vanishes when `e ≤ p-2`; the sum is bounded pointwise and
  filtered to `Istar` using `Istar ⊆ I`.
- Checks: project module/root, Challenge, Solution, and default `lake build`
  passed; the comparator signature diff was empty; project-imported and
  Solution-exported axiom prints both listed exactly `propext`,
  `Classical.choice`, and `Quot.sound`; trust and all-public axiom audits passed;
  the nested blueprint build, `ci-pages.sh`, nonempty site/manifest/cache checks,
  and checks for all five linked declaration names passed; `git diff --check`
  passed.
- Commit: `P3: prove comparator arithmetic and re-export solution` (this phase
  commit; use `git log -1 --format=%h` for its local hash).
- Next: submit P3 for review; do not begin P4 before acceptance.
