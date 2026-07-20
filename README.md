# iut

Inter-universal Teichmüller theory: the ABC/IUT trunk.

## Goals

This repository holds the IUT-specific material — the parts of the programme that are particular to Mochizuki's papers rather than independently established mathematics.

Its content is **the Corollary 3.12 variant**: a project-owner-specified variant of IUT III, Corollary 3.12 — initial Θ-data (IUT I, Definition 3.1), processions and tensor-packets of log-shells, the large volume container, its log-volume, and the holomorphic hull. It also carries the ABC target statement that the programme aims at.

Two neighbouring strands already have their own homes and are **not** developed here:

* **`genl`** — Mochizuki's *Arithmetic Elliptic Curves in General Position*, in [`LANA-Project/genl`](https://github.com/LANA-Project/genl).
* **IUT4 §1** — Section 1 of the fourth IUT paper, in [`LANA-Project/iut4-sec1`](https://github.com/LANA-Project/iut4-sec1). The analytic, reduction-theoretic and prime-counting inputs it needs sit behind explicit certificate interfaces, so that IUT4 §1 states its results conditionally and the certificates are discharged in `padic-log-volume`, `elliptic-reduction` and `prime-counting`.

## Scope boundary

The Corollary 3.12 strand is a **specification / formal-statement project only**. Proving the resulting proposition is explicitly out of scope. The formalisation must not silently identify the variant with Mochizuki's published Corollary 3.12, and must not encode any disputed implication as a proved theorem. Every assumption and specification boundary should be visible in the types.

The intended statement will differ in some respects from the formulation printed in the IUT papers; the precise data, hypotheses, definitions and conclusion are supplied per-issue by the project owner.

## Related repositories

Independently established inputs live in their own repositories so they can be developed, reviewed and potentially upstreamed to Mathlib on their own terms: `padic-log-volume`, `elliptic-reduction`, `prime-counting`, `tate-curves-theta`, `continuous-kummer-theory`, `local-class-field-theory`, `formal-schemes`, `tempered-fundamental-groups`, `belyi`.

## Layout

Lean 4 project pinned to `leanprover/lean4:v4.32.0` with Mathlib at `v4.32.0`.
Library sources live under `Iut/`, and every file must be imported from
the root module `Iut.lean`.

```bash
lake exe cache get                       # fetch the Mathlib build cache
lake build                               # build the library
lake exe mk_all --lib Iut --git   # regenerate the root module after adding files
```

## Validation

`.orchestra/` tells the agent harness how to prepare the environment and how to
check that a change is complete:

* `before.sh` warms the Mathlib build cache before work starts.
* `validation.sh` checks the worktree is clean, that every `.lean` file is
  imported (`mk_all --check`), and that everything builds with warnings as
  errors (`lake build --wfail`).

Run it locally with `bash .orchestra/validation.sh`.

## Tracker

Work is tracked in taxis: [#1](https://taxis.lana.merten.dev/issues/1), [#33](https://taxis.lana.merten.dev/issues/33), [#34](https://taxis.lana.merten.dev/issues/34), [#35](https://taxis.lana.merten.dev/issues/35), [#38](https://taxis.lana.merten.dev/issues/38), [#39](https://taxis.lana.merten.dev/issues/39), [#40](https://taxis.lana.merten.dev/issues/40), [#41](https://taxis.lana.merten.dev/issues/41), [#42](https://taxis.lana.merten.dev/issues/42), [#43](https://taxis.lana.merten.dev/issues/43), [#44](https://taxis.lana.merten.dev/issues/44), [#45](https://taxis.lana.merten.dev/issues/45)
