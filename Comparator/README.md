# Comparator core: Proposition 1.4(iii) arithmetic

This directory contains a [leanprover/comparator](https://github.com/leanprover/comparator)
challenge/solution pair for the finite-sum ramification-error estimate used in
Proposition 1.4(iii), `Iut4Sec1.nonarchimedean_logError_sum_le`. This estimate is
the **comparator core**, rather than Section 1's headline result.

For the pointwise bound put `d = p - 2 > 0`. Positivity of `e` gives
`ceil (e / d) - 1 < e / d`, hence the error is `< 1 / d ≤ 4 / p` for
`p ≥ 3`; if `e ≤ d`, then `0 < e / d ≤ 1`, so the ceiling is exactly `1` and
the error is zero. Summing over the complement of the small indices gives the
stated estimate.

- `Challenge.lean` imports only `Mathlib` and states the comparator core with
  the permanent challenge placeholder.
- `Solution.lean` also imports only `Mathlib` during P2 and contains an
  independent copied declaration with a temporary placeholder. In P3 it expires
  and this file will import/re-export the project proof.
- `config.json` names the challenge and solution modules and the theorem checked
  by comparator.

`Challenge` and `Solution` are separate Lake roots and must never be imported
into the same Lean environment.
