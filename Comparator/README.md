# Comparator suite: IUT IV Section 1

This directory contains the mathlib-only Section 1 challenge selected in
§3 of `Plans/Iut4Sec1Spec.md`. `Challenge.lean` has ten theorem targets, each
with one proof placeholder. Its auxiliary definitions are statement vocabulary,
not comparator tasks.

`Solution.lean` is import/re-export only: it currently imports the proved project
theorem from P3 and declares no wrappers. Challenge and Solution are separate
Lake roots and must never be imported into the same Lean environment.

## Target and config schedule

| Challenge target | Project proving phase | Config status after P3b |
|---|---:|---|
| `Iut4Sec1.nonarchimedean_logError_sum_le` | P3 (complete) | included |
| `Iut4Sec1.weighted_average_eq` | P4 | not yet included |
| `Iut4Sec1.average_range_sum` | P4 | not yet included |
| `Iut4Sec1.average_range_sq_sum` | P4 | not yet included |
| `Iut4Sec1.normalizedArithmeticDivisorDegree_nonneg` | P4 | not yet included |
| `Iut4Sec1.localParameters_eq_of_smallRamification` | P6 | not yet included |
| `Iut4Sec1.nonarchimedean_secondError_sum_le` | P11 | not yet included |
| `Iut4Sec1.complexTensorToProd_bijective` | P12 | not yet included |
| `Iut4Sec1.complexTensorToProd_normSq` | P12 | not yet included |
| `Iut4Sec1.eventually_primeCounting_le_four_thirds` | no unconditional phase | never under the current honesty boundary |

`config.json` therefore keeps `theorem_names` equal to
`["Iut4Sec1.nonarchimedean_logError_sum_le"]`. A target enters that array only
when Solution exports a project proof with exactly the challenge type. The exact
`4 / 3` prime-counting target remains outside config because the planned project
result requires an explicit `PrimeCountingCertificate`.

`scripts/check_comparator_signature.sh` builds isolated public declaration
manifests for the two roots, intersects them, compares the complete elaborated
types of every shared declaration, and checks that the config names are exactly
the shared theorem targets currently exported by Solution.
