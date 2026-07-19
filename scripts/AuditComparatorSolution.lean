import Solution
import Lean.Util.CollectAxioms

/-!
# Comparator-solution logical-dependency audit

This file audits the configured theorems exported by `Solution` in its separate environment.
-/

open Lean Elab Command

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

private def configuredTheorems : List Name :=
  [``Iut4Sec1.nonarchimedean_logError_sum_le,
    ``Iut4Sec1.weighted_average_eq,
    ``Iut4Sec1.average_range_sum,
    ``Iut4Sec1.average_range_sq_sum,
    ``Iut4Sec1.normalizedArithmeticDivisorDegree_nonneg]

run_cmd liftCoreM do
  logInfo "solution-exported declaration\tlogical dependencies"
  for declName in configuredTheorems do
    let dependencies := sortNames (← collectAxioms declName)
    logInfo m!"{declName}\t{String.intercalate ", "
      (dependencies.toList.map Name.toString)}"
    let forbidden := dependencies.filter fun name => !allowedAxioms.contains name
    unless forbidden.isEmpty do
      throwError "disallowed comparator-solution logical dependencies: {declName}: {String.intercalate ", "
        (forbidden.toList.map Name.toString)}"
  logInfo m!"audited {configuredTheorems.length} theorems exported by Solution"
