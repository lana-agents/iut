import Solution
import Lean.Util.CollectAxioms

/-!
# Comparator-solution logical-dependency audit

This file audits the theorem exported by `Solution` in its separate environment.
-/

open Lean Elab Command

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

run_cmd liftCoreM do
  let declName := ``Iut4Sec1.nonarchimedean_logError_sum_le
  let dependencies := sortNames (← collectAxioms declName)
  logInfo "solution-exported declaration\tlogical dependencies"
  logInfo m!"{declName}\t{String.intercalate ", "
    (dependencies.toList.map Name.toString)}"
  let forbidden := dependencies.filter fun name => !allowedAxioms.contains name
  unless forbidden.isEmpty do
    throwError "disallowed comparator-solution logical dependencies: {declName}: {String.intercalate ", "
      (forbidden.toList.map Name.toString)}"
  logInfo "audited the theorem exported by Solution"
