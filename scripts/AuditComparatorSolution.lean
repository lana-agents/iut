/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Solution
import Lean.Util.CollectAxioms

/-!
# Comparator-solution logical-dependency audit

This file audits the configured theorem of `Solution`, `Iut.classicalABC_of_cor312Variant`,
in its separate environment.
-/

open Lean Elab Command

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

private def configuredTheorems : List Name :=
  [``Iut.classicalABC_of_cor312Variant]

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
