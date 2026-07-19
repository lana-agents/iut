import Solution
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter.PrivateModule

/-!
# P2 comparator-solution logical-dependency audit

The duplicate comparator roots cannot share an environment. This audit visits every
public declaration defined by `Solution` alone. Its temporary P2 logical dependency
allowance expires when P3 replaces that module with the project theorem re-export.
-/

open Lean Elab Command

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice, ``sorryAx]

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

run_cmd liftCoreM do
  let env ← getEnv
  let mut declarations := #[]
  for (declName, _) in env.constants.toList do
    if (← findModuleOf? declName) == some `Solution &&
        !isPrivateName declName && !isReservedName env declName then
      declarations := declarations.push declName
  let sortedDeclarations := sortNames declarations
  if sortedDeclarations.isEmpty then
    throwError "comparator solution audit selected no declarations"
  let mut violations : Array (Name × Array Name) := #[]
  let mut foundTemporaryDependency := false
  logInfo "solution declaration\tlogical dependencies"
  for declName in sortedDeclarations do
    let dependencies := sortNames (← collectAxioms declName)
    logInfo m!"{declName}\t{String.intercalate ", "
      (dependencies.toList.map Name.toString)}"
    if dependencies.contains ``sorryAx then
      foundTemporaryDependency := true
    let forbidden := dependencies.filter fun name => !allowedAxioms.contains name
    unless forbidden.isEmpty do
      violations := violations.push (declName, forbidden)
  unless foundTemporaryDependency do
    throwError "the temporary P2 comparator-solution dependency was not found"
  unless violations.isEmpty do
    let messages := violations.toList.map fun (declName, dependencies) =>
      s!"{declName}: {String.intercalate ", "
        (dependencies.toList.map Name.toString)}"
    throwError "disallowed comparator-solution logical dependencies:\n{String.intercalate "\n" messages}"
  logInfo m!"audited {sortedDeclarations.size} public Solution declaration(s)"
