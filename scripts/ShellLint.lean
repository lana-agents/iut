/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Iut

/-!
# Shell lint (multiradial roadmap, MR0; criterion (L1))

Lists every `Prop`-valued field of every structure or class declared in the import closure of
the module imported above, outside the third-party roots (Lean core, Mathlib and its
dependencies). Each line has the form

`<structure>.<field>\t<module>`

and the list is sorted. A `Prop` field of a structure is either a *defining condition* of a
mathematical notion (allowed, e.g. the clauses of `IsFrobenioid`) or a *shell*: a property of an
IUT object that the papers prove, made into an input. `scripts/shell_lint.sh` compares this list
with the allowlist `scripts/shell_lint_allowlist.txt`.

`scripts/shell_lint.sh` runs a copy of this file in which the `import` line names the module
under audit; with the import line above, the audit covers the whole `Iut` library.
-/

open Lean Meta Elab Command

/-- Module roots that are not audited (the trusted third-party libraries). -/
private def thirdPartyRoots : List Name :=
  [`Init, `Lean, `Std, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible,
    `LeanSearchClient, `ImportGraph, `Cli]

private def isAudited (moduleName : Name) : Bool :=
  !thirdPartyRoots.contains moduleName.getRoot

/-- The `Prop`-valued fields of the structure `structName` (direct fields, parents excluded:
a parent structure is audited on its own). -/
private def propFields (structName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let mut out := #[]
  for field in getStructureFields env structName do
    if (`to).isPrefixOf field && (isSubobjectField? env structName field).isSome then
      continue
    let some projName := getProjFnForField? env structName field | continue
    let some info := env.find? projName | continue
    let isPropField ← forallTelescopeReducing info.type fun _ body => isProp body
    if isPropField then
      out := out.push field
  return out

run_cmd liftTermElabM do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (declName, _) in env.constants.toList do
    unless isStructure env declName do continue
    if isPrivateName declName then continue
    let some moduleIdx := env.getModuleIdxFor? declName | continue
    let moduleName := env.header.moduleNames[moduleIdx.toNat]!
    unless isAudited moduleName do continue
    for field in ← propFields declName do
      lines := lines.push s!"{declName}.{field}\t{moduleName}"
  let sorted := lines.qsort (· < ·)
  match ← IO.getEnv "SHELL_LINT_OUTPUT" with
  | some path => IO.FS.writeFile path (String.intercalate "\n" sorted.toList ++ "\n")
  | none => logInfo (String.intercalate "\n" sorted.toList)
