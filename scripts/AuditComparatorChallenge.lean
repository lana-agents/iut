/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import Challenge
import Lean.Util.CollectAxioms

/-!
# Comparator-challenge trust audit

The comparator trusts `Challenge` and its whole import closure. This file checks, in the
challenge's own environment, that this closure is statement-only:

* none of the modules that prove the main theorem is imported (`Iut.MainTheorem`,
  `Iut.Tripod`, `Iut.Implication`, `Iut.Abc`), and none of the declarations of the proof
  chain is present;
* no safe declaration of the closure, Lean's core included, and no declaration of
  `Challenge` other than the challenge theorem (the definition `ABC`, the copied definition
  `ABC.radical` and the auxiliary matcher of the set-builder) refers directly to any axioms
  other than `propext`, `Classical.choice` and `Quot.sound`; in particular none refers to
  `sorryAx` or to the compiler-trust axioms. Since every
  transitive dependency on such axioms passes through a direct reference, no declaration of
  the closure depends on them;
* no module outside Lean's core declares axioms;
* the challenge theorem itself depends on `sorryAx` (its placeholder) and otherwise only on
  `propext`, `Classical.choice` and `Quot.sound`.

It prints the project modules of the closure, grouped by package.
-/

open Lean Elab Command

private def challengeModule : Name := `Challenge

private def challengeTheorem : Name := `Iut.abc_of_cor312Variant

/-- Module prefixes of the proof of the main theorem; none may be imported. -/
private def forbiddenModulePrefixes : List Name :=
  [`Iut.MainTheorem, `Iut.Tripod, `Iut.Implication, `Iut.Abc]

/-- Declarations of the proof chain of the main theorem; none may be present. -/
private def forbiddenDeclarations : List Name :=
  [`Iut.classicalABC_of_variant, `Iut.Tripod.abc_of_variant,
    `Iut.Tripod.statementI_of_statementII, `Iut.Tripod.classicalABC_of_statementI,
    `Iut.ClassicalABC, `Iut.formalConjecturesABC_of_variant, `Iut.classicalABC_iff_abc,
    `FormalConjecturesABC.abc]

/-- The definitions of `Challenge` that the statement uses; each must be present as a
definition, and is scanned in step 3 like every other declaration of the closure. -/
private def challengeDefinitions : List Name := [`ABC, `ABC.radical]

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def isCoreModule (moduleName : Name) : Bool :=
  [`Init, `Lean, `Std, `Lake].any (·.isPrefixOf moduleName)

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

/-- A declaration referred to by `e` that is one of the axioms outside `allowedAxioms`. -/
private def disallowedReference (env : Environment) (e : Expr) : Option Name :=
  e.foldConsts none fun c found => found <|>
    match env.find? c with
    | some (.axiomInfo _) => if allowedAxioms.contains c then none else some c
    | _ => none

run_cmd liftCoreM do
  let env ← getEnv
  let modules := env.header.moduleNames
  -- 1. The closure contains no module and no declaration of the proof.
  for moduleName in modules do
    if forbiddenModulePrefixes.any (·.isPrefixOf moduleName) then
      throwError "the challenge imports a proof module: {moduleName}"
  for declName in forbiddenDeclarations do
    if env.contains declName then
      throwError "the challenge environment contains a proof declaration: {declName}"
  -- 2. The project modules of the closure, by package (first name component).
  let mut packages : Std.HashMap Name Nat := {}
  for moduleName in modules do
    unless isCoreModule moduleName || moduleName == challengeModule do
      let root := moduleName.getRoot
      packages := packages.insert root (packages.getD root 0 + 1)
  logInfo m!"trusted import closure: {modules.size} modules"
  for root in sortNames (packages.toArray.map (·.1)) do
    logInfo m!"  {root}: {packages.getD root 0} modules"
  let iutModules := sortNames (modules.filter (`Iut).isPrefixOf)
  logInfo m!"Iut modules of the closure:\n{String.intercalate "\n" (iutModules.toList.map Name.toString)}"
  -- The statement definitions are present, as definitions of `Challenge`.
  for declName in challengeDefinitions do
    unless env.find? declName matches some (.defnInfo _) do
      throwError "the challenge does not define {declName}"
    unless env.getModuleFor? declName == some challengeModule do
      throwError "{declName} is not declared in {challengeModule}"
  -- 3. No declaration of the closure refers to disallowed axioms, and no module outside
  -- Lean's core declares axioms.
  let mut checked := 0
  for h : moduleIdx in *...modules.size do
    let moduleName := modules[moduleIdx]
    let isChallenge := moduleName == challengeModule
    for declName in env.header.moduleData[moduleIdx]!.constNames do
      -- The challenge theorem carries the placeholder; it is checked in step 4.
      if isChallenge && declName == challengeTheorem then continue
      let some info := env.find? declName | continue
      if info matches .axiomInfo _ then
        unless isCoreModule moduleName do
          throwError "the trusted closure declares axioms: {declName} ({moduleName})"
        continue
      -- Unsafe declarations cannot occur in the kernel-checked terms of safe ones.
      if info.isUnsafe then continue
      let found := (disallowedReference env info.type) <|>
        (info.value?.bind (disallowedReference env))
      if let some c := found then
        throwError "{declName} ({moduleName}) refers to {c}"
      checked := checked + 1
      if isChallenge && challengeDefinitions.contains declName then
        logInfo m!"{declName}: definition of {challengeModule}, refers only to allowed axioms"
  logInfo m!"no declaration of the trusted closure refers to axioms other than propext, \
    Classical.choice, Quot.sound ({checked} declarations checked)"
  -- 4. The challenge theorem: its placeholder is its only `sorryAx`.
  let dependencies := sortNames (← collectAxioms challengeTheorem)
  logInfo m!"{challengeTheorem}\t{String.intercalate ", " (dependencies.toList.map Name.toString)}"
  unless dependencies.contains ``sorryAx do
    throwError "{challengeTheorem} should carry its proof placeholder"
  let forbidden := dependencies.filter fun n => n != ``sorryAx && !allowedAxioms.contains n
  unless forbidden.isEmpty do
    throwError "{challengeTheorem} depends on {forbidden}"
