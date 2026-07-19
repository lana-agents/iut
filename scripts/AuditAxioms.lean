import Iut4Sec1
import Lean.Util.CollectAxioms
import Mathlib.Tactic.Linter.PrivateModule

open Lean Elab Command

private def auditedRoot : Name := `Iut4Sec1

private def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

private def inAuditedRoot (moduleName : Name) : Bool :=
  moduleName == auditedRoot || auditedRoot.isPrefixOf moduleName

private def isAuditedPublicName (env : Environment) (declName : Name) : Bool :=
  !isPrivateName declName && !isReservedName env declName

private def visitedDeclarations : CoreM (Array Name) := do
  let env ← getEnv
  env.constants.foldM (init := #[]) fun names declName _ => do
    let some moduleName ← findModuleOf? declName | return names
    if inAuditedRoot moduleName && isAuditedPublicName env declName then
      return names.push declName
    return names

private def compiledManifest : CoreM (Array Name) := do
  let env ← getEnv
  let mut names := #[]
  for h : moduleIdx in *...env.header.moduleNames.size do
    let moduleName := env.header.moduleNames[moduleIdx]
    if inAuditedRoot moduleName then
      for declName in env.header.moduleData[moduleIdx]!.constNames do
        if isAuditedPublicName env declName then
          names := names.push declName
  return names

private def sortNames (names : Array Name) : Array Name :=
  names.qsort fun left right => left.toString < right.toString

private def renderNames (names : Array Name) : String :=
  String.intercalate "\n" ((sortNames names).toList.map Name.toString) ++ "\n"

private def writeSelectedNames (names : Array Name) : CommandElabM Unit := do
  let some output ← IO.getEnv "IUT4_SEC1_AUDIT_OUTPUT" |
    throwError "IUT4_SEC1_AUDIT_OUTPUT is required in manifest mode"
  IO.FS.writeFile output (renderNames names)

run_cmd do
  let mode ← IO.getEnv "IUT4_SEC1_AUDIT_MODE"
  match mode with
  | some "manifest" =>
      writeSelectedNames (← liftCoreM compiledManifest)
  | some "visited" =>
      writeSelectedNames (← liftCoreM visitedDeclarations)
  | _ => liftCoreM do
      let declarations := sortNames (← visitedDeclarations)
      if declarations.isEmpty then
        throwError "all-public audit selected no Iut4Sec1 declarations"
      let mut violations : Array (Name × Array Name) := #[]
      logInfo "declaration\tlogical dependencies"
      for declName in declarations do
        let dependencies := sortNames (← collectAxioms declName)
        logInfo m!"{declName}\t{String.intercalate ", "
          (dependencies.toList.map Name.toString)}"
        let forbidden := dependencies.filter fun name => !allowedAxioms.contains name
        unless forbidden.isEmpty do
          violations := violations.push (declName, forbidden)
      unless violations.isEmpty do
        let messages := violations.toList.map fun (declName, dependencies) =>
          s!"{declName}: {String.intercalate ", "
            (dependencies.toList.map Name.toString)}"
        throwError "disallowed logical dependencies:\n{String.intercalate "\n" messages}"
      logInfo m!"audited {declarations.size} public Iut4Sec1 declaration(s)"
