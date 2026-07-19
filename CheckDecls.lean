import Lake.CLI.Main

/-!
# Blueprint declaration checker

Local replacement for the `checkdecls` executable from
https://github.com/PatrickMassot/checkdecls. The upstream version imports the roots of
every `lean_lib` into one environment. That fails here because `Challenge` and
`Solution` declare the same comparator names. This version excludes those two roots.
-/

open Lake Lean

/-- Library roots omitted because their declaration names overlap by design. -/
def excludedLibs : Array Name := #[`Challenge, `Solution]

def main (args : List String) : IO UInt32 := do
  unless args.length == 1 do
    println! "This command takes exactly one argument: \
      the path to a file containing a list of declarations to check."
    return 1
  let filename : System.FilePath := args[0]!
  unless ← filename.pathExists do
    println! "Could not find declaration list {filename}."
    return 1
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let config ← MonadError.runEIO <| mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let (ws?, log) ← (loadWorkspace config).run?
  log.replay (logger := .stderr)
  let some ws := ws? | return 1
  let libs := ws.root.leanLibs.filter fun lib ↦ !excludedLibs.contains lib.name
  let imports := libs.flatMap (·.config.roots.map fun module ↦ { module })
  let env ← Lean.importModules imports {}
  let mut ok := true
  for line in ← IO.FS.lines filename do
    unless env.contains line.toName do
      println! "{line} is missing."
      ok := false
  return if ok then 0 else 1
