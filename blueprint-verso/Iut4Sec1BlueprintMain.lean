import VersoManual
import VersoBlueprint.PreviewManifest
import Iut4Sec1Blueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Iut4Sec1Blueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
