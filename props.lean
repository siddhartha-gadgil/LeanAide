import LeanAide.Premises
import Lean.Meta
import LeanAide.Config
open Lean Meta LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def init : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles

def environment : IO Environment := do
  importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanAide.VerboseDelabs},
    {module:= `LeanAide.Premises},
    {module := `Mathlib}] {}

def environment' : IO Environment := do
  importModules #[{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanAide.ConstDeps},
    {module := `Mathlib}] {}


def coreContext : Core.Context := {fileName := "", fileMap := {source:= "", positions := #[]}, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }

def main (_: List String) : IO Unit := do
  init
  let env' ← environment'
  let propMap ←
    propMapCore.run' coreContext {env := env'} |>.runToIO'
  IO.println s!"Obtained prop-map: {propMap.size} entries"
  return ()
