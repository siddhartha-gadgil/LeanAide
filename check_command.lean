import Mathlib
import Lean
import LeanAide.SimpleFrontend

open Lean LeanAide

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true)  #[{module := `Mathlib, importAll := true}] {} (trustLevel := 1)
  let text := "example : ∀ (G : Type) [Group G], ∀ a b : G, a * b = b * a := by sorry"
  let text := args[0]? |>.getD text
  let (_, logs) ← simpleRunFrontend text env
  logToStdErr `leanaide.translate.info "Ran dummy example to load Mathlib"
  for log in logs.toList do
    logToStdErr `leanaide.translate.info s!"{←  log.toString}"
