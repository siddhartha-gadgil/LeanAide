import Lean

open Lean Meta Elab Term

namespace LeanAide

structure TopCodeData where
  imports : List String
  codeLines : List String
deriving Inhabited

def TopCodeData.toString (tc : TopCodeData) : String :=
  let importsStr := String.intercalate "\n" tc.imports
  let codeStr := String.intercalate "\n" tc.codeLines
  s!"{importsStr}\n{codeStr}\n"

def topCodeData : TopCodeData :=
  { imports := ["import Mathlib"]
    codeLines := ["universe u v w u_1 u_2 u_3 u₁ u₂ u₃",
                   "set_option maxHeartbeats 10000000",
                   "set_option linter.unreachableTactic false",
                   "open scoped Nat"] }

initialize topDataExt :
    SimpleScopedEnvExtension TopCodeData TopCodeData ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m n =>
        n
    initial := topCodeData -- empty by default
  }

elab "#topCode" "[" imps:str,* "]" "[" lines:str,* "]" : command => Command.liftTermElabM do
    let imports := imps.getElems.map (·.getString)
    let codeLines := lines.getElems.map (·.getString)
    let newData := { imports := imports.toList, codeLines := codeLines.toList }
    topDataExt.add newData

def topCodeDataM : MetaM TopCodeData := do
  return topDataExt.getState (← getEnv)

def topCodeM : MetaM String := do
  let data ← topCodeDataM
  return data.toString

end LeanAide
