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
  importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    
    {module:= `LeanCodePrompts.VerboseDelabs},
    {module:= `LeanAide.Premises},
    {module := `Mathlib}] {}

def environment' : IO Environment := do
  importModules [{module := `Mathlib},
    {module:= `LeanCodePrompts.CheckParse},
    
    {module:= `LeanAide.ConstDeps},
    {module := `Mathlib}] {}

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }   

def main (args: List String) : IO Unit := do
  init
  let env ← environment
  let dir := System.mkFilePath <| [".", "rawdata", "defn-types"]
  if !(← dir.pathExists) then
        IO.FS.createDirAll dir
  let path := System.mkFilePath ["rawdata", "defn-types", "all.jsonl"]
  let propMap ← if ← path.pathExists then 
        let lines ←  IO.FS.lines path
        let lines := lines.filterMap (fun l => (Lean.Json.parse l).toOption)
        let dfns : Array DefnTypes := 
          lines.filterMap (fun l=>  (fromJson? l).toOption)
        let propList := dfns.toList.filter (·.isProp) |>.map (fun d => (d.name.toString, d.type))
        pure <| HashMap.ofList propList
    else 
        IO.println s!"File {path} not found, running to generate it"
        propMapCore.run' coreContext {env := env} |>.runToIO'
  -- IO.println s!"Success: ran to {propMap.size}"
  let names := args.map String.toName
  let handles ← fileHandles false
  -- IO.println "Writing batch"
  let testCore := 
    PremiseData.writeBatchCore (names) "extra" handles propMap "" true
  discard <| testCore.run' coreContext {env := env} |>.runToIO'  
  IO.println ""
  let rawLines := (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "extra.jsonl"])).filter (fun l => l != "")
  let jsLines := rawLines.filterMap <| fun l => (Lean.Json.parse l).toOption
  -- IO.println <| ← IO.FS.readFile (System.mkFilePath ["rawdata", "premises", "core", "extra.jsonl"]) 
  for name in names do
    let stxCore :=  nameViewCore? name 
    let stx ← stxCore.run' coreContext {env := ← environment'} |>.runToIO'
    IO.println s!"\nname: {name}"
    IO.println s!"\nexpression: \n{stx}"
    let verboseCore := verboseViewCore? name
    let view ← verboseCore.run' coreContext {env := env} |>.runToIO'
    IO.println s!"\nverbose: \n{view}" 
  for l in jsLines do
    IO.println ""
    IO.println l.pretty
  return ()
