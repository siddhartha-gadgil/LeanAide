import Lean.Meta
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def block (name: Name)(js: Json) : Option String :=
  let desc? := js.getObjValAs? String "description"
  let statement? := js.getObjValAs? String "statement"
  match desc?, statement? with
  | Except.ok desc, Except.ok statement =>
    let statement := if (statement.splitOn "/--").length > 0 then statement.splitOn "-/" |>.getD 1 (statement) else statement

    let statement := statement.replace ":= by sorry" ""
    some s!"<tr><td><h4>Name: {name}</h4>\n<h5>{statement}</h5>\n<p>{desc}</p>\n</td></tr>\n"
  | _, _ => none

def main : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  let env ←
    importModules #[
    {module := `Mathlib},
    {module := `LeanAide.ConstDeps}] {}
  let dataPath : System.FilePath := ("rawdata"/ "premises" / "ident_pairs"/"descriptions.jsonl")
  let jsData ←
      IO.FS.lines dataPath
  let data :=  jsData.filterMap (fun js => Json.parse js |>.toOption)
  let dataMapArr := data.filterMap (fun js =>
    match js.getObjValAs? String "name" with
    | Except.error _ => none
    | Except.ok name => some (name, js))
  let dataMap : HashMap Name Json := HashMap.ofList dataMapArr.toList
  let core := modulePairs
  let mp ← core.run' coreContext {env := env} |>.runToIO'
  IO.println s!"{mp.size} module pairs"
  IO.println s!"{dataMap.size} descriptions"
  let head ← IO.FS.readFile (System.mkFilePath ["resources", "desc_head.html"])
  let tail ← IO.FS.readFile (System.mkFilePath ["resources", "desc_tail.html"])
  IO.FS.writeFile (System.mkFilePath ["rawdata", "docs", "index.html"]) head
  let indexHandle ← IO.FS.Handle.mk (System.mkFilePath ["rawdata", "docs", "index.html"]) IO.FS.Mode.append
  indexHandle.putStrLn "<ul class=\"lead\">"
  for i in [0:50] do
    let (module, consts) := mp.get! i
    let mut counts := 0
    let file := System.mkFilePath ["rawdata", "docs", s!"{module}.html"]
    IO.FS.writeFile file head
    let h ← IO.FS.Handle.mk file IO.FS.Mode.append
    IO.println s!"Module: {module}"
    h.putStrLn s!"<h2>Module: {module}</h2>\n<table class=\"table table-striped\">\n<tbody>"
    for n in consts do
      match dataMap.find? n with
      | some js =>
        match block n js with
        | some ul =>
          IO.println ul
          h.putStr ul
          counts := counts + 1
        | none =>
          -- IO.println s!"skipped (no description): {n}"
          pure ()
      | none =>
          -- IO.println s!"skipped (no data): {n}"
          pure ()
    h.putStrLn "</tbody>\n</table>"
    h.putStrLn tail
    h.flush
    if counts > 0 then
      indexHandle.putStrLn s!"<li><a href=\"{module}.html\">{module}</a></li>"

    IO.println "-----------------"
  indexHandle.putStrLn "</ul>"
  indexHandle.putStrLn tail
