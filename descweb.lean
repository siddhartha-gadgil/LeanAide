import Lean.Meta
import LeanAide.Config
import LeanAide.Descriptions
open Lean LeanAide.Meta

set_option maxHeartbeats 10000000
set_option maxRecDepth 1000
set_option compiler.extract_closed false

def coreContext : Core.Context := {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 1000000
    }

def block? (name: Name)(js: Json) : Option String :=
  let desc? := js.getObjValAs? String "description"
  let statement? := js.getObjValAs? String "statement"
  match desc?, statement? with
  | Except.ok desc, Except.ok statement =>
    let concise :=
      match js.getObjValAs? String "concise-description" with
      | Except.ok cd => cd
      | Except.error _ =>
        panic!"No concise description for {name}"
    let statement := statement.replace ":= by sorry" ""
    let statement := statement.replace "by sorry" "" |>.trim
    let statement := if statement.endsWith ":=" then statement.dropRight 2 else statement
    let statement := if (statement.splitOn "/--").length > 0 then statement.splitOn "-/" |>.getD 1 (statement) else statement
    some s!"<tr><td><h4><code>{name}</code></h4>\n<h5>{statement}</h5>\n<p>{desc}</p>\n<p>More concisely: <em>{concise}</em></p>\n</td></tr>\n"
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
  let dataMap : HashMap String Json := HashMap.ofList dataMapArr.toList
  let core := modulePairs
  let mp ← core.run' coreContext {env := env} |>.runToIO'
  IO.println s!"{mp.size} module pairs"
  IO.println s!"{dataMap.size} descriptions"
  let head ← IO.FS.readFile (System.mkFilePath ["resources", "desc_head.html"])
  let tail ← IO.FS.readFile (System.mkFilePath ["resources", "desc_tail.html"])
  IO.FS.writeFile (System.mkFilePath ["rawdata", "docs", "index.html"]) head
  let indexHandle ← IO.FS.Handle.mk (System.mkFilePath ["rawdata", "docs", "index.html"]) IO.FS.Mode.append
  indexHandle.putStrLn "<ul class=\"lead\">"
  let mut moduleCount := 1
  let mp := mp.qsort (fun a b => toString a.1 < toString b.1)
  for pair in mp do
    let (module, consts, docs) := pair
    let mut count := 0
    let file := System.mkFilePath ["rawdata", "docs", s!"{module}.html"]
    IO.FS.writeFile file head
    let h ← IO.FS.Handle.mk file IO.FS.Mode.append
    IO.println s!"Module: {module} ({moduleCount} of {mp.size})"
    h.putStrLn s!"<h3>Module: {module}</h3>"
    for doc in docs do
      h.putStrLn s!"<zero-md><script type=\"text/markdown\">\n{doc}\n</script></zero-md>"
      h.putStrLn "<hr>"
    h.putStrLn "<table class=\"table table-striped\">\n<tbody>"
    for n in consts do
      match dataMap.find? (toString n) with
      | some js =>
        match block? n js with
        | some ul =>
          -- IO.println ul
          h.putStr ul
          count := count + 1
        | none =>
          -- IO.println s!"skipped (no description): {n}"
          pure ()
      | none =>
          -- IO.println s!"skipped (no data): {n}"
          pure ()
    h.putStrLn "</tbody>\n</table>"
    h.putStrLn tail
    h.flush
    moduleCount := moduleCount + 1
    if count > 0 then
      indexHandle.putStrLn s!"<li><a href=\"{module}.html\">{module}</a></li>"

    -- IO.println "-----------------"
  indexHandle.putStrLn "</ul>"
  indexHandle.putStrLn tail
  indexHandle.flush
