import Lean
import LeanAideCore.Aides
open System
namespace LeanAide

def callSimilaritySearch (query : String) (descField : String := "docString") (numSim : Nat := 10) : IO String := do
  let APIUrl := "http://localhost:7654/run-sim-search"
  let js := Lean.Json.mkObj [("num", numSim), ("query", query), ("descField", descField)]
  let inp ← IO.Process.output {cmd := "curl", args := #["--fail-with-body", "-X", "POST", APIUrl, "-H", "Content-Type: application/json", "-d", js.compress]}
  let ⟨err_code,stdout,stderr⟩ := inp
  match err_code with
  | 0 =>
    match Lean.Json.parse stdout with
    | Except.error e => return e
    | Except.ok response =>
      match response.getObjValAs? String "output" with
      | Except.error e => return e
      | Except.ok output => return output
  | _ =>
    let cmd ← LeanAide.pythonPath
    let ss := ("." : FilePath) / "SimilaritySearch" / "similarity_search.py"
    let inp ← IO.Process.output {cmd := cmd, args := #[ss.toString, js.compress]}
    let ⟨err_code,stdout,stderr'⟩ := inp
    match err_code with
    | 0 =>
      match Lean.Json.parse stdout with
      | Except.error e => return e ++ "\nFrom:" ++ stdout
      | Except.ok output =>
        return output.compress
    | _ => return stderr ++ "\n" ++ stderr'
