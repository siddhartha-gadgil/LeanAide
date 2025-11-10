import Lean
import LeanAideCore.Aides
open System Lean
namespace LeanAide

def callSimilaritySearch (query : String) (descField : String := "docString") (numSim : Nat := 10) : IO <| Except String Json := do
  let APIUrl := "http://localhost:7654/run-sim-search"
  let js := Json.mkObj [("num", numSim), ("query", query), ("descField", descField)]
  let inp ← IO.Process.output {cmd := "curl", args := #["--fail-with-body", "-X", "POST", APIUrl, "-H", "Content-Type: application/json", "-d", js.compress]}
  let ⟨err_code,stdout,stderr⟩ := inp
  match err_code with
  | 0 =>
    match Json.parse stdout with
    | Except.error e => return Except.error <| "Could not parse JSON from sim-search response:\n" ++ e
    | Except.ok response =>
      match response.getObjValAs? (Array Json) "output" with
      | Except.error e => return Except.error <| "Could not extract an Array Json from key `output` in sim-search response:\n" ++ e
      | Except.ok val => return Except.ok val.toJson
  | _ =>
    let cmd ← LeanAide.pythonPath
    let ss := ("." : FilePath) / "SimilaritySearch" / "similarity_search.py"
    let inp ← IO.Process.output {cmd := cmd, args := #[ss.toString, js.compress]}
    let ⟨err_code,stdout,stderr'⟩ := inp
    match err_code with
    | 0 =>
      match Json.parse stdout with
      | Except.error e => return Except.error <| e ++ "\nFrom:" ++ stdout
      | Except.ok output =>
        return Except.ok <| output
    | _ => return Except.error <| stderr ++ "\n" ++ stderr'
