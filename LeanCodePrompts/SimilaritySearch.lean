import Lean
import LeanAideCore.Aides
import LeanAideCore.Kernel
open System Lean
namespace LeanAide

def callSimilaritySearch (query : String) (descField : String := "docString") (numSim : Nat := 10) : MetaM <| Except String Json := do
  let js := Json.mkObj [("num", numSim), ("query", query), ("descField", descField)]
  try
    let serverUrl ← getUrlM
    let APIUrl := s!"{serverUrl}/run-sim-search"
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
    | _ => return Except.error <| "Error from sim-search API:\n" ++ stderr
  catch e =>
    traceAide `leanaide.translate.info s!"Exception while calling similarity search API: {← e.toMessageData.toString}"
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
    | _ => return Except.error stderr'

-- #leanaide_connect

-- #eval callSimilaritySearch "This is a prime"
