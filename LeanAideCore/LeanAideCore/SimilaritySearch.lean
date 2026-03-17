import Lean
import LeanAideCore.Aides
import LeanAideCore.Kernel
open System Lean
namespace LeanAide

def callSimilaritySearch (query : String) (descField : String := "docString") (numSim : Nat := 10) : MetaM <| Except String Json := do
  let js := Json.mkObj [("num", numSim), ("query", query), ("descField", descField)]
  try
    let serverUrl ← try
      getUrlM
    catch e =>
      traceAide `leanaide.translate.info s!"Could not get URL for similarity search API, falling back to local server. Error was: {← e.toMessageData.toString}"
      pure "http://localhost:7654"
    let APIUrl := s!"{serverUrl}/run-sim-search"
    let inp ← IO.Process.output {cmd := "curl", args := #["--fail-with-body", "-X", "POST", APIUrl, "-H", "Content-Type: application/json", "-d", js.compress]}
    let ⟨err_code,stdout,stderr⟩ := inp
    match err_code with
    | 0 =>
      match Json.parse stdout with
      | Except.error e =>
          traceAide `leanaide.translate.info s!"Error parsing JSON from similarity search API, falling back to local script. Error was: {e}({stderr})\nFrom: {stdout}"
          useScript js
      | Except.ok response =>
        match response.getObjValAs? (Array Json) "output" with
        | Except.error e =>
            traceAide `leanaide.translate.info s!"Error extracting Array Json from key `output` in similarity search response. Error was: {e}\nFrom: {stdout}"
            useScript js
        | Except.ok val => return Except.ok val.toJson
    | _ => useScript js
  catch e =>
    traceAide `leanaide.translate.info s!"Exception while calling similarity search API: {← e.toMessageData.toString}"
    useScript js
  where
    useScript (js: Json) : MetaM <| Except String Json := do
      let cmd ← LeanAide.pythonPath
      let ss := ("." : FilePath) / "SimilaritySearch" / "similarity_search.py"
      let inp ← IO.Process.output {cmd := cmd, args := #[ss.toString, js.compress]}
      let ⟨err_code,stdout,stderr⟩ := inp
      match err_code with
      | 0 =>
        match Json.parse stdout with
        | Except.error e => return Except.error <| e ++ "\nFrom:" ++ stdout
        | Except.ok output =>
          return Except.ok <| output
      | _ => return Except.error stderr

-- #leanaide_connect

-- #eval callSimilaritySearch "This is a prime"
