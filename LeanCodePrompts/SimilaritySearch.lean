import Lean

def callSimilaritySearch (descField : String := "docString") (query : String := "mathematics") (numSim : Nat := 10) : IO String := do
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
  | _ => return stderr

--#eval callSimilaritySearch "docString" "infinite odd primes" 5
