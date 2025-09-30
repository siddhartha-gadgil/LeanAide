def callSimilaritySearch (descField : String) (query : String) (numSim : Nat) : IO String := do
  let exePath := System.mkFilePath [".", "SimilaritySearch", "SimilaritySearch.py"]
  let inp ← IO.Process.output {cmd := "python3", args := #[exePath.toString, query, (toString numSim), descField]}
  let ⟨err_code,stdout,stderr⟩ := inp
  match err_code with
  | 0 => return stdout
  | _ => return stderr
