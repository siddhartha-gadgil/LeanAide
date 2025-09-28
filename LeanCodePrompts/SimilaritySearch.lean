def callSimilaritySearch : IO String := do
  let exePath := System.mkFilePath [".", "SimilaritySearch", "SimilaritySearch.py"]
  let inp ← IO.Process.output {cmd := "python3", args := #[exePath.toString, "infinite primes", "10"]}
  let ⟨err_code,stdout,stderr⟩ := inp
  match err_code with
  | 0 => return s!"SUCCESS: {stdout}"
  | _ => return s!"ERROR THROWN: {stderr}"

-- #eval callSimilaritySearch
