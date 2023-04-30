def main (_: List String) : IO Unit := do
  let allLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "all.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  let trainLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "train.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  let testLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"])).filter (fun l => l != "" && !trainLines.contains l) |>.toList.eraseDups
  let validLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "valid.jsonl"])).filter (fun l => l != "" && !trainLines.contains l && !testLines.contains l) |>.toList.eraseDups
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "all.jsonl"]) (allLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "train.jsonl"]) (trainLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"]) (testLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "valid.jsonl"]) (validLines.foldl (fun s l => s ++ l ++ "\n") "")

  let allLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "all.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  let trainLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "train.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  let testLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "test.jsonl"])).filter (fun l => l != "" && !trainLines.contains l) |>.toList.eraseDups
  let validLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "valid.jsonl"])).filter (fun l => l != "" && !trainLines.contains l && !testLines.contains l) |>.toList.eraseDups
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "all.jsonl"]) (allLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "train.jsonl"]) (trainLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "test.jsonl"]) (testLines.foldl (fun s l => s ++ l ++ "\n") "")
  IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "valid.jsonl"]) (validLines.foldl (fun s l => s ++ l ++ "\n") "")