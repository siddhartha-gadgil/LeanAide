import LeanCodePrompts.Premises
open Lean Json Data

def pairs? (s: String) : Option <| List IdentPair := 
  let js? := Lean.Json.parse s |>.toOption
  let ids? : Option IdentData :=
     js?.bind (fun js => fromJson? js |>.toOption)
  ids?.map <| fun id => id.unfold |>.toList 

def allPairs (ss: List String) : List IdentPair := 
  ss.foldl (fun acc s => 
    match pairs? s with
    | some ps => ps ++ acc
    | none => acc
  ) []

def allPairsString (ss: List String) : String := 
  jsonLines <| (allPairs ss).toArray

def main (_: List String) : IO Unit := do
  IO.println "Deduplicating core"
  -- let allLines := 
  --   (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "all.jsonl"])).filter (fun l => l != "") -- |>.toList.eraseDups
  let trainLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "train.jsonl"])) --.filter (fun l => l != "") |>.toList.eraseDups
  let testLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"])) --.filter (fun l => l != "" && !trainLines.contains l) -- |>.toList.eraseDups
  let validLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "valid.jsonl"])) --.filter (fun l => l != "" && !trainLines.contains l && !testLines.contains l) -- |>.toList.eraseDups

  IO.println s!"Read lines: {trainLines.size}, {testLines.size}, {validLines.size}"


  let lineMap : HashMap String <| Array String := HashMap.ofList  <| [("train", trainLines), ("test", testLines), ("valid", validLines)]
  let mut prevLines: HashSet String := {}
  let mut count := 0
  for l in trainLines do
    if !prevLines.contains l then
      count := count + 1
      let js? := Lean.Json.parse l |>.toOption
      let dfn? : Option CorePremiseData := 
        js?.bind <| fun js => (fromJson? js).toOption
      if count % 100 = 0 then
        IO.println s!"obtained {count} definitions"
      if dfn?.isNone then
        IO.println s!"Could not parse: {l}"
    else IO.println "duplicate line"

  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "all.jsonl"]) (allLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "train.jsonl"]) (trainLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"]) (testLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "core", "valid.jsonl"]) (validLines.foldl (fun s l => s ++ l ++ "\n") "")

  -- IO.println "Deduplicating identifiers"
  -- let allLines := 
  --   (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "all.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  -- let trainLines := 
  --   (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "train.jsonl"])).filter (fun l => l != "") |>.toList.eraseDups
  -- let testLines := 
  --   (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "test.jsonl"])).filter (fun l => l != "" && !trainLines.contains l) |>.toList.eraseDups
  -- let validLines := 
  --   (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "identifiers", "valid.jsonl"])).filter (fun l => l != "" && !trainLines.contains l && !testLines.contains l) |>.toList.eraseDups
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "all.jsonl"]) (allLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "train.jsonl"]) (trainLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "test.jsonl"]) (testLines.foldl (fun s l => s ++ l ++ "\n") "")
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "identifiers", "valid.jsonl"]) (validLines.foldl (fun s l => s ++ l ++ "\n") "")

  -- IO.println "Deduplicating ident pairs"
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "ident_pairs", "all.jsonl"]) (allPairsString allLines)
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "ident_pairs", "train.jsonl"]) (allPairsString trainLines)
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "ident_pairs", "test.jsonl"]) (allPairsString testLines)
  -- IO.FS.writeFile (System.mkFilePath ["rawdata", "premises", "ident_pairs", "valid.jsonl"]) (allPairsString validLines)