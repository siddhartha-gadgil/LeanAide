import DataGenAide.PremiseData
open Lean Json Data LeanAide.Meta



def pairs? (s: String) : Option <| List IdentPair :=
  let js? := Lean.Json.parse s |>.toOption
  let ids? : Option IdentData :=
     js?.flatMap (fun js => fromJson? js |>.toOption)
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

  let handles ← mainFileHandles
  let lineMap : Std.HashMap String <| Array String := Std.HashMap.ofList  <| [("train", trainLines), ("test", testLines), ("valid", validLines)]
  let mut prevLines: Std.HashSet String := {}
  let mut count := 0
  let mut dups := 0
  for group in groups do
    IO.println s!"Writing group {group}"
    for l in lineMap.find! group do
      if !prevLines.contains l then
        count := count + 1
        prevLines := prevLines.insert l
        let js? := Lean.Json.parse l |>.toOption
        let premise? : Option CorePremiseData :=
          js?.flatMap <| fun js => (fromJson? js).toOption
        match premise? with
        | some corePremise =>
            corePremise.write group handles
            let identData :=
                IdentData.ofCorePremiseData corePremise
            identData.write group handles
            identData.writeString group handles
            let identPairs := identData.unfold
            for identPair in identPairs do
                identPair.write group handles
            let termPairs := TermPair.ofCorePremiseData corePremise
            for termPair in termPairs do
                termPair.write group handles
            let lemmaPairs := LemmaPair.ofCorePremiseData corePremise
            for lemmaPair in lemmaPairs do
                lemmaPair.write group handles
            if count % 5000 = 0 then
              IO.println s!"obtained {count} definitions; {dups} duplicates"
        | none =>
          IO.println s!"Could not parse: {l}"
      else dups := dups + 1
