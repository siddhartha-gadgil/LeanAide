import LeanAide.PremiseData
open Lean Json Data LeanAide.Meta

def main (_: List String) : IO Unit := do
  let testLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"]))
  let mut count := 0
  let mut premiselessCount := 0
  let mut provedCount := 0
  for l in testLines do
    if count % 100 = 0 then
      IO.println s!"{count} processed, {premiselessCount} premiseless"
    let js? := Lean.Json.parse l |>.toOption
    let premise? : Option CorePremiseData := 
      js?.bind <| fun js => (fromJson? js).toOption
    match premise? with
    | some corePremise =>
      count := count + 1
      let ids := corePremise.ids.map (·.toName)
      let check := ids.all (
        fun n ↦
          (``Eq).isPrefixOf n || (``Iff).isPrefixOf n)
      if check then
        premiselessCount := premiselessCount + 1
        IO.println s!"{corePremise.thm} has no true premises"
        IO.println s!"{corePremise.ids} are the ids"
        -- should try to prove here
    | none => pure ()