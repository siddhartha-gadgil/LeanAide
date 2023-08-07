import LeanAide.PremiseData
import LeanAide.ProofSearch
open Lean Json Data LeanAide.Meta

def environment : IO Environment := do
  importModules [{module := `Mathlib},
    {module:= `LeanAide.TheoremElab},
    {module:= `LeanAide.PremiseData},
    {module:= `LeanAide.ProofSearch},
    {module := `Mathlib}] {}

def coreContext : Core.Context := 
  {fileName := "", fileMap := ⟨"", #[], #[]⟩, maxHeartbeats := 100000000000, maxRecDepth := 3000, openDecls := [Lean.OpenDecl.simple `LeanAide.Meta []]
    }   

def filterPremiseless (init : Array String)(full: Bool) : Array String :=
  init.filterMap <| fun l =>
    let js? := Lean.Json.parse l |>.toOption
    let premise? : Option CorePremiseData := 
      js?.bind <| fun js => (fromJson? js).toOption
    match premise? with
    | some corePremise =>
      let ids := corePremise.ids.map (·.toName)
      let check := ids.all (
        fun n ↦
          (``Eq).isPrefixOf n || (``Iff).isPrefixOf n)
      if check && corePremise.lemmas.isEmpty &&
        corePremise.terms.isEmpty
      then 
        if full then some l
        else
        some corePremise.thm
      else none 
    | none => none


def serial (testLines : Array String)(preChecked: Bool := false) : IO Unit := do
  let env ← environment
  let mut count := 0
  let mut premiselessCount := 0
  let mut provedCount := 0
  let mut elaboratedCount := 0
  for l in testLines do
    if count % 100 = 0 then
      IO.println s!"{count} processed, {premiselessCount} premiseless, {provedCount} proved, {elaboratedCount} elaborated"
    let js? := Lean.Json.parse l |>.toOption
    let premise? : Option CorePremiseData := 
      js?.bind <| fun js => (fromJson? js).toOption
    match premise? with
    | some corePremise =>
      count := count + 1
      let ids := corePremise.ids.map (·.toName)
      let check := preChecked || (ids.all (
        fun n ↦
          (``Eq).isPrefixOf n || (``Iff).isPrefixOf n))
      if check && corePremise.lemmas.isEmpty &&
        corePremise.terms.isEmpty then
        premiselessCount := premiselessCount + 1
        IO.println s!"{corePremise.thm} has no lemmas, terms, true premises"
        IO.println s!"{corePremise.ids} are the ids"
        IO.println "launching proof search"
        let core := proofSearchCore corePremise.thm #[]
        let (elaborated, proved) ← 
          core.run' coreContext {env := env} |>.runToIO'
        IO.println "finished proof search"
        if elaborated then
          elaboratedCount := elaboratedCount + 1
          IO.println s!"Result elaborated"
        else
          IO.println s!"Result not elaborated"
        if proved then
          provedCount := provedCount + 1
          IO.println s!"Result proved"
        else
          IO.println s!"Result not proved"
        IO.println s!"{count} processed, {premiselessCount} premiseless,
        {provedCount} proved, {elaboratedCount} elaborated"
        IO.println "-------------------"
          
    | none => pure ()
  IO.println s!"{count} processed, {premiselessCount} premiseless, {provedCount} proved, {elaboratedCount} elaborated"


def main (_: List String) : IO Unit := do
  initSearchPath (← Lean.findSysroot) initFiles
  -- let env ← environment
  let testLines := 
    (← IO.FS.lines (System.mkFilePath ["rawdata", "premises", "core", "test.jsonl"]))
  IO.println "filtering"
  let premiseless := filterPremiseless testLines true
  IO.println s!"filtered: {premiseless.size} premiseless of {testLines.size} total"

  serial premiseless true

  -- let concurrency := (← threadNum) * 3 / 4
  -- let batches := premiseless.batches' concurrency
  -- let mut count := 0
  -- let mut total := 0
  -- let mut elaboratedNum := 0
  -- let mut provedNum := 0
  -- for batch in batches do
  --   IO.println s!"Processing batch {count} of {batches.size}"
  --   let core := batchProofSearchCore batch
  --   let triples ← 
  --     core.run' coreContext {env := env} |>.runToIO'
  --   let elaborated := triples.filter <| fun (_, el, _) => el
  --   let proved := elaborated.filter <| fun (_, _, pr) => pr
  --   IO.println s!"Elaborated: {elaborated.size}, proved: {proved.size} of {batch.size}"
  --   elaboratedNum := elaboratedNum + elaborated.size
  --   provedNum := provedNum + proved.size
  --   total := total + batch.size
  --   count := count + 1
  --   IO.println s!"Total elaborated: {elaboratedNum}, proved: {provedNum} of {total}"
  --   IO.println "-------------------"
  -- let batches' := batches.zip (Array.range batches.size)
  -- let tasks ← batches'.mapM fun (batch, k) => do
  --    let core := batchProofSearchCore batch
  --    let t ← core.run' coreContext {env := env} |>.spawnToIO
  --    pure (t, k)
  -- IO.println "Spawned tasks"
  -- let mut count := 0
  -- for (task, k) in tasks do
  --   count := count + 1
  --   IO.println s!"Waiting for task {k}: {count} of {tasks.size}"
  --   let triples ← task.get
  --   let elaborated := triples.filter <| fun (_, el, _) => el
  --   let proved := elaborated.filter <| fun (_, _, pr) => pr
  --   IO.println s!"Elaborated: {elaborated.size}, proved: {proved.size}"
