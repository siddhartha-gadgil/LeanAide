import LeanCodePrompts.Translate
import Lean.Meta
open Lean Meta Elab

/-- given string to translate, build prompt and query OpenAI; returns JSON response
-/
def getCodeCustomJson (s: String)(customPrompts : Array (String × String) := #[])(numSim : Nat:= 5)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Json := do
  match ← getCachedJson? s with
  | some js => return js
  | none =>    
    let pending ←  pendingJsonQueries.get
    if pending.contains s then pollCacheJson s 
    else 
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.insert s)
      -- work starts here; before this was caching, polling etc
      let (pairs, IOOut) ←  
        if numSim > 0 then  
          getPromptPairs s numSim scoreBound matchBound 
        else pure (#[], ⟨0, "", ""⟩)
      let pairs := pairs.reverse
      let pairs := pairs ++ customPrompts 
      let prompt := makePrompt s pairs
      mkLog prompt
      -- IO.println s!"seeking Codex completions; time : {← IO.monoMsNow}"
      let fullJson ← openAIQuery prompt queryNum temp
      -- IO.println s!"obtained Codex completions; time : {← IO.monoMsNow}"
      let outJson := 
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.erase s)
      if IOOut.exitCode = 0 then cacheJson s outJson 
        else throwError m!"Web query error: {IOOut.stderr}"
      return outJson

/-- elaborates the string with translations and auto-corrections, including the one-to-many compatibility transformations and (optionally) returns a list of translations and (un)translated strings -/
def polyElabThmTransWithErr (s : String)(limit : Option Nat := none)
  (transf : String → MetaM (Option String) := caseOrBinName?)
  (extraTransf : List (String → MetaM (Option String))
        := [dotName?])
  (opens: List String := []) 
  (levelNames : List Lean.Name := levelNames)
  : TermElabM <| Except String <| 
        (Array (Expr × String)) × (Array (String × String)) := do
  -- IO.println s!"started translations for {s}; time : {← IO.monoMsNow}"
  match ← polyIdentMappedFunStx s transf extraTransf opens limit with
  | Except.ok funTypeStrList => do
    -- IO.println s!"obtained translations for {s}; time : {← IO.monoMsNow}"
    let mut elabPairs : Array (Expr × String) := #[]
    let mut errorPairs : Array (String × String) := #[]
    for funTypeStr in funTypeStrList do
        let expE? ← elabFuncTyp funTypeStr levelNames
        -- IO.println s!"obtained elaboration for {funTypeStr}; time : {← IO.monoMsNow}"
        match expE? with
        | Except.ok expE => elabPairs := elabPairs.push (expE.snd, funTypeStr)
        | Except.error err => 
              errorPairs := errorPairs.push (err, funTypeStr)
    return Except.ok (elabPairs, errorPairs)
  | Except.error e => return Except.error e

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and returns the best choice, with all attemts.  -/
def arrayToExprWithErr? (outputs: Array String) : TermElabM <| Except String (String × (Array String)) := do
  let outputs := outputs.toList.eraseDups.toArray
  let mut elaborated : Array String := Array.empty
  let mut errorLog: String := ""
  -- IO.println s!"started elaborations; time : {← IO.monoMsNow}"
  -- translation, autocorrection and filtering by elaboration
  for out in outputs do
    let ployElab? ← polyElabThmTransWithErr out
    -- IO.println s!"obtained elaboration for {out}; time : {← IO.monoMsNow}"
    match ployElab? with
      | Except.error msg =>
          errorLog := errorLog ++ s!"Completion: {out}, Error: {msg}; "
          pure ()
      | Except.ok (es, errs) =>
        for (_ , s) in es do
            elaborated := elaborated.push s
        for (msg, s) in errs do
            errorLog := errorLog ++ s!"Completion: {out}, Parsed-to: {s}, Failure: {msg}; " 
  if elaborated.isEmpty then 
      return Except.error errorLog
  else    
    -- grouping by trying to prove equality and selecting
    -- IO.println s!"grouping and selecting; time : {← IO.monoMsNow}"
    let groupSorted ← groupFuncStrs elaborated
    let topStr := groupSorted[0]![0]!
    -- IO.println s!"chosen best result; time : {← IO.monoMsNow}"
    return Except.ok (topStr, elaborated)

def translate (s: String)(customPrompts : Array (String × String) := #[])(numSim : Nat:= 5)(queryNum: Nat := 15)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM (Except String (String × (Array String))) := do
  -- IO.println s!"started translating {s}; time : {← IO.monoMsNow}"
  let json ← getCodeCustomJson s customPrompts numSim queryNum temp scoreBound matchBound
  let outputs ← jsonToExprStrArray json
  let out? ← arrayToExprWithErr? outputs
  return out?
