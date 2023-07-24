import LeanCodePrompts.Translate
import Lean
import Lean.Meta
open Lean Meta Elab

/-- extract prompt pairs from JSON response to local server -/
def sentenceSimTriples(s: String) : MetaM  <| Except String (Array (String × String × String)) := do
  let json := Lean.Json.parse s |>.toOption.get! 
  -- logInfo "obtained json"
  match json.getArr? with
  | Except.ok jsonArr => do
    let pairs ←  jsonArr.mapM fun json => do
      let docstring : String ←  
        match (json.getObjVal? "doc_string") with
        | Except.error e => throwError s!"Error {e} while getting doc_string"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      let args ←  match (json.getObjVal? "args") with
        | Except.error e => throwError s!"Error {e} while getting theorem"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      let type ←  match (json.getObjVal? "type") with
        | Except.error e => throwError s!"Error {e} while getting theorem"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      return (docstring, args, type)
    return Except.ok pairs
  | Except.error e => return Except.error e

/-- choosing pairs to build a prompt -/
def getPromptTriples(s: String)(numSim : Nat)
   : TermElabM (Array (String × String × String) × IO.Process.Output) := do
      let jsData := Json.mkObj [
        ("filename", "data/safe_prompts.json"),
        ("field", "doc_string"),
        ("doc_string", s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←  
        IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      let triples? ← sentenceSimTriples simJsonOut.stdout
      let allTriples := triples?.toOption.getD #[]        
        -- ←  allPairs.filterM (fun (_, s) => do
        --     isElabPrompt s )
      return (
          allTriples.toList.eraseDups.toArray, simJsonOut)


def sysContinuationPrompt := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the syntax in the examples given. You will continue the sequence of examples"

def continuationPrompt (egs: String) : Json := 
  Json.arr <| #[GPT.message "system" sysContinuationPrompt, GPT.message "user" egs]
    

/-- make prompt for continuing statements-/
def makeThmsPrompt(pairs: Array (String × String))(context: String := "") : String := 
pairs.foldr (fun  (_, thm) acc => 
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"theorem {thm} :=

{acc}"
          ) s!""


/-- make prompt for continuing statements with docs-/
def makeDocsThmsPrompt(pairs: Array (String × String)) : String := 
pairs.foldr (fun  (ds, thm) acc => 
s!"/-- {ds} -/
theorem {thm} := sorry

{acc}") s!"
/--"

/-- make prompt for continuing statements with docs-/
def makeSectionPrompt(triples: Array (String × String × String))
    (context: String) : String := 
triples.foldr (fun  (ds, args, type) acc => 
s!"section
variable {args} 
/-- {ds} -/
theorem : {type} := sorry
end

{acc}") s!"section
variable {context}
/-- "



def getContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 20)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (pairs, IOOut) ←  
      if numSim > 0 then  
        getPromptPairs s numSim numKW scoreBound matchBound 
      else pure (#[], ⟨0, "", ""⟩)
    let pairs := if includeFixed then pairs ++ fixedPrompts else pairs 
    let prompt := continuationPrompt (makeThmsPrompt pairs)
    trace[Translate.info] m!"prompt: \n{prompt}"
    mkLog prompt
    let fullJson ← gptQuery prompt queryNum temp
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    GPT.jsonToExprStrArray outJson

def getDocContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (pairs, IOOut) ←  
      if numSim > 0 then  
        getPromptPairs s numSim numKW scoreBound matchBound 
      else pure (#[], ⟨0, "", ""⟩)
    let pairs := if includeFixed then pairs ++ fixedPrompts else pairs 
    let promptPairs := pairs.map (fun (doc, thm) => ("State a theorem with docstring", s!"/-- {doc} -/\ntheorem {thm}"))
    let prompt := GPT.makePrompt "State a theorem" promptPairs
    trace[Translate.info] m!"prompt: \n{prompt}"
    mkLog prompt
    let fullJson ← gptQuery prompt queryNum temp #[":="]
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    let completions ← GPT.jsonToExprStrArray outJson
    let padded := completions.map (fun c => "/-- " ++ c)
    return padded

def getSectionContinuationExprs (s: String)(context: String)(numSim : Nat:= 10)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (triples, IOOut) ←  
        getPromptTriples s numSim  
    let promptPairs := triples.map (fun (doc, args, thm) => ("State a theorem with docstring in context", s!"variable {args}\n/-- {doc} -/\ntheorem {thm}"))
    let prompt := GPT.makePrompt "State a theorem" promptPairs
    trace[Translate.info] m!"prompt: \n{prompt}"
    mkLog prompt
    let fullJson ← gptQuery prompt queryNum temp #[":="]
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    let completions ← GPT.jsonToExprStrArray outJson
    let padded := completions.map (fun c => 
    s!"{context}
/-- " ++ c)
    return padded


def showContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getContinuationExprs s numSim numKW includeFixed queryNum temp scoreBound matchBound
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (context ++ " " ++ s)
    let exps := exps?.toOption.getD []
    return (s!"{s} := sorry",exps.map (fun (_, s) => s.2))
  )

def showDocContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 1)(includeFixed: Bool := Bool.false)(queryNum: Nat := 20)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getDocContinuationExprs s numSim numKW includeFixed queryNum temp scoreBound matchBound
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (s)
    let exps := exps?.toOption.getD []
    return (s, exps.map (fun (_, s) => s.2))
  )

def showSectionContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(queryNum: Nat := 16)(temp : JsonNumber := ⟨8, 1⟩) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getSectionContinuationExprs s context numSim  queryNum temp 
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (s)
    let exps := exps?.toOption.getD []
    return (s, exps.map (fun (_, s) => s.2))
  )
