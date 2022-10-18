import LeanCodePrompts.Translate
import Lean
import Lean.Meta
open Lean Meta Elab



/-- make prompt for continuing statements-/
def makeThmsPrompt(pairs: Array (String × String))(context: String := "") : String := 
pairs.foldr (fun  (_, thm) acc => 
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"theorem {thm} :=

{acc}"
          ) s!"
theorem {context}"


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



def getContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 20)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (pairs, IOOut) ←  
      if numSim > 0 then  
        getPromptPairs s numSim numKW scoreBound matchBound 
      else pure (#[], ⟨0, "", ""⟩)
    let pairs := if includeFixed then pairs ++ fixedPrompts else pairs 
    let prompt := makeThmsPrompt pairs context
    mkLog prompt
    let fullJson ← openAIQuery prompt queryNum temp
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    jsonToExprStrArray outJson

def getDocContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (pairs, IOOut) ←  
      if numSim > 0 then  
        getPromptPairs s numSim numKW scoreBound matchBound 
      else pure (#[], ⟨0, "", ""⟩)
    let pairs := if includeFixed then pairs ++ fixedPrompts else pairs 
    let prompt := makeDocsThmsPrompt pairs 
    mkLog prompt
    let fullJson ← openAIQuery prompt queryNum temp #[":="]
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    let completions ← jsonToExprStrArray outJson
    let padded := completions.map (fun c => "/-- " ++ c)
    return padded

def getSectionContinuationExprs (s: String)(context: String)(numSim : Nat:= 10)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩) : TermElabM <| Array String := do
      -- work starts here; before this was caching, polling etc
    let (triples, IOOut) ←  
        getPromptTriples s numSim  
    let prompt := makeSectionPrompt triples context
    mkLog prompt
    let fullJson ← openAIQuery prompt queryNum temp #[":="]
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let pending ←  pendingJsonQueries.get
    pendingJsonQueries.set (pending.erase s)
    if IOOut.exitCode = 0 then cacheJson s outJson 
      else throwError m!"Web query error: {IOOut.stderr}"
    let completions ← jsonToExprStrArray outJson
    let padded := completions.map (fun c => 
    s!"{context}
/-- " ++ c)
    return padded


def showContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 8)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getContinuationExprs s context numSim numKW includeFixed queryNum temp scoreBound matchBound
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (context ++ " " ++ s)
    let exps := exps?.toOption.getD []
    return (s!"theorem {context} {s} := sorry",exps.map (fun (_, s) => s))
  )

def showDocContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 20)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getDocContinuationExprs s numSim numKW includeFixed queryNum temp scoreBound matchBound
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (s)
    let exps := exps?.toOption.getD []
    return (s, exps.map (fun (_, s) => s))
  )

def showSectionContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(queryNum: Nat := 16)(temp : JsonNumber := ⟨8, 1⟩) : TermElabM <| Array (String × (List String)) := do
  let exprs ← 
    getSectionContinuationExprs s context numSim  queryNum temp 
  exprs.mapM (fun s => do
    let exps? ← polyElabThmTrans (s)
    let exps := exps?.toOption.getD []
    return (s, exps.map (fun (_, s) => s))
  )
