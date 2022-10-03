import LeanCodePrompts.Translate
import Lean
import Lean.Meta
open Lean Meta Elab

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

def getDocContinuationExprs (s: String)(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 20)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array String := do
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
    jsonToExprStrArray outJson


def statement := "Every subgroup of a group is normal."

def showContinuationExprs (s: String)(context: String := "")(numSim : Nat:= 10)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 10)(temp : JsonNumber := ⟨8, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM <| Array (String × (List String)) := do
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

-- #eval showContinuationExprs statement "(G: Type u)"

-- #eval showLogs 10

-- def statement2 := "Every two prime numbers are coprime."

-- #eval showContinuationExprs statement "(n: Nat)"

-- #eval showLogs 10

#eval showDocContinuationExprs statement 

#eval showLogs 10
