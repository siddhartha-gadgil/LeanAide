import Lean
import Lean.Meta
import Lean.Parser
import LeanCodePrompts.CheckParse
import LeanCodePrompts.ParseJson
import LeanCodePrompts.Autocorrect
import LeanCodePrompts.KeywordSummary.KeywordExtraction
import LeanCodePrompts.EgsTranslate
open Lean Meta Std

open Lean Elab Parser Command

/-- extrct prompt pairs from JSON response to local server -/
def sentenceSimPairs(s: String) : MetaM  <| Except String (Array (String × String)) := do
  let json ← readJson (s) 
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
      let thm ←  match (json.getObjVal? "theorem") with
        | Except.error e => throwError s!"Error {e} while getting doc_string"
        | Except.ok js => 
          match js.getStr? with
          | Except.error e => throwError s!"Error {e} while processing {js} as string"  
          | Except.ok s => pure s
      return (docstring, thm)
    return Except.ok pairs
  | Except.error e => return Except.error e

-- #eval sentenceSimPairs egSen

/-- make prompt from prompt pairs -/
def makePrompt(prompt : String)(pairs: Array (String × String)) : String := 
      pairs.foldr (fun  (ds, thm) acc => 
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"/-- {ds} -/
theorem {thm} :=

{acc}"
          ) s!"/-- {prompt} -/
theorem "

/-- make prompt for reverse translation from prompt pairs -/
def makeFlipPrompt(statement : String)(pairs: Array (String × String)) : String := 
      pairs.foldr (fun  (ds, thm) acc => 
s!"theorem {thm} := 
/- {ds} -/

{acc}"
          ) s!"theorem {statement} := 
/- "

def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

/--query open-ai with given prompt and parameters -/
def openAIQuery(prompt: String)(n: Nat := 1)
  (temp : JsonNumber := ⟨2, 1⟩)(stopTokens: Array String :=  #[":=", "-/"]) : MetaM Json := do
  let key? ← openAIKey
  let key := 
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj [("model", "code-davinci-002"), ("prompt", prompt), ("temperature", Json.num temp), ("n", n), ("max_tokens", 150), ("stop", Json.arr <| stopTokens |>.map Json.str)]
  let data := dataJs.pretty
  let out ←  IO.Process.output {
        cmd:= "curl", 
        args:= #["https://api.openai.com/v1/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  readJson out.stdout

/-!
Caching, polling etc to avoid repeatedly calling servers
-/

initialize webCacheJson : IO.Ref (HashMap String Json) ← IO.mkRef (HashMap.empty)

initialize pendingJsonQueries : IO.Ref (HashSet String) 
    ← IO.mkRef (HashSet.empty)

initialize logCache : IO.Ref (Array String) ← IO.mkRef (#[])

def mkLog{α : Type _}[ToString α](msg: α) : IO Unit := do
  let cache ← logCache.get
  logCache.set (cache.push (toString msg))

def logs (num: Nat) : IO (List String) := do
  let cache ← logCache.get
  return cache.reverse.toList.take num

def showLogs (num: Nat) : IO Unit := do
  let cache ← logCache.get
  let ls := cache.reverse.toList.take num
  for lines in ls do
  for l in lines.splitOn "\n" do
    IO.println l

def getCachedJson? (s: String) : IO (Option Json) := do
  let cache ← webCacheJson.get
  return cache.find? s

def cacheJson (s: String)(js: Json)  : IO Unit := do
  let cache ← webCacheJson.get
  webCacheJson.set (cache.insert s js)
  return ()

partial def pollCacheJson (s : String) : IO Json := do
  let cache ← webCacheJson.get
  match cache.find? s with
  | some jsBlob => return jsBlob
  | none => do
    IO.sleep 200
    pollCacheJson s

/-- check if there is a valid elaboration after translation, autocorrection -/
def hasElab (s: String)(limit : Option Nat := none) : TermElabM Bool := do
    -- (elabThmTrans s).map (fun e => e.toBool)
  let elab? ← polyElabThmTrans s limit
  match elab? with
  | Except.error _ => return Bool.false
  | Except.ok els => return !els.isEmpty

/-- log to file -/
def elabLog (s: String) : IO Unit := do
  let logFile := System.mkFilePath ["results/elab_logs.txt"]
  let h ← IO.FS.Handle.mk logFile IO.FS.Mode.append Bool.false
  h.putStrLn s
  h.putStrLn ""

def fixedPrompts:= #[("If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$.", "(n : ℕ) (f : ℕ → ℂ) :\n abs (∑ i in finset.range n, f i) ≤ ∑ i in finset.range n, abs (f i) :="), ("If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$.", "(n : ℕ) (x y : euclidean_space ℝ (fin n)) :\n ∥x + y∥^2 + ∥x - y∥^2 = 2*∥x∥^2 + 2*∥y∥^2 :="), ("If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct.", "(G : Type*) [group G] (x : G) (hx : x ≠ 1) (hx_inf : ∀ n : ℕ, x ^ n ≠ 1) : ∀ m n : ℤ, m ≠ n → x ^ m ≠ x ^ n :="), ("Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\\in A$ there is an open set $U$ containing $x$ such that $U\\subset A$. Show that $A$ is open in $X$.", "(X : Type*) [topological_space X]\n (A : set X) (hA : ∀ x ∈ A, ∃ U : set X, is_open U ∧ x ∈ U ∧ U ⊆ A):\n is_open A :=")]

/-- choosing pairs to build a prompt -/
def getPromptPairs(s: String)(numSim : Nat)(numKW: Nat)
    (scoreBound: Float)(matchBound: Nat)
   : TermElabM (Array (String × String) × IO.Process.Output) := do
      let simJsonOut ←  
        IO.Process.output {cmd:= "curl", args:= 
          #["-X", "POST", "-H", "Content-type: application/json", "-d", s ++ s!" top_K {numSim}", "localhost:5000/similar_json"]}
      let pairs? ← sentenceSimPairs simJsonOut.stdout
      let allPairs := pairs?.toOption.getD #[]        
      let kwPairs :=
        if numKW >0 
        then ←  keywordBasedPrompts docPair s numKW scoreBound matchBound
        else #[]
      let allPairs := (allPairs ++ kwPairs).toList.eraseDups.toArray
      let pairs -- := allPairs -- 
        ←  allPairs.filterM (fun (_, s) => do
            isElabPrompt s )
      let kwPairs ←  keywordBasedPrompts docPair s
      return (
          (pairs ++ kwPairs).toList.eraseDups.toArray, simJsonOut)

/-- given string to translate, build prompt and query OpenAI; returns JSON response
-/
def getCodeJson (s: String)(numSim : Nat:= 5)(numKW: Nat := 4)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := ⟨2, 1⟩)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM Json := do
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
          getPromptPairs s numSim numKW scoreBound matchBound 
        else pure (#[], ⟨0, "", ""⟩)
      let pairs := if includeFixed then pairs ++ fixedPrompts else pairs 
      let prompt := makePrompt s pairs
      mkLog prompt
      let fullJson ← openAIQuery prompt queryNum temp
      let outJson := 
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
      let pending ←  pendingJsonQueries.get
      pendingJsonQueries.set (pending.erase s)
      if IOOut.exitCode = 0 then cacheJson s outJson 
        else throwError m!"Web query error: {IOOut.stderr}"
      return outJson

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and returns the best choice, throwing an error if nothing elaborates.  -/
def arrayToExpr (output: Array String) : TermElabM Expr := do
  let output := output.toList.eraseDups.toArray
  mkLog output
  let mut elaborated : Array String := Array.empty
  -- translation, autocorrection and filtering by elaboration
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (_ , s) in es do
            elaborated := elaborated.push s 
  if elaborated.isEmpty then do
    -- information with failed logs
    logWarning m!"No valid output from Codex; outputs below"
    for out in output do
      let polyOut ←  polyStrThmTrans out
      for str in polyOut do
        logWarning m!"{str}"
    mkSyntheticSorry (mkSort levelZero)
  else    
    -- grouping by trying to prove equality and selecting
    let groupSorted ← groupFuncStrs elaborated
    let topStr := groupSorted[0]![0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok thm => return thm
    | Except.error s => throwError s

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and optionally returns the best choice as well as all elaborated terms (used for batch processing, interactive code uses `arrayToExpr` instead)  -/
def arrayToExpr? (output: Array String) : TermElabM (Option (Expr× (Array String))) := do
  let mut elaborated : Array String := Array.empty
  let mut fullElaborated : Array String := Array.empty
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (expr, s) in es do
          elaborated := elaborated.push s 
          if !expr.hasExprMVar then
            fullElaborated := fullElaborated.push s
  if elaborated.isEmpty then 
    elabLog "No valid output from Codex; outputs below"
    for out in output do
      let polyOut ←  polyStrThmTrans out
      for str in polyOut do
        elabLog s!"{str}"
    return none
  else    
    let priority := 
        if fullElaborated.isEmpty then elaborated else fullElaborated
    let groupSorted ← groupFuncStrs priority
    let topStr := groupSorted[0]![0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok thm => return some (thm, elaborated)
    | Except.error s =>
        elabLog s!"Second round error : {s}"
        return none

/-- reverse translation from `Lean` to natural language -/
def leanToPrompt (thm: String)(numSim : Nat:= 5)(numKW: Nat := 4)(temp : JsonNumber := 0)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM String := do
    let (pairs, _) ← getPromptPairs thm numSim numKW scoreBound matchBound
    let prompt := makeFlipPrompt thm pairs
    -- elabLog prompt
    let fullJson ← openAIQuery prompt 1 temp
    let outJson := 
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let out? := (outJson.getArrVal? 0).bind fun js => js.getObjVal? "text"
    let outJson := 
        match (out?) with
        | Except.error s => Json.str s!"query for translation failed: {s}" 
        | Except.ok js => js
    return outJson.getStr!

-- #eval leanToPrompt "∀ {p : ℕ} [inst : Fact (Nat.Prime p)], p = 2 ∨ p % 2 = 1"

-- #eval leanToPrompt "∀ {α : Type u} {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x"

-- #eval leanToPrompt "{  n :  ℕ } ->  Even   (    (   n +  1  ) * n  )"

/-- array of outputs extracted from json -/
def jsonToExprStrArray (json: Json) : TermElabM (Array String) := do
  let outArr : Array String ← 
    match json.getArr? with
    | Except.ok arr => 
        let parsedArr : Array String ← 
          arr.filterMapM <| fun js =>
            match js.getObjVal? "text" with
              | Except.ok jsstr =>
                match jsstr.getStr? with
                | Except.ok str => pure (some str)
                | Except.error e => 
                  throwError m!"json string expected but got {js}, error: {e}"
              | Except.error _ =>
                throwError m!"no text field"
        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"
  return outArr

/-- given json returned by open-ai obtain the best translation -/
def jsonToExpr' (json: Json) : TermElabM Expr := do
  let output ← jsonToExprStrArray json
  arrayToExpr output

/-- translation from a comment-like syntax to a theorem statement -/
elab "//-" cb:commentBody  : term => do
  let s := cb.raw.getAtomVal!
  let s := (s.dropRight 2).trim  
  -- querying codex
  let js ← getCodeJson  s
  -- filtering, autocorrection and selection
  let e ← jsonToExpr' js
  logInfo m!"{e}"
  return e
