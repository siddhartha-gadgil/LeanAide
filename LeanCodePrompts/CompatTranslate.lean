import Lean
import Lean.Meta
import Lean.Parser
import LeanAide.TheoremElab
import LeanAide.IP

import LeanCodePrompts.Autocorrect
import LeanCodePrompts.EgsTranslate

open Lean Meta Elab Parser Command

def fileName := "extra_resources/safe_prompts.json"

/-- extract prompt pairs from JSON response to local server -/
def sentenceSimPairs
  (s: String)
  (theoremField : String := "theorem")
   : MetaM  <| Except String (Array (String × String)) := do
  let json := Lean.Json.parse  s |>.toOption.get!
  return do
    (← json.getArr?).mapM <| fun j => do
      let lean4mode := fileName ∈ ["resources/mathlib4-prompts.json",
        "resources/mathlib4-thms.json"]
      let docField :=
        if lean4mode then "docString" else "doc_string"
      let docstring ← j.getObjValAs? String docField
      let typeField :=
        if lean4mode then "type"
        else theoremField
      let thm ← j.getObjValAs? String typeField
      pure (docstring, thm)

-- #eval sentenceSimPairs egSen

namespace GPT

def message (role content : String) : Json :=
  Json.mkObj [("role", role), ("content", content)]

def prompt (sys: String) (egs : List <| String × String)(query : String) : Json :=
  let head := message "system" sys
  let egArr :=
    egs.bind (fun (ds, thm) => [message "user" ds, message "assistant" thm])
  Json.arr <| head :: egArr ++ [message "user" query] |>.toArray

def sysPrompt := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."

def makePrompt(query : String)(pairs: Array (String × String)) : Json:= prompt sysPrompt pairs.toList query

def makeFlipPrompt(query : String)(pairs: Array (String × String)) : Json:= prompt sysPrompt (pairs.toList.map (fun (x, y) => (y, x))) query

def jsonToExprStrArray (json: Json) : TermElabM (Array String) := do
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getObjVal? "message" with
            | Except.ok jsobj =>
                match jsobj.getObjVal? "content" with
                | Except.ok jsstr =>
                  match jsstr.getStr? with
                  | Except.ok str => pure (some str)
                  | Except.error e =>
                    throwError m!"json string expected but got {js}, error: {e}"
                | Except.error _ =>
                  throwError m!"no content field in {jsobj}"
            | Except.error _ =>
                throwError m!"no message field in {js}"

        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"

end GPT

/-- make prompt from prompt pairs -/
@[deprecated makePrompt]
def makePrompt'(prompt : String)(pairs: Array (String × String)) : String :=
      pairs.foldr (fun  (ds, thm) acc =>
        -- acc ++ "/-- " ++ ds ++" -/\ntheorem" ++ thm ++ "\n" ++ "\n"
s!"/-- {ds} -/
theorem {thm} :=

{acc}"
          ) s!"/-- {prompt} -/
theorem "


/-- make prompt for reverse translation from prompt pairs -/
@[deprecated makeFlipPrompt]
def makeFlipPrompt'(statement : String)(pairs: Array (String × String)) : String :=
      pairs.foldr (fun  (ds, thm) acc =>
s!"theorem {thm} :=
/- {ds} -/

{acc}"
          ) s!"theorem {statement} :=
/- "

/-- make prompt for reverse translation from prompt pairs -/
def makeFlipStatementsPrompt(statement : String)(pairs: Array (String × String)) : String :=
      pairs.foldr (fun  (ds, thm) acc =>
s!"{thm} :=
/- {ds} -/

{acc}"
          ) s!"{statement} :=
/- "

-- def openAIKey : IO (Option String) := IO.getEnv "OPENAI_API_KEY"

/--query OpenAI Codex with given prompt and parameters -/
def codexQuery(prompt: String)(n: Nat := 1)
  (temp : JsonNumber := 0.2)(stopTokens: Array String :=  #[":=", "-/"]) : MetaM Json := do
  let key? ← openAIKey
  let key :=
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj [("model", "code-davinci-002"), ("prompt", prompt), ("temperature", Json.num temp), ("n", n), ("max_tokens", 150), ("stop", Json.arr <| stopTokens |>.map Json.str)]
  let data := dataJs.pretty
  trace[Translate.info] "OpenAI query: {data}"
  let out ←  IO.Process.run {
        cmd:= "curl",
        args:= #["https://api.openai.com/v1/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  return Lean.Json.parse out |>.toOption.get!

def gptQuery(messages: Json)(n: Nat := 1)
  (temp : JsonNumber := 0.2)(stopTokens: Array String :=  #[":=", "-/"]) : MetaM Json := do
  let key? ← openAIKey
  let key :=
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj [("model", "gpt-3.5-turbo"), ("messages", messages)
  , ("temperature", Json.num temp), ("n", n), ("max_tokens", 150), ("stop", Json.arr <| stopTokens |>.map Json.str)
  ]
  let data := dataJs.pretty
  trace[Translate.info] "OpenAI query: {data}"
  let out ←  IO.Process.output {
        cmd:= "curl",
        args:= #["https://api.openai.com/v1/chat/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  trace[Translate.info] "OpenAI response: {out.stdout} (stderr: {out.stderr})"
  return Lean.Json.parse out.stdout |>.toOption.get!

def openAIQuery(prompt: String)(n: Nat := 1)
  (temp : JsonNumber := 0.2)(stopTokens: Array String :=  #[":=", "-/"]) : MetaM Json :=
  codexQuery prompt n temp stopTokens

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
  let h ←  IO.FS.Handle.mk logFile IO.FS.Mode.append
  h.putStrLn s
  h.putStrLn ""

def fixedPrompts:= #[("If $z_1, \\dots, z_n$ are complex, then $|z_1 + z_2 + \\dots + z_n|\\leq |z_1| + |z_2| + \\dots + |z_n|$.", "(n : ℕ) (f : ℕ → ℂ) :\n abs (∑ i in finset.range n, f i) ≤ ∑ i in finset.range n, abs (f i) :="), ("If x and y are in $\\mathbb{R}^n$, then $|x+y|^2 + |x-y|^2 = 2|x|^2 + 2|y|^2$.", "(n : ℕ) (x y : euclidean_space ℝ (fin n)) :\n ∥x + y∥^2 + ∥x - y∥^2 = 2*∥x∥^2 + 2*∥y∥^2 :="), ("If $x$ is an element of infinite order in $G$, prove that the elements $x^n$, $n\\in\\mathbb{Z}$ are all distinct.", "(G : Type*) [group G] (x : G) (hx : x ≠ 1) (hx_inf : ∀ n : ℕ, x ^ n ≠ 1) : ∀ m n : ℤ, m ≠ n → x ^ m ≠ x ^ n :="), ("Let $X$ be a topological space; let $A$ be a subset of $X$. Suppose that for each $x\\in A$ there is an open set $U$ containing $x$ such that $U\\subset A$. Show that $A$ is open in $X$.", "(X : Type*) [topological_space X]\n (A : set X) (hA : ∀ x ∈ A, ∃ U : set X, is_open U ∧ x ∈ U ∧ U ⊆ A):\n is_open A :=")]

/-- choosing pairs to build a prompt -/
def getPromptPairs(s: String)(numSim : Nat)(numKW: Nat)
    (scoreBound: Float)(matchBound: Nat)
   : TermElabM (Array (String × String) × IO.Process.Output) := do
      let jsData := Json.mkObj [
        ("filename", fileName),
        ("field", "doc_string"),
        ("doc_string", s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←
        IO.Process.output {cmd:= "curl", args:=
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      let pairs? ← sentenceSimPairs simJsonOut.stdout "theorem"
      -- IO.println s!"obtained sentence similarity; time : {← IO.monoMsNow}"
      let allPairs : Array (String × String) ←
        match pairs? with
        | Except.error e =>
            throwError e
        | Except.ok pairs => pure pairs
      -- logInfo m!"all pairs: {allPairs}"
      let allPairs := allPairs.toList.eraseDups.toArray
      let pairs -- := allPairs --
        ←  allPairs.filterM (fun (_, s) => do
            isElabPrompt s )
      return (pairs.toList.eraseDups.toArray, simJsonOut)

/-- choosing pairs to build a prompt -/
def getPromptPairsGeneral(s: String)(numSim : Nat)(field: String := "doc_string")
    (theoremField : String := "theorem")
   : TermElabM (Array (String × String) × IO.Process.Output) := do
      let jsData := Json.mkObj [
        ("filename", fileName),
        ("field", field),
        (field, s),
        ("n", numSim),
        ("model_name", "all-mpnet-base-v2")
      ]
      let simJsonOut ←
        IO.Process.output {cmd:= "curl", args:=
          #["-X", "POST", "-H", "Content-type: application/json", "-d", jsData.pretty, s!"{← leanAideIP}/nearest_prompts"]}
      let pairs? ← sentenceSimPairs simJsonOut.stdout theoremField
      -- IO.println s!"obtained sentence similarity; time : {← IO.monoMsNow}"
      let allPairs : Array (String × String) ←
        match pairs? with
        | Except.error e =>
            throwError e

        | Except.ok pairs => pure pairs
      -- logInfo m!"all pairs: {allPairs}"
      return (
          allPairs.toList.eraseDups.toArray, simJsonOut)


/-- given string to translate, build prompt and query OpenAI; returns JSON response
-/
def getCodeJson (s: String)(numSim : Nat:= 8)(numKW: Nat := 0)(includeFixed: Bool := Bool.false)(queryNum: Nat := 5)(temp : JsonNumber := 0.2)(scoreBound: Float := 0.2)(matchBound: Nat := 15) : TermElabM Json := do
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
      let pairs  := pairs.filter (fun (s, _) => s.length < 100)
      let prompt := makePrompt s pairs
      trace[Translate.info] m!"prompt: \n{prompt.pretty}"
      -- mkLog prompt
      let fullJson ←
        gptQuery prompt queryNum temp
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
  trace[Translate.info] m!"output:\n{output}"
  -- mkLog output
  let mut elaborated : Array String := Array.empty
  -- translation, autocorrection and filtering by elaboration
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (_ , _, s) in es do
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
    let topStr := (groupSorted[0]!)[0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok (_, thm) => return thm
    | Except.error s => throwError s

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and returns the best choice, throwing an error if nothing elaborates.  -/
def arrayToStx (output: Array String) : TermElabM Syntax := do
  let output := output.toList.eraseDups.toArray
  trace[Translate.info] m!"output:\n{output}"
  -- mkLog output
  let mut elaborated : Array String := Array.empty
  -- translation, autocorrection and filtering by elaboration
  for out in output do
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (_ , _, s) in es do
            elaborated := elaborated.push s
  if elaborated.isEmpty then do
    -- information with failed logs
    logWarning m!"No valid output from Codex; outputs below"
    for out in output do
      let polyOut ←  polyStrThmTrans out
      for str in polyOut do
        logWarning m!"{str}"
    pure Syntax.missing
  else
    -- grouping by trying to prove equality and selecting
    let groupSorted ← groupFuncStrs elaborated
    let topStr := (groupSorted[0]!)[0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok (stx, _) => return stx
    | Except.error s => throwError s

/-- Given an array of outputs, tries to elaborate them with translation and autocorrection and optionally returns the best choice as well as all elaborated terms (used for batch processing, interactive code uses `arrayToExpr` instead)  -/
def arrayToExpr? (output: Array String) : TermElabM (Option (Expr× (Array String))) := do
  -- IO.println s!"arrayToExpr? called with {output.size} outputs"
  let mut elaborated : Array String := Array.empty
  let mut fullElaborated : Array String := Array.empty
  for out in output do
    -- IO.println s!"elaboration called: {out}"
    let ployElab? ← polyElabThmTrans out
    match ployElab? with
      | Except.error _ => pure ()
      | Except.ok es =>
        for (expr, _, s) in es do
          elaborated := elaborated.push s
          if !expr.hasExprMVar then
            fullElaborated := fullElaborated.push s
  if elaborated.isEmpty then
    elabLog "No valid output from LLM; outputs below"
    for out in output do
      let polyOut ←  polyStrThmTrans out
      for str in polyOut do
        elabLog s!"{str}"
    return none
  else
    let priority :=
        if fullElaborated.isEmpty then elaborated else fullElaborated
    let groupSorted ← groupFuncStrs priority
    let topStr := (groupSorted[0]!)[0]!
    let thmExc ← elabFuncTyp topStr
    match thmExc with
    | Except.ok (_, thm) => return some (thm, elaborated)
    | Except.error s =>
        elabLog s!"Second round error : {s}"
        return none

def greedyArrayToExpr? (output: Array String) : TermElabM (Option Expr) := do
    output.findSomeM? <| fun out => do
      let t? ← elabThmTrans? out
      return t?.map fun (expr, _, _) => expr

/-- reverse translation from `Lean` to natural language -/
def leanToPrompt (thm: String)(numSim : Nat:= 5)(numKW: Nat := 1)(temp : JsonNumber := 0)(scoreBound: Float := 0.2)(matchBound: Nat := 15)(textField : String := "text") : TermElabM String := do
    let (pairs, _) ← getPromptPairs thm numSim numKW scoreBound matchBound
    let prompt := makeFlipPrompt thm pairs
    -- elabLog prompt
    let fullJson ← gptQuery prompt 1 temp
    let outJson :=
      (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let out? := (outJson.getArrVal? 0).bind fun js => js.getObjVal? textField
    let outJson :=
        match (out?) with
        | Except.error s => Json.str s!"query for translation failed: {s}"
        | Except.ok js => js
    return outJson.getStr!

/-- reverse translation from `Lean` to natural language -/
@[deprecated leanToPrompt]
def statementToDoc (thm: String)(numSim : Nat:= 5)(temp : JsonNumber := 0) : TermElabM String := do
    let (pairs, _) ← getPromptPairsGeneral thm numSim "statement"
    let prompt := makeFlipStatementsPrompt thm pairs
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

def egThm := "theorem eg_thm : ∀ n: Nat, ∃ m : Nat, m > n ∧ m % 2 = 0"

def egPairs := getPromptPairsGeneral egThm 5 "statement" "statement"

def egPrompt := do
  let (pairs, _) ← egPairs
  return makeFlipStatementsPrompt egThm pairs

-- #eval egPrompt

-- #eval statementToDoc egThm 5 0

-- #eval leanToPrompt "∀ {p : ℕ} [inst : Fact (Nat.Prime p)], p = 2 ∨ p % 2 = 1"

-- #eval leanToPrompt "∀ {α : Type u} {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x"

-- #eval leanToPrompt "{  n :  ℕ } ->  Even   (    (   n +  1  ) * n  )"

/-- array of outputs extracted from OpenAI Json -/
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

/-- array of outputs extracted from Json Array -/
def jsonStringToExprStrArray (jsString: String) : TermElabM (Array String) := do
  try
  let json := Lean.Json.parse  jsString |>.toOption.get!
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getStr? with
            | Except.ok str => pure (some str)
            | Except.error e =>
              throwError m!"json string expected but got {js}, error: {e}"
        pure parsedArr
    | Except.error _ => pure #[jsString]
  return outArr
  catch _ =>
    pure #[jsString]

-- #eval jsonStringToExprStrArray "simple"
-- #eval jsonStringToExprStrArray "[\"simple\", \"simple2\"]"


/-- given json returned by open-ai obtain the best translation -/
def jsonToExpr' (json: Json) : TermElabM Expr := do
  let output ← jsonToExprStrArray json
  arrayToExpr output

/-- translation from a comment-like syntax to a theorem statement -/
elab "//-" cb:commentBody  : term => do
  let s := cb.raw.getAtomVal
  let s := (s.dropRight 2).trim
  -- querying codex
  let js ← getCodeJson  s
  -- filtering, autocorrection and selection
  let e ← jsonToExpr' js
  trace[Translate.info] m!"{e}"
  return e

def uncurriedView(numArgs: Nat)(e: Expr) : MetaM String :=
  match numArgs with
  | 0 => do return " : " ++ (← e.view)
  | k +1 =>
    match e with
    | Expr.forallE n t _ bi => do
      let core := s!"{n.eraseMacroScopes} : {← t.view}"
      let typeString :=s!"{← t.view}"
      let argString := match bi with
      | BinderInfo.implicit => "{"++ core ++ "}"
      | BinderInfo.strictImplicit => "{{ "++ core ++ "}}"
      | BinderInfo.instImplicit =>
        if (`inst).isPrefixOf n then s!"[{typeString}]"
          else s!"[{core}]"
      | BinderInfo.default => s!"({core})"
      let tail : String ←
        withLocalDecl `func BinderInfo.default e fun func =>
          withLocalDecl n bi t fun arg => do
            let fx := mkAppN func #[arg]
            let newType ← inferType fx
            uncurriedView k newType
      return " " ++ argString ++ tail
    | _ => do return " : " ++ (← e.view)

elab "uncurry2" e:term : term => do
  let e ← Term.elabTerm e none
  let e ← uncurriedView 2 e
  return mkStrLit e

universe u


def translateViewM (s: String) : TermElabM String := do
  let js ← getCodeJson  s
  let output ← jsonToExprStrArray js
  trace[Translate.info] m!"{output}"
  let e? ← arrayToExpr? output
  match e? with
  | some (e, _) => do
    e.view
  | none => do
    let stx ← output.findSomeM? <| fun s => do
      let exp ←  identMappedFunStx s
      return exp.toOption
    return stx.getD "False"


/-- view of string in core; to be run with Snapshot.runCore
-/
def translateViewCore (s: String) : CoreM String :=
  (translateViewM s).run'.run'
