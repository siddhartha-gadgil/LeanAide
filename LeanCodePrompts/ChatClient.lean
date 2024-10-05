import Lean
import Cache.IO
import LeanAide.Aides
import LeanAide.Template

open Lean Meta System

/--
Extracts the content of the message field from a JSON object,
following the OpenAI API format.
-/
def getMessageContents (json: Json) : CoreM (Array String) := do
  let outArr : Array String ←
    match json.getArr? with
    | Except.ok arr =>
        let parsedArr : Array String ←
          arr.filterMapM <| fun js =>
            match js.getObjVal? "message" with
            | Except.ok jsobj =>
                match jsobj.getObjValAs? String "content" with
                | Except.ok str =>
                  pure (some str)
                | Except.error _ =>
                  throwError m!"no  string content field in {jsobj}"
            | Except.error _ =>
                throwError m!"no message field in {js}"

        pure parsedArr
    | Except.error e => throwError m!"json parsing error: {e}"

structure ChatParams where
  n : Nat := 1
  temp : JsonNumber := 0.8
  stopTokens : Array String :=  #[]
  maxTokens : Nat := 1600
  deriving Repr, Hashable, FromJson, ToJson, Inhabited, DecidableEq

namespace ChatParams
def stopColEq (params: ChatParams) : Bool :=
  params.stopTokens.contains ":="

def splitOutputs (params: ChatParams)
  (outputs : Array String) : Array String :=
  if stopColEq params then
    outputs
  else
    let outs := outputs.toList.bind colEqSegments
    outs.toArray

def noStop (p: ChatParams) : ChatParams :=
  {p with stopTokens := #["\n\n"]}

def withoutStop (p: ChatParams)(stopless: Bool) : ChatParams :=
  if stopless then noStop p else p

end ChatParams


inductive ChatServer where
  | openAI (model: String := "gpt-4o")
  | azure (deployment: String := "GPT4TestDeployment")
      (model: String := "GPT-4")
  | google (model: String := "gemini-1.5-pro-001") (location: String := "asia-south1")
  | generic (model: String) (url: String) (hasSysPropmpt : Bool := false)
  deriving Repr, FromJson, ToJson, Inhabited, DecidableEq, Hashable

namespace ChatServer

initialize queryCache : IO.Ref
  (HashMap (ChatServer × Json × ChatParams) Json) ← IO.mkRef {}

initialize pendingQueries :
  IO.Ref (Array (ChatServer × Json × ChatParams)) ← IO.mkRef #[]

def url : ChatServer → IO String
  | openAI _ =>
      return "https://api.openai.com/v1/chat/completions"
  | azure deployment _ =>
      azureURL deployment
  | google _ location => do
      let url ←  pure s!"https://{location}-aiplatform.googleapis.com/v1beta1/projects/{← projectID}/locations/{location}/endpoints/openapi/chat/completions"
      -- IO.eprintln s!"Google URL: {url}"
      return url
  | generic _ url _ =>
      return url++"/v1/chat/completions"

def model : ChatServer → String
  | openAI model => model
  | azure _ model => model
  | generic model _ _ => model
  | google model _ => "google/" ++ model

def hasSysPropmpt : ChatServer → Bool
  | openAI _ => true
  | azure _ _ => true
  | generic _ _ b => b
  | google _ _ => true

def authHeader? : ChatServer → IO (Option String)
  | openAI _ => do
    let key? ← openAIKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "OPENAI_API_KEY not set"
    return some <|"Authorization: Bearer " ++ key
  | azure .. => do
    let key? ← azureKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "AZURE_OPENAI_KEY not set"
    return some <| "api-key: " ++ key
  | generic .. =>
    return none
  | google _ _ => do
    let key ← IO.Process.run {cmd := "gcloud", args := #["auth", "print-access-token"]}
    return some <|"Authorization: Bearer " ++ key.trim

def query (server: ChatServer)(messages : Json)(params : ChatParams) : CoreM Json := do
  let stopJs := Json.mkObj <| if params.stopTokens.isEmpty then [] else
    [("stop", Json.arr <| params.stopTokens |>.map Json.str)]
  let dataJs := Json.mkObj [("model", server.model), ("messages", messages)
  , ("temperature", Json.num params.temp), ("n", params.n), ("max_tokens", params.maxTokens)]
  let dataJs := dataJs.mergeObj stopJs
  let data := dataJs.pretty
  trace[Translate.info] "Model query: {data}"
  let url ← server.url
  let authHeader? ← server.authHeader?
  -- IO.eprintln s!"Querying {url} at {← IO.monoMsNow }"
  -- let start ← IO.monoMsNow
  let baseArgs :=
    #[url, "-X", "POST", "-H", "Content-Type: application/json"]
  let args := match authHeader? with
    | some h => #["-H", h] ++ baseArgs
    | none => baseArgs
  let output ← Cache.IO.runCurl (args ++ #["--data", data])
  trace[Translate.info] "Model response: {output}"
  let queryJs := Json.mkObj [
    ("url", Json.str url),
    ("arguments", Json.arr <| baseArgs.map (Json.str)),
    ("data", data)]
  -- IO.eprintln s!"Received response from {url} at {← IO.monoMsNow }; time taken: {(← IO.monoMsNow) - start}"
  match Lean.Json.parse output with
  | Except.ok j =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", true), ("response", j)])
    return j
  | Except.error e =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", false), ("error", e), ("response", output)])
    panic! s!"Error parsing JSON: {e}; source: {output}"

def pollCacheQuery (server: ChatServer)(messages : Json)
    (params : ChatParams) (retries: Nat) : CoreM Json := do
  let key := (server, messages, params)
  let cache ← queryCache.get
  match cache.find? key with
  | some j => return j
  | none => do
    match retries with
    | 0 =>
      let data ←  server.query messages params
      queryCache.modify (·.insert key data)
      pendingQueries.modify fun q =>
        q.filter (· != key)
      return data
    | k + 1 =>
      IO.sleep 200
      pollCacheQuery server messages params k

def cachedQuery (server: ChatServer)(messages : Json)
    (params : ChatParams) : CoreM Json := do
  let key := (server, messages, params)
  let queue ← pendingQueries.get
  if queue.contains key then
    pollCacheQuery server messages params 40
  else do
    let cache ← queryCache.get
    match cache.find? key with
    | some j =>
      return j
    | none => do
      pendingQueries.modify (·.push key)
      let j ← query server messages params
      queryCache.modify (·.insert key j)
      pendingQueries.modify fun q =>
        q.filter (· != key)
      return j

def dataPath (server: ChatServer) : IO  FilePath := do
  match server with
  | azure deployment _ => do
    let path := llmDir / "azure" / deployment
    IO.FS.createDirAll path
    return path
  | _ => do
    let path := llmDir / server.model
    IO.FS.createDirAll path
    return path

def dump (server: ChatServer)(data : Json)
    (name: String) (task : String): IO Unit := do
  let path ← dataPath server
  let path := path / name
  IO.FS.createDirAll path
  IO.FS.writeFile (path / s!"{task}.json") <| data.pretty

def load (server: ChatServer)(name: String)
    (task : String) : IO Json := do
  let path ← dataPath server
  let path := path / name / s!"{task}.json"
  let js ← IO.FS.readFile path
  match Json.parse js with
  | Except.ok j => return j
  | Except.error e =>
    IO.throwServerError s!"Error parsing JSON: {e}; source: {js}"

end ChatServer

structure ChatExample where
  user : String
  assistant : String
deriving FromJson, ToJson, Repr, DecidableEq, Inhabited

def ChatExample.messages (ex : ChatExample)(responder := "assistant") : List Json :=
  [Json.mkObj [("role", "user"), ("content", ex.user)],
    Json.mkObj [("role", responder), ("content", ex.assistant)]]

abbrev ToChatExample := String × Json → MetaM (Option ChatExample)

def simpleChatExample : ToChatExample
  | (docString, data) =>
    return data.getObjValAs? String "type" |>.toOption.map fun thm => {user := docString, assistant:= thm}

def fullTheorem (js: Json) : Option String := do
  let thm ← js.getObjValAs? String "type" |>.toOption
  let name ← js.getObjValAs? String "name" |>.toOption
  let isProp ← js.getObjValAs? Bool "isProp" |>.toOption
  return if isProp then
    s!"theorem {name} : {thm} := by sorry"
  else
    s!"def {name} : {thm} := sorry"

def displayedDoc (doc: String)(isProp: Bool)(name?: Option String) : String :=
  let withName : String := match name? with
    | some n => s!" with name **{n}**"
    | none => ""
  if (isProp) then s!"Consider the mathematical theorem.
**Theorem:**
{doc}
---
Translate the above mathematical statement into a Lean 4 `theorem`{withName} with proof `by sorry`. Give the Lean code only"
  else s!"Consider the mathematical definition.
**Definition:**
{doc}
---
Translate the above mathematical definition into a Lean 4 `def`{withName}. Give the Lean code only"


def docChatExample
  (fullThm: Bool := true)(fullDoc : Bool := true) : ToChatExample
  | (docString, data) => do
    let thm? := data.getObjValAs? String "type" |>.toOption
    let name? := data.getObjValAs? String "name" |>.toOption
    let isProp?:= data.getObjValAs? Bool "isProp" |>.toOption
    match thm?, name?, isProp? with
    | some thm, some name, some isProp =>
    let user := if fullDoc then displayedDoc docString isProp (some name) else
      docString
    let head := if isProp then "theorem" else "definition"
    let value ←  if isProp then pure "by sorry" else
      let env ← getEnv
      let decl := env.find? name.toName
      let expr? := decl.bind (fun d => d.value?)
      let fmt? ← expr?.mapM (fun e => ppExpr e)
      pure <| fmt?.map (·.pretty) |>.getD "sorry"
    let assistant :=
      if fullThm then s!"{head} {name} : {thm} := {value}" else thm
    return some {user := user, assistant := assistant}
    | _,_,_ => return none



/--
A Json object representing a chat message
-/
def message (role content : String) : Json :=
  Json.mkObj [("role", role), ("content", content)]

/--
JSON object for the messages field in a chat prompt,
assuming that there is a system message at the beginning.
-/
def sysMessages (sys: String) (egs : List <| ChatExample)
  (query : String) : Json :=
  let head := message "system" sys
  let egArr :=
    egs.bind (fun eg  => eg.messages)
  Json.arr <| head :: egArr ++ [message "user" query] |>.toArray

def syslessAnswer := "Sure. I will answer precisely and concisely following instructions"

/--
JSON object for the messages field in a chat prompt,
assuming that there is no system message at the beginning.
-/
def syslessMessages (sys: String)(egs : List <| ChatExample)
    (query : String) : Json :=
  let headEg : ChatExample := ⟨sys, syslessAnswer⟩
  let egArr :=
    (headEg :: egs).bind (fun eg  => eg.messages)
  Json.arr <| egArr ++ [message "user" query] |>.toArray


def sysPrompt' := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."

/--
Given a query and a list of examples, build messages for a prompt for OpenAI
-/
def mkMessages(query : String)(examples: Array ChatExample)
  (sysPrompt: String)(sysLess: Bool := false) : IO Json:= do
  if sysLess then
    return syslessMessages sysPrompt examples.toList query
  else
    return sysMessages sysPrompt examples.toList query



def mathPrompt := getTemplate "math_sys_prompt"

def sysPrompt := getTemplate "sys_prompt"

def transPrompt : IO String := do
  let sys ← sysPrompt
  let trans ← getTemplate "translate_sys_prompt"
  return s!"{sys} {trans}"
namespace ChatServer

def completions (server: ChatServer)
  (queryString: String)(sysPrompt: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let messages ←  mkMessages queryString examples sysPrompt !(server.hasSysPropmpt)
  let data ← ChatServer.query server messages params
  match data.getObjValAs? Json "choices" with
  | Except.error _ =>
    throwError m!"no choices field in {data}"
  | Except.ok data =>
    let outputs ← getMessageContents data
    return outputs

def mathCompletions (server: ChatServer)
  (queryString: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let sysPrompt ← mathPrompt
  ChatServer.completions server queryString sysPrompt n params examples

def prove (server: ChatServer)
  (thm: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove" [("theorem", thm)]
  ChatServer.mathCompletions server queryString n params examples


def prove_with_outline (server: ChatServer)
  (thm outline: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove_with_outline" [("theorem", thm), ("outline", outline)]
  ChatServer.mathCompletions server queryString n params examples

def solve (server: ChatServer)
  (problem: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solve" [("problem", problem)]
  ChatServer.mathCompletions server queryString n params examples

def checkEquivalence (server: ChatServer)
  (thm1 thm2 : String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array Bool) := do
  let queryString ← fromTemplate "check_equivalence" [("theorem1", thm1), ("theorem2", thm2)]
  let responses ← ChatServer.mathCompletions server queryString n params examples
  return responses.map fun s =>
    (s.toLower.trim.splitOn "true").length > 1

def mathTerms (server: ChatServer)
    (statement : String)(n: Nat := 3)
    (params: ChatParams := {n := n, stopTokens := #[]})
    (examples: Array ChatExample := #[]): CoreM (Array (Array String)) := do
    let queryString ← fromTemplate "math_terms" [("statement", statement)]
    let responses ← ChatServer.mathCompletions server queryString n params examples
    return responses.filterMap getTerms
  where getTerms (s: String) : Option (Array String) :=
    let js? := Json.parse s |>.toOption
    js?.bind fun js => fromJson? js |>.toOption

def solution_to_theory (server: ChatServer)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solution_to_theory" [("problem", problem), ("solution", solution)]
  ChatServer.mathCompletions server queryString n params examples

def structuredProof (server: ChatServer)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  : CoreM (Array Json) := do
  let instructions ← jsonProofInstructions
  let init : ChatExample := {
    user := instructions
    assistant := "Please provide the theorem and proof. I will translated this into ProofJSON format."
  }
  let examples := #[init]
  let outs ← ChatServer.mathCompletions server pf n params examples
  outs.mapM extractJsonM

def structuredProofRaw (server: ChatServer)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  : CoreM (Array String) := do
  let instructions ← jsonProofInstructions
  let init : ChatExample := {
    user := instructions
    assistant := "Please provide the theorem and proof. I will translated this into ProofJSON format."
  }
  let examples := #[init]
  let outs ← ChatServer.mathCompletions server pf n params examples
  return outs

def structuredProofFromSolution (server: ChatServer)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]) : CoreM (Array Json) := do
  let theories ← solution_to_theory server problem solution n params examples
  let results ← theories.mapM (structuredProof server)
  return results.foldl (· ++ ·) #[]

@[deprecated structuredProof]
def structuredProofFull (server: ChatServer)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array Json) := do
  let queryString ← structuredProofQueryFull pf
  let outs ← ChatServer.mathCompletions server queryString n params examples
  return outs.map extractJson

@[deprecated structuredProof]
def make_structured (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "make_structured" [("text", text)]
  ChatServer.mathCompletions server queryString n params examples

def informalize (server: ChatServer)
  (code: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let text ← fromTemplate "informalize" [("code", code)]
  ChatServer.completions server text (← sysPrompt) n params examples

def add_statements (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "add_statements" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_deductions (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_deductions" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_observations (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_observations" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_justifications (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatExample := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_justifications" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def summarize (server: ChatServer)
  (text: String)
  (examples: Array ChatExample := #[])(n: Nat := 3)
  : CoreM (Array String) := do
  let queryString ← fromTemplate "summarize" [("text", text)]
  ChatServer.mathCompletions server queryString n {n := n, stopTokens := #[]} examples

end ChatServer
