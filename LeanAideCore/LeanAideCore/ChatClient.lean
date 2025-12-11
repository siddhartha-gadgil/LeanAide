import Lean
import LeanAideCore.Aides
import LeanAideCore.Template
import LeanAideCore.MathDoc
import LeanAideCore.Resources

open Lean Meta System

namespace LeanAide

variable [LeanAideBaseDir]
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
    | Except.error e =>
      IO.eprintln s!"json parsing error: {e}"
      return #[]

structure ChatParams where
  n : Nat := 1
  temp : JsonNumber := 1.0
  stopTokens : Array String :=  #[]
  maxTokens : Nat := 1600
  deriving Repr, Hashable, FromJson, ToJson, DecidableEq

instance : Inhabited ChatParams := ⟨{}⟩

namespace ChatParams
def stopColEq (params: ChatParams) : Bool :=
  params.stopTokens.contains ":="

def splitOutputs (params: ChatParams)
  (outputs : Array String) : Array String :=
  if stopColEq params then
    outputs
  else
    let outs := outputs.toList.flatMap colEqSegments
    outs.toArray

def noStop (p: ChatParams) : ChatParams :=
  {p with stopTokens := #["\n\n"]}

def withoutStop (p: ChatParams)(stopless: Bool) : ChatParams :=
  if stopless then noStop p else p

end ChatParams


inductive ChatServer where
  | openAI (model: String := "gpt-4o") (authHeader? : Option String := none)
  | azure (deployment: String := "GPT4TestDeployment")
      (model: String := "GPT-4") (authHeader? : Option String := none)
  | gemini (model: String := "gemini-1.5-pro-001")  (key? : Option String := none)
  | generic (model: String) (url: String) (authHeader? : Option String) (hasSysPropmpt : Bool := false)
  deriving Repr, FromJson, ToJson, DecidableEq, Hashable

namespace ChatServer

def default : ChatServer := .openAI "gpt-4o"

instance : Inhabited ChatServer := ⟨default⟩

initialize queryCache : IO.Ref
  (Std.HashMap (ChatServer × Json × ChatParams) Json) ← IO.mkRef {}

initialize pendingQueries :
  IO.Ref (Array (ChatServer × Json × ChatParams)) ← IO.mkRef #[]

def url : ChatServer → IO String
  | openAI _ _ =>
      return "https://api.openai.com/v1/chat/completions"
  | azure deployment _ _ =>
      azureURL deployment
  | gemini _ _ => do
      let url ←  pure s!"https://generativelanguage.googleapis.com/v1beta/openai/chat/completions"
      -- IO.eprintln s!"Google URL: {url}"
      return url
  | generic _ url .. =>
      return url

def model : ChatServer → String
  | openAI model _ => model
  | azure _ model _ => model
  | generic model .. => model
  | gemini model _ => model

def setModel (modelName: String) : ChatServer → ChatServer
  | openAI _ h? => .openAI modelName h?
  | azure deployment _ h? => .azure deployment modelName h?
  | generic _ url h? p => .generic modelName url h? p
  | gemini _ h? => .gemini modelName h?

def setUrl (url: String) : ChatServer → ChatServer
  | generic model _ h? p => .generic model url h? p
  | openAI model h? => .generic model url h? false
  | azure _ model h? => .generic model url h? false
  | gemini model h? => .generic model url h? false

def hasSysPrompt : ChatServer → Bool
  | openAI model _ => !(model.startsWith "o")
  | azure _ _ _ => true
  | generic _ _ _ b => b
  | gemini _ _=> true


def authHeader? : ChatServer → IO (Option String)
  | openAI _ h? => match h? with
    | some h => pure h
    | none =>  do
    let key ←  openAIKey
    return some <|"Authorization: Bearer " ++ key
  | azure _ _ h? => match h? with
    | some h => pure h
    | none => do
    let key? ← azureKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "AZURE_OPENAI_KEY not set"
    return some <| "api-key: " ++ key
  | generic _ _ h? _ =>
    return h?
  | gemini _ h? => match h? with
    | some h => pure h
    | none =>  do
    let key ←  geminiAPIKey
    return some <|"Authorization: Bearer " ++ key

def addKey (key: String) : ChatServer → ChatServer
| .generic model url _ p => .generic model url (some <|"Authorization: Bearer " ++ key) p
| .openAI model _ => .openAI model <| some <|"Authorization: Bearer " ++ key
| .azure deployment model _ => .azure deployment model <| some <| "api-key: " ++ key
| .gemini model _ => .gemini model <| some <|"Authorization: Bearer " ++ key


def addKeyOpt (key?: Option String) (cs : ChatServer) : ChatServer :=
  match key? with
  | some key => addKey key cs
  | none => cs

def queryAux (server: ChatServer)(messages : Json)(params : ChatParams) : CoreM Json := do
  let stopJs := Json.mkObj <| if params.stopTokens.isEmpty then [] else
    [("stop", Json.arr <| params.stopTokens |>.map Json.str)]
  let dataJs := Json.mkObj [("model", server.model), ("messages", messages)
  , ("temperature", Json.num params.temp), ("n", params.n)]
  let dataJs := dataJs.mergeObj stopJs
  let data := dataJs.pretty
  trace[Translate.info] "Model query: {data}"
  -- logInfo s!"Querying {server.model} with {data}"
  let url ← server.url
  -- logInfo "Authenticating"
  let authHeader? ← server.authHeader?
  -- logInfo s!"Auth header: {authHeader?}"
  -- IO.eprintln s!"Querying {url} at {← IO.monoMsNow }"
  let start ← IO.monoMsNow
  let baseArgs :=
    #[url, "-X", "POST", "-H", "Content-Type: application/json"]
  let args := match authHeader? with
    | some h => #["-H", h] ++ baseArgs
    | none => baseArgs
  -- logInfo s!"Querying {url} with {data}"
  let output ← IO.Process.output {cmd := "curl", args := (args ++ #["--data", data])}
  let output := output.stdout
  trace[Translate.info] "Model response: {output}"
  let queryJs := Json.mkObj [
    ("url", Json.str url),
    ("arguments", Json.arr <| baseArgs.map (Json.str)),
    ("data", data)]
  IO.eprintln s!"Received response from {url} at {← IO.monoMsNow }; time taken: {(← IO.monoMsNow) - start}"
  IO.eprintln s!"Response: {output}" -- uncomment for debugging
  match Lean.Json.parse output with
  | Except.ok j =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", true), ("response", j)])
    return j
  | Except.error e =>
    IO.eprintln s!"Error parsing JSON: {e}; source: {output}"
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", false), ("error", e), ("response", output)])
    return .null

def query (server: ChatServer)(messages : Json)(params : ChatParams) : CoreM Json := do
  IO.eprintln s!"Querying: {toJson server |>.compress}"
  -- logInfo s!"Querying {server.model}"
  let file : System.FilePath :=
    (← cachePath) / "chat" /
      s!"{hash server}_{hash params}_{hash messages}.json"
  if ← file.pathExists then
    IO.eprintln s!"Reading from cache: {file}"
    -- logInfo s!"Reading from cache: {file}"
    let output ← IO.FS.readFile file
    match Json.parse output with
    | Except.ok j => return j
    | Except.error e =>
      IO.eprintln s!"Error parsing JSON: {e}; source: {output}"
      let result ←  queryAux server messages params
      unless (result.getObjVal? "error").toOption.isSome do
        IO.FS.writeFile file result.pretty
      return result
  else
    -- IO.eprintln s!"Querying server"
    -- logInfo s!"Querying server"
    let result ←  queryAux server messages params
    IO.FS.writeFile file result.pretty
    return result

def pollCacheQuery (server: ChatServer)(messages : Json)
    (params : ChatParams) (retries: Nat) : CoreM Json := do
  let key := (server, messages, params)
  let cache ← queryCache.get
  match cache.get? key with
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
    match cache.get? key with
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
  | azure deployment _ _ => do
    let path := (← llmDir) / "azure" / deployment
    IO.FS.createDirAll path
    return path
  | _ => do
    let path := (← llmDir) / server.model
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

structure ChatPair where
  user : String
  assistant : String
deriving FromJson, ToJson, Repr, DecidableEq, Inhabited

def ChatPair.messages (ex : ChatPair)(responder := "assistant") : List Json :=
  [Json.mkObj [("role", "user"), ("content", ex.user)],
    Json.mkObj [("role", responder), ("content", ex.assistant)]]

abbrev ToChatExample := String × Json → MetaM (Option ChatPair)

def simpleChatExample : ToChatExample
  | (docString, data) =>
    return data.getObjValAs? String "type" |>.toOption.map fun thm => {user := docString, assistant:= thm}

def detailedType (js: Json) : MetaM <| Option String := do
  let type? := js.getObjValAs? String "type" |>.toOption
  let name? := js.getObjValAs? String "name" |>.toOption
  let info? ← name?.mapM fun n => getConstInfo n.toName
  let expr? := info?.map (·.type)
  let type?' ←
    try
      expr?.mapM (fun e => ppExprDetailed e)
    catch _ => pure none
  return type?' |>.orElse fun _ => type?


def fullStatement? (js: Json) : Option String := do
  let type ← js.getObjValAs? String "type" |>.toOption
  let name ← js.getObjValAs? String "name" |>.toOption
  let isProp ← js.getObjValAs? Bool "isProp" |>.toOption
  return if isProp then
    s!"theorem {name} : {type} := by sorry"
  else
    let value := js.getObjValAs? String "value" |>.toOption |>.getD "sorry"
    s!"def {name} : {type} := {value}"

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
      let decl? := env.find? name.toName
      let expr? := decl?.bind (fun d => d.value?)
      let fmt? ← expr?.mapM (fun e => ppExpr e)
      pure <| fmt?.map (·.pretty) |>.getD "sorry"
    let assistant :=
      if fullThm then s!"{head} {name} : {thm} := {value}" else thm
    return some {user := user, assistant := assistant}
    | _,_,_ => return none


def docDetailedChatExample (fullThm: Bool := true)(fullDoc : Bool := true) : ToChatExample
  | (docString, data) => do
    let thm? ← detailedType data
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

def simpleDetailedChatExample : ToChatExample
  | (docString, data) => do
    docDetailedChatExample true false (docString, data)


/-- Chat examples, i.e., the dialogues of `user` and `assistant`, from the examples. -/
inductive ChatExampleType
  /-- *user* just gives documentation string, *assistant* responds with only type -/
  | simple
  /-- translation task explicitly spelled out by *user*, *assistant* responds with full statement.-/
  | doc
  /-- *user* just gives documentation string, *assistant* responds with only type but with details in the type -/
  | detailed
  /-- translation task explicitly spelled out by *user*, *assistant* responds with full statement with details in the type.-/
  | detailedDoc
  deriving Repr, FromJson, ToJson, Inhabited, DecidableEq

def ChatExampleType.map? (t: ChatExampleType) : ToChatExample :=
  match t with
  | ChatExampleType.simple => simpleChatExample
  | ChatExampleType.doc => docChatExample
  | ChatExampleType.detailed => simpleDetailedChatExample
  | ChatExampleType.detailedDoc => docDetailedChatExample



/--
A Json object representing a chat message
-/
def message (role content : String) : Json :=
  Json.mkObj [("role", role), ("content", content)]

/--
JSON object for the messages field in a chat prompt,
assuming that there is a system message at the beginning.
-/
def sysMessages (sys: String) (egs : List ChatPair)
  (query : String) (developerId : String := "system") : Json :=
  let head := message developerId sys
  let egArr :=
    egs.flatMap (fun eg  => eg.messages)
  Json.arr <| head :: egArr ++ [message "user" query] |>.toArray

def syslessAnswer := "Sure. I will answer precisely and concisely following instructions"

/--
JSON object for the messages field in a chat prompt,
assuming that there is no system message at the beginning.
-/
def syslessMessages (sys: String)(egs : List <| ChatPair)
    (query : String) : Json :=
  let headEg : ChatPair := ⟨sys, syslessAnswer⟩
  let egArr :=
    (headEg :: egs).flatMap (fun eg  => eg.messages)
  Json.arr <| egArr ++ [message "user" query] |>.toArray


def sysPrompt' := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. Follow EXACTLY the examples given."

def MessageBuilder.header := "You are a coding assistant who translates from natural language to Lean Theorem Prover code following examples. The translated code is preceded by `import Mathlib._`, so do not include import statements. Suppress proofs for brevity. Follow EXACTLY the examples given."

inductive MessageBuilder where
  | syslessBuilder
  | sysBuilder (developerId := "system")
  | directBuilder (headMessage := MessageBuilder.header) (egsHead := "The following are some examples of statements and their translations (proofs are suppressed for brevity):") (egQueryHead := "## Natural language statement\n\n") (egResponseHead := "## Lean Code\n\n") (userHead := "user")
deriving Repr, FromJson, ToJson, Inhabited, DecidableEq

def MessageBuilder.buildMessages (mb: MessageBuilder)
  (sysPrompt: String)(examples: Array ChatPair)
  (query: String) : IO Json := do
  match mb with
  | .syslessBuilder =>
    return syslessMessages sysPrompt examples.toList query
  | .sysBuilder developerId =>
    return sysMessages sysPrompt examples.toList query developerId
  | directBuilder headMessage egsHead egQueryHead egResponseHead userId =>
    let mut text : String := headMessage ++ "\n\n"
    if !examples.isEmpty then
      text := text ++ egsHead ++ "\n\n"
      for eg in examples do
        text := text ++ s!"{egQueryHead}{eg.user}\n\n{egResponseHead}{eg.assistant}\n\n"
      text := text ++ "---\n\n"
    text := text ++ query
    return Json.arr <| #[.mkObj [("role", userId), ("content", text)]]

def ChatServer.messageBuilder (_server: ChatServer) : MessageBuilder := .directBuilder
  -- if server.hasSysPrompt then
  --   .sysBuilder
  -- else
  --   .syslessBuilder

def MessageBuilder.useInstructions : MessageBuilder → Bool
  | .directBuilder .. => false
  | _ => true

/--
Given a query and a list of examples, build messages for a prompt for OpenAI
-/
def mkMessages(query : String)(examples: Array ChatPair)
  (sysPrompt: String)(msg: MessageBuilder := .directBuilder) : IO Json:= do
  msg.buildMessages sysPrompt examples query



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
  (history: Array ChatPair := #[]): CoreM (Array String) := do
  let messages ←  mkMessages queryString history sysPrompt server.messageBuilder
  let data ← ChatServer.query server messages params
  match data.getObjVal? "choices" with
  | Except.error _ =>
    throwError m!"no choices field in {data}"
  | Except.ok data =>
    let outputs ← getMessageContents data
    return outputs

def mathCompletions (server: ChatServer)
  (queryString: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (history: Array ChatPair := #[]): CoreM (Array String) := do
  let sysPrompt ← mathPrompt
  ChatServer.completions server queryString sysPrompt n params history

def prove (server: ChatServer)
  (thm: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove" [("theorem", thm)]
  ChatServer.mathCompletions server queryString n params examples

def proveForFormalization (server: ChatServer)
  (thm statement definitions: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove_theorem_for_formalization" [("theorem", thm),  ("statement", statement), ("definitions", definitions), ("proof_guidelines", Resources.proofGuidelines)]
  ChatServer.mathCompletions server queryString n params examples

def jsonStructured (server: ChatServer)
  (document: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array Json) := do
  let queryString ← fromTemplate "json_structured" [("document", document), ("schema", Resources.paperStructure.pretty)]
  let outs ← ChatServer.mathCompletions server queryString n params examples
  outs.mapM extractJsonM

def prove_with_outline (server: ChatServer)
  (thm outline: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "prove_with_outline" [("theorem", thm), ("outline", outline)]
  ChatServer.mathCompletions server queryString n params examples

def solve (server: ChatServer)
  (problem: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solve" [("problem", problem)]
  ChatServer.mathCompletions server queryString n params examples

def checkEquivalence
  (thm1 thm2 : String) (defBlob? : Option String) (server: ChatServer := ChatServer.openAI "o3-mini")
  (params: ChatParams := {})
  (examples: Array ChatPair := #[]): CoreM (Array <| Bool × String) := do
  let queryString ←
    match defBlob? with
    | none =>
    fromTemplate "check_equivalence" [("theorem1", thm1), ("theorem2", thm2)]
    | some defBlob =>
    fromTemplate "check_equivalence_with_defs" [("theorem1", thm1), ("theorem2", thm2), ("definitions", defBlob)]
  let responses ← ChatServer.mathCompletions server queryString 1 params examples
  -- IO.eprintln responses
  return responses.map fun s =>
    ((s.toLower.trim.splitOn "true").length > 1, s)

def mathTerms (server: ChatServer)
    (statement : String)(n: Nat := 3)
    (params: ChatParams := {n := n, stopTokens := #[]})
    (examples: Array ChatPair := #[]): CoreM (Array (Array String)) := do
    let queryString ← fromTemplate "math_terms" [("statement", statement)]
    let responses ← ChatServer.mathCompletions server queryString n params examples
    return responses.filterMap getTerms
  where getTerms (s: String) : Option (Array String) :=
    let js? := Json.parse s |>.toOption
    js?.bind fun js => fromJson? js |>.toOption

def solution_to_theory (server: ChatServer)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "solution_to_theory" [("problem", problem), ("solution", solution)]
  ChatServer.mathCompletions server queryString n params examples

def structuredProof (server: ChatServer)
  (pf: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (alertErrors : Bool := false)
  : CoreM (Array Json) := do
  let instructions ← MathDoc.instructions alertErrors
  let init : ChatPair := {
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
  let init : ChatPair := {
    user := instructions
    assistant := "Please provide the theorem and proof. I will translated this into ProofJSON format."
  }
  let examples := #[init]
  let outs ← ChatServer.mathCompletions server pf n params examples
  return outs

def structuredProofFromSolution (server: ChatServer)
  (problem solution: String)(n: Nat := 1)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]) : CoreM (Array Json) := do
  let theories ← solution_to_theory server problem solution n params examples
  let results ← theories.mapM (structuredProof server)
  return results.foldl (· ++ ·) #[]

def structuredProofFromStatement (server: ChatServer)
  (statement: String)(n m: Nat := 1)
  (params: ChatParams := {n := m, stopTokens := #[]})
  (examples: Array ChatPair := #[]) :
    CoreM (Array (String × Array Json)) := do
  let proofs ← server.prove statement n params examples
  let theories := proofs.map fun pf => (pf, s!"## Theorem : {statement}\n##Proof: {pf}")
  theories.mapM fun (pf, thmPf) => do
    pure (pf, ← structuredProof server thmPf)

def theoremName (server: ChatServer)
  (statement: String): CoreM Name := do
    let query := s!"Give a name following the conventions of the Lean Prover 4 and Mathlib for the theorem: \n{statement}\n\nUse snakecase and ensure that there are no whitespaces. Give ONLY the name of the theorem."
    let namesArr ←  server.mathCompletions query 1
    let llm_name := namesArr[0]! |>.replace "`" ""
          |>.replace "\""  "" |>.trim
        -- logInfo llm_name
    return llm_name.toName

def fullStatement (server: ChatServer)
  (statement: String): CoreM String := do
    let query := s!"Rewrite the following in typical mathematical English using LaTeX if necessary:\n{statement}\nGive ONLY the English statement."
    let statementsArr ←  server.mathCompletions query 1
    return statementsArr[0]? |>.getD statement

-- @[deprecated structuredProof]
-- def structuredProofFull (server: ChatServer)
--   (pf: String)(n: Nat := 1)
--   (params: ChatParams := {n := n, stopTokens := #[]})
--   (examples: Array ChatPair := #[]): CoreM (Array Json) := do
--   let queryString ← structuredProofQueryFull pf
--   let outs ← ChatServer.mathCompletions server queryString n params examples
--   return outs.map extractJson

-- @[deprecated structuredProof]
-- def make_structured (server: ChatServer)
--   (text: String)(n: Nat := 3)
--   (params: ChatParams := {n := n, stopTokens := #[]})
--   (examples: Array ChatPair := #[]): CoreM (Array String) := do
--   let queryString ← fromTemplate "make_structured" [("text", text)]
--   ChatServer.mathCompletions server queryString n params examples

def informalize (server: ChatServer)
  (code: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let text ← fromTemplate "informalize" [("code", code)]
  ChatServer.completions server text (← sysPrompt) n params examples

def add_statements (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "add_statements" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_deductions (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_deductions" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_observations (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_observations" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def expand_justifications (server: ChatServer)
  (text: String)(n: Nat := 3)
  (params: ChatParams := {n := n, stopTokens := #[]})
  (examples: Array ChatPair := #[]): CoreM (Array String) := do
  let queryString ← fromTemplate "expand_justifications" [("json", text)]
  ChatServer.mathCompletions server queryString n params examples

def summarize (server: ChatServer)
  (text: String)
  (examples: Array ChatPair := #[])(n: Nat := 3)
  : CoreM (Array String) := do
  let queryString ← fromTemplate "summarize" [("text", text)]
  ChatServer.mathCompletions server queryString n {n := n, stopTokens := #[]} examples

end ChatServer
