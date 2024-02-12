import Lean
import LeanAide.Aides

open Lean Meta

structure ChatParams where
  n : Nat := 1
  temp : JsonNumber := 0.2
  stopTokens : Array String :=  #[":=", "-/"]
  model : String := "gpt-3.5-turbo"
  max_tokens : Nat := 1600

inductive ChatServer where
  | openAI
  | azure (deployment: String := "leanaide-gpt4")
  | generic (url: String)

namespace ChatServer

def url : ChatServer → IO String
  | openAI =>
      return "https://api.openai.com/v1/chat/completions"
  | azure deployment =>
      azureURL deployment
  | generic url =>
      return url++"/v1/chat/completions"

def authHeader? : ChatServer → IO (Option String)
  | openAI => do
    let key? ← openAIKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "OPENAI_API_KEY not set"
    return some <|"Authorization: Bearer " ++ key
  | azure _ => do
    let key? ← azureKey
    let key :=
    match key? with
      | some k => k
      | none => panic! "AZURE_OPENAI_KEY not set"
    return some <| "api-key: " ++ key
  | generic _ =>
    return none

def query (server: ChatServer)(messages : Json)(params : ChatParams) : CoreM Json := do
  let dataJs := Json.mkObj [("model", params.model), ("messages", messages)
  , ("temperature", Json.num params.temp), ("n", params.n), ("max_tokens", params.max_tokens),
  ("stop", Json.arr <| params.stopTokens |>.map Json.str)
  ]
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
  let out ←  IO.Process.output {
        cmd:= "curl",
        args:= args ++ #["--data", data]}
  trace[Translate.info] "Model response: {out.stdout} (stderr: {out.stderr})"
  let queryJs := Json.mkObj [
    ("url", Json.str url),
    ("arguments", Json.arr <| baseArgs.map (Json.str)),
    ("data", data)]
  -- IO.eprintln s!"Received response from {url} at {← IO.monoMsNow }; time taken: {(← IO.monoMsNow) - start}"
  match Lean.Json.parse out.stdout with
  | Except.ok j =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", true), ("response", j)])
    return j
  | Except.error e =>
    appendLog "chat_queries"
      (Json.mkObj [("query", queryJs), ("success", false), ("error", e), ("response", out.stdout)])
    panic! s!"Error parsing JSON: {e}; source: {out.stdout}"

end ChatServer

structure ChatExample where
  user : String
  assistant : String

def ChatExample.messages (ex : ChatExample) : List Json :=
  [Json.mkObj [("role", "user"), ("content", ex.user)],
    Json.mkObj [("role", "assistant"), ("content", ex.assistant)]]

abbrev ToChatExample := String × Json → Option ChatExample

def simpleChatExample : ToChatExample
  | (docString, data) => data.getObjValAs? String "theorem" |>.toOption.map fun thm => {user := docString, assistant:= thm}

def fullTheorem (js: Json) : Option String := do
  let thm ← js.getObjValAs? String "theorem" |>.toOption
  let name ← js.getObjValAs? String "name" |>.toOption
  let isProp ← js.getObjValAs? Bool "isProp" |>.toOption
  return if isProp then
    s!"theorem {name} : {thm} := by sorry"
  else
    s!"def {name} : {thm} := sorry"

def displaydDoc (doc: String)(isProp: Bool) : String :=
  if (isProp) then s!"Consider the mathematical theorem.
**Theorem:**
{doc}
---
Translate the above mathematical statement into a Lean 4 `theorem` with proof `by sorry`. Give the Lean code only"
  else s!"Consider the mathematical definition.
**Definition:**
{doc}
---
Translate the above mathematical definition into a Lean 4 `def` with value `by sorry`. Give the Lean code only"


def docChatExample
  (fullThm: Bool := false)(fullDoc : Bool := false) : ToChatExample
  | (docString, data) =>
    do
    let thm ← data.getObjValAs? String "theorem" |>.toOption
    let name ← data.getObjValAs? String "name" |>.toOption
    let isProp ← data.getObjValAs? Bool "isProp" |>.toOption
    let user := if fullDoc then displaydDoc docString isProp else
      docString
    let assistant := if fullThm then s!"theorem {name} : {thm} := by sorry" else thm
    return {user := user, assistant := assistant}
