import Lean
import LeanAideCore.Aides
import LeanAideCore.Template
import LeanAideCore.MathDoc
import LeanAideCore.Resources

open Lean Meta System LeanAide

#logIO leanaide.llm.info

variable [LeanAideBaseDir]

deriving instance Repr for Lean.Json

partial def removeNulls (js : Json) : Json :=
  match js with
  | Json.obj tmap =>
    let filtered := tmap.foldl (init := {}) fun tm key value =>
      match value with
      | Json.null => tm
      | _         => tm.insert key (removeNulls value)
    Json.obj filtered
  | Json.arr a => Json.arr (a.map removeNulls)
  | _ => js

namespace OpenAI

structure Client where
  apiKey : String := ""
  organization : Option String := none
  project : Option String := none
  baseUrl : String := "https://api.openai.com/v1"
  deriving Repr

instance : Inhabited Client where
  default := {
    apiKey := "",
    organization := none,
    project := none,
    baseUrl := "https://api.openai.com/v1"
  }

inductive Role where
  | developer | system | user | assistant | tool | function
  deriving Inhabited, Repr, ToJson, FromJson

inductive ReasoningEffort where
  | none | minimal | low | medium | high | xhigh
  deriving Inhabited, Repr, Hashable, FromJson, DecidableEq

instance : ToJson ReasoningEffort where
  toJson
    | .none    => "none"
    | .minimal => "minimal"
    | .low     => "low"
    | .medium  => "medium"
    | .high    => "high"
    | .xhigh   => "xhigh"

structure Reasoning where
  effort : Option ReasoningEffort := none
  summary : Option String := none -- "auto" or "detailed" or "concise"
  deriving Inhabited, Repr, ToJson

structure ImageUrl where
  url : String
  detail : Option String := none -- "auto" or "low" or "high"
  deriving ToJson, FromJson, Repr, Inhabited

structure FileInput where
  file_id : Option String := none
  file_data : Option String := none -- base64 encoded
  filename : Option String := none
  deriving ToJson, FromJson, Repr, Inhabited

inductive ContentPart where
  | text (text : String)
  | imageUrl (image_url : ImageUrl)
  | file (file : FileInput)
  | inputAudio (data : String) (format : String) -- base64 encoded `dat`, "wav" or "mp3" `format`
  deriving Inhabited, Repr, FromJson

instance : ToJson ContentPart where
  toJson
    | .text t => Json.mkObj [("type", "text"), ("text", t)]
    | .imageUrl img => Json.mkObj [("type", "image_url"), ("image_url", toJson img)]
    | .file f => Json.mkObj [("type", "file"), ("file", toJson f)]
    | .inputAudio d f => Json.mkObj [("type", "input_audio"), ("input_audio", Json.mkObj [("data", d), ("format", f)])]

inductive Content where
  | str (s : String)
  | parts (p : Array ContentPart)
  deriving Inhabited, Repr, FromJson, ToJson

instance : ToJson Content where
  toJson
    | .str s => toJson s
    | .parts p => toJson p

structure JSONSchema where
  name : String
  schema : Json
  description : Option String := none
  strict : Option Bool := none
  deriving ToJson, FromJson, Inhabited, Repr

inductive ResponseFormat where
  | text
  | jsonObject
  | jsonSchema (schema : JSONSchema)
  deriving Repr, FromJson, ToJson

instance : ToJson ResponseFormat where
  toJson
    | .text => Json.mkObj [("type", "text")]
    | .jsonObject => Json.mkObj [("type", "json_object")]
    | .jsonSchema s => Json.mkObj [("type", "json_schema"), ("json_schema", toJson s)]

structure JSONSchemaConfig where
  type : String := "json_schema"
  name : String
  schema : Json
  description : Option String := none
  strict : Option Bool := none
  deriving ToJson, FromJson, Inhabited, Repr

inductive ResponseFormatTextConfig where
  | text
  | jsonObject
  | jsonSchema (schemaConfig : JSONSchemaConfig)
  deriving Repr

instance : ToJson ResponseFormatTextConfig where
  toJson
    | .text => Json.mkObj [("type", "text")]
    | .jsonObject => Json.mkObj [("type", "json_object")]
    | .jsonSchema s => toJson s

structure ResponseTextConfig where
  format : Option ResponseFormatTextConfig := none
  verbosity : Option String := none -- "low" or "medium" or "high"
  deriving Inhabited, ToJson, Repr

/- Chat Completions API -/

structure ChatMessage where
  role : Role
  content : Content
  name : Option String := none
  deriving FromJson, ToJson, Inhabited, Repr

structure ChatCompletionRequest where
  model : String := "gpt-5"
  messages : Json
  n : Option Nat := none -- number of chat completion choices
  reasoning_effort : Option ReasoningEffort := none
  response_format : Option ResponseFormat := none
  temperature : Option JsonNumber := none
  max_completion_tokens : Option Nat := none
  deriving FromJson, ToJson, Inhabited, Repr

structure ChatCompletionMessage where
  content : String
  role : Role
  deriving FromJson, ToJson, Inhabited, Repr

structure Choice where
  message : ChatCompletionMessage
  index : Nat
  deriving FromJson, ToJson, Inhabited, Repr

structure ChatCompletionResponse where
  id : String
  object : String
  created : Nat
  model : String
  choices : Array Choice
  usage : Option Json
  deriving FromJson, ToJson, Inhabited, Repr

namespace ChatCompletionResponse

def getChoiceIndex? (resp : ChatCompletionResponse) (i : Nat) : Option Choice :=
  resp.choices.find? (fun c => c.index == i)

def getContentIndex? (resp : ChatCompletionResponse) (i : Nat) : Option String :=
  match resp.getChoiceIndex? i with
  | none => none
  | some choice => choice.message.content

def getContents (resp : ChatCompletionResponse) : Array String :=
  resp.choices.map fun choice => choice.message.content

end ChatCompletionResponse

/- Responses API -/

structure ResponseInputMessage where
  role : Role
  content : Content
  phase : Option String := none
  type : String := "message"
  deriving ToJson, Inhabited, Repr

structure ResponseRequest where
  model : Option String := none
  input : Array ResponseInputMessage
  background : Option Bool := none
  reasoning : Option Reasoning := none
  text : Option ResponseTextConfig := none -- contains response format
  tools : Option Json := none -- have to expand this
  deriving ToJson, Inhabited, Repr

structure APIResponse where
  id : String
  object : String
  created_at : Nat
  output : Array Json
  usage : Option Json
  deriving FromJson, ToJson, Inhabited, Repr

/- API Call Method -/

def runCurl (client : Client) (method : String) (endpoint : String) (body : Option Json := none) : MetaM <| Except String String := do
  let mut args := #["-s", "-X", method, client.baseUrl ++ endpoint,
    "-H", s!"Authorization: Bearer {client.apiKey}",
    "-H", "Content-Type: application/json"]

  if let some org := client.organization then
    args := args.push "-H" |>.push s!"OpenAI-Organization: {org}"
  if let some proj := client.project then
    args := args.push "-H" |>.push s!"OpenAI-Project: {proj}"

  if let some payload := body then
    args := args.push "-d" |>.push (payload.compress)

  traceAide `leanaide.llm.info s!"OpenAI API Call Payload: {body.getD Json.null}"

  let out ← IO.Process.output { cmd := "curl", args := args }
  if out.exitCode != 0 then
    traceAide `leanaide.llm.info s!"Curl failed with code {out.exitCode}: {out.stderr}"
    -- throw <| IO.userError s!"Curl failed with code {out.exitCode}: {out.stderr}"
    return .error out.stderr
  return .ok out.stdout

def parseJson {α} [FromJson α] [Inhabited α] (result : Except String String) : MetaM α := do
  match result with
  | .error _ => return default
  | .ok raw =>
    match Json.parse raw with
    | .error e =>
      traceAide `leanaide.llm.info s!"Error parsing JSON: {e}; source: {raw}"
      return default
    | .ok js => match fromJson? js with
              | .error e =>
                traceAide `leanaide.llm.info s!"Failed to parse JSON into struct: {e}; source: {js}"
                return default
              | .ok val => return val

def checkClient (client : Client) : IO Client := do
  match client.apiKey with
  | "" => return {client with apiKey := ← openAIKey}
  | _ => return client

/- Chat Completions Endpoints -/

namespace Chat

def create (req : ChatCompletionRequest) (client : Client := default) : MetaM ChatCompletionResponse := do
  let client ← checkClient client
  let reqJs := removeNulls <| toJson req
  let result ← runCurl client "POST" "/chat/completions" reqJs
  parseJson result

def list (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let result ← runCurl client "GET" "/chat/completions"
  parseJson result

def get (id : String) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let result ← runCurl client "GET" s!"/chat/completions/{id}"
  parseJson result

def update (id : String) (metadata : Json) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let payload := Json.mkObj [("metadata", metadata)]
  let result ← runCurl client "POST" s!"/chat/completions/{id}" payload
  parseJson result

def delete (id : String) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let result ← runCurl client "DELETE" s!"/chat/completions/{id}"
  parseJson result

end Chat

/- Responses Endpoints -/

namespace Responses

def create (req : ResponseRequest) (client : Client := default) : MetaM APIResponse := do
  let client ← checkClient client
  let reqJs := removeNulls <| toJson req
  let result ← runCurl client "POST" "/responses" reqJs
  parseJson result

def get (id : String) (client : Client := default) : MetaM APIResponse := do
  let client ← checkClient client
  let result ← runCurl client "GET" s!"/responses/{id}"
  parseJson result

def cancel (id : String) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let result ← runCurl client "POST" s!"/responses/{id}/cancel" (Json.mkObj [])
  parseJson result

def delete (id : String) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let result ← runCurl client "DELETE" s!"/responses/{id}"
  parseJson result

def compact (id : String) (client : Client := default) : MetaM Json := do
  let client ← checkClient client
  let payload := Json.mkObj [("response_id", toJson id)]
  let result ← runCurl client "POST" "/responses/compact" payload
  parseJson result

end Responses

end OpenAI
