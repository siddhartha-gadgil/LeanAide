import Lean
import LeanAideCore.Aides
import LeanAideCore.Template
import LeanAideCore.MathDoc
import LeanAideCore.Resources

open Lean Meta System

deriving instance Repr for Lean.Json

namespace OpenAI

structure Client where
  apiKey : String
  organization : Option String := none
  project : Option String := none
  baseUrl : String := "https://api.openai.com/v1"
  deriving Inhabited, Repr

inductive Role where
  | developer | system | user | assistant | tool | function
  deriving Inhabited, Repr

instance : ToJson Role where
  toJson
    | .developer => "developer"
    | .system    => "system"
    | .user      => "user"
    | .assistant => "assistant"
    | .tool      => "tool"
    | .function  => "function"

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
  deriving Inhabited, Repr

instance : ToJson ContentPart where
  toJson
    | .text t => Json.mkObj [("type", "text"), ("text", t)]
    | .imageUrl img => Json.mkObj [("type", "image_url"), ("image_url", toJson img)]
    | .file f => Json.mkObj [("type", "file"), ("file", toJson f)]
    | .inputAudio d f => Json.mkObj [("type", "input_audio"), ("input_audio", Json.mkObj [("data", d), ("format", f)])]

inductive Content where
  | str (s : String)
  | parts (p : Array ContentPart)
  deriving Inhabited, Repr

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
  deriving Repr

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
  deriving ToJson, Inhabited, Repr

structure ChatCompletionRequest where
  model : String
  messages : Array ChatMessage
  n : Option Nat := none -- number of chat completion choices
  reasoning_effort : Option ReasoningEffort := none
  response_format : Option ResponseFormat := none
  temperature : Option Float := none
  max_completion_tokens : Option Nat := none
  deriving ToJson, Inhabited, Repr

structure ChatCompletionResponse where
  id : String
  object : String
  created : Nat
  model : String
  choices : Array Json
  usage : Option Json
  deriving FromJson, Inhabited, Repr

#eval (default : ChatCompletionResponse)

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
  deriving FromJson, Inhabited, Repr

/- API Call Method -/

def runCurl (client : Client) (method : String) (endpoint : String) (body : Option Json := none) : IO <| Except String String := do
  let mut args := #["-s", "-X", method, client.baseUrl ++ endpoint,
    "-H", s!"Authorization: Bearer {client.apiKey}",
    "-H", "Content-Type: application/json"]

  if let some org := client.organization then
    args := args.push "-H" |>.push s!"OpenAI-Organization: {org}"
  if let some proj := client.project then
    args := args.push "-H" |>.push s!"OpenAI-Project: {proj}"

  if let some payload := body then
    args := args.push "-d" |>.push (payload.compress)

  let out ← IO.Process.output { cmd := "curl", args := args }
  if out.exitCode != 0 then
    return .error s!"Curl failed with code {out.exitCode}: {out.stderr}"
    -- throw <| IO.userError s!"Curl failed with code {out.exitCode}: {out.stderr}"
  return .ok out.stdout

def parseJson! {α} [FromJson α] [Inhabited α] (result : Except String String) : IO α := do
  match result with
  | .error _ => return default
  | .ok raw =>
    match Json.parse raw with
    | .error e => throw <| IO.userError s!"Invalid JSON structure: {e}\nPayload: {raw}"
    | .ok j => match fromJson? j with
              | .error e => throw <| IO.userError s!"Failed to parse into struct: {e}\nPayload: {raw}"
              | .ok val => return val

/- Chat Completions Endpoints -/

namespace Chat

  def create (client : Client) (req : ChatCompletionRequest) : IO ChatCompletionResponse := do
    let result ← runCurl client "POST" "/chat/completions" (toJson req)
    parseJson! result

  def list (client : Client) : IO Json := do
    let result ← runCurl client "GET" "/chat/completions"
    parseJson! result

  def get (client : Client) (id : String) : IO Json := do
    let result ← runCurl client "GET" s!"/chat/completions/{id}"
    parseJson! result

  def update (client : Client) (id : String) (metadata : Json) : IO Json := do
    let payload := Json.mkObj [("metadata", metadata)]
    let result ← runCurl client "POST" s!"/chat/completions/{id}" payload
    parseJson! result

  def delete (client : Client) (id : String) : IO Json := do
    let result ← runCurl client "DELETE" s!"/chat/completions/{id}"
    parseJson! result

end Chat

/- Responses Endpoints -/

namespace Responses

  def create (client : Client) (req : ResponseRequest) : IO APIResponse := do
    let result ← runCurl client "POST" "/responses" (toJson req)
    parseJson! result

  def get (client : Client) (id : String) : IO APIResponse := do
    let result ← runCurl client "GET" s!"/responses/{id}"
    parseJson! result

  def cancel (client : Client) (id : String) : IO Json := do
    let result ← runCurl client "POST" s!"/responses/{id}/cancel" (Json.mkObj [])
    parseJson! result

  def delete (client : Client) (id : String) : IO Json := do
    let result ← runCurl client "DELETE" s!"/responses/{id}"
    parseJson! result

  def compact (client : Client) (id : String) : IO Json := do
    let payload := Json.mkObj [("response_id", toJson id)]
    let result ← runCurl client "POST" "/responses/compact" payload
    parseJson! result

end Responses

end OpenAI
