import Lean
import StatementAutoformalisation.Utils

namespace LLM

/-- A structure with all the relevant parameters for making a query to a large language model such as OpenAI Codex. -/
structure Params where
  /-- The Codex model to use. -/
  openAIModel : String := "gpt-3.5-turbo"
  /-- The temperature at which to generate the completion. 
      This is stored as a natural number representing the actual temperature scaled up by a factor of ten. -/
  temperature : Nat := 8
  /-- The number of completions to generate. -/
  n : Nat
  /-- The maximum allowed number of tokens in the completion. -/
  maxTokens : Nat := 300
  /-- The stop tokens for the completion. -/
  stopTokens : Array String := #[":=", "\n\n/-", "\n/-", "/-"]
  /-- The system message to supply to the model. -/
  systemMessage : String
deriving Repr

/-- A `Request` comprises a prompt and a collection of parameters. -/
structure Request extends Params where
  /-- The main prompt for querying the large language model. -/
  messages : Array Lean.Json

/-- Convert the parameters for querying the LLM to `JSON` format. -/
def Request.toJson (req : LLM.Request) : Lean.Json := .mkObj $ [
  ("messages", .arr <| #[.mkObj [("role", "system"), ("content", req.systemMessage)]] ++ req.messages),
  ("model", req.openAIModel),
  ("temperature", .num ⟨req.temperature, 1⟩),
  ("n", req.n),
  ("max_tokens", req.maxTokens),
  ("stop", .arr <| req.stopTokens.map .str)
  ]

/-- The key required to query the large language model. -/
def key : IO String := do
  let some key ← IO.getEnv "OPENAI_API_KEY" | IO.throwServerError "`OPENAI_API_KEY` environment variable not found.
        This is required for the statement translation tool.
        Set it using the bash command `export OPENAI_API_KEY=<key>`,
        where `<key>` is your personal OpenAI key."
  return key

/-- Query the large language model. -/
def Request.queryLLM (req : LLM.Request) : IO Lean.Json := do
  let out ←  IO.Process.output {
      cmd:= "curl", 
      args:= #["https://api.openai.com/v1/chat/completions",
      "-X", "POST",
      "-H", s!"Authorization: Bearer {← key}",
      "-H", "Content-Type: application/json",
      "--data", req.toJson.pretty ]}
  IO.ofExcept <| Lean.Json.parse out.stdout

/-- Get the LLM completions as an array of `String`s. -/
def Request.getLLMCompletions (req : LLM.Request) : IO <| Array String := do
  let out ← queryLLM req
  IO.ofExcept <| do
    let choices ← out.getObjVal? "choices"
    let completions ← choices.getArr?
    completions.mapM <| fun completion => do (← completion.getObjVal? "content").getStr?

end LLM

section Test

def LLM.egReq : LLM.Request := 
{ systemMessage := "You are a large language model."
  messages := #[mkMessage "user" "For all epsilon greater than zero, "], 
  n := 1 }

-- #eval LLM.egReq.getLLMCompletions

end Test