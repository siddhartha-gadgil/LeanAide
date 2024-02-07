import Lean
import LeanAide.Aides

open Lean Meta Elab Parser Command

def gptQuery(messages: Json)(n: Nat := 1)
  (temp : JsonNumber := 0.2)
  (stopTokens: Array String :=  #[":=", "-/"])(model: String := "gpt-3.5-turbo") : CoreM Json := do
  let key? ← openAIKey
  let key :=
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj [("model", model), ("messages", messages)
  , ("temperature", Json.num temp), ("n", n), ("max_tokens", 800), ("stop", Json.arr <| stopTokens |>.map Json.str)
  ]
  let data := dataJs.pretty
  trace[Translate.info] "GPT query: {data}"
  let out ←  IO.Process.output {
        cmd:= "curl",
        args:= #["https://api.openai.com/v1/chat/completions",
        "-X", "POST",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  trace[Translate.info] "OpenAI response: {out.stdout} (stderr: {out.stderr})"
  return Lean.Json.parse out.stdout |>.toOption.get!

def azureQuery(messages: Json)(n: Nat := 1)
  (temp : JsonNumber := 0.2)
  (stopTokens: Array String :=  #[":=", "-/"])(model: String)
  (deployment: String := "leanaide-gpt4") : CoreM Json := do
  let key? ← azureKey
  let key :=
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj [("model", model), ("messages", messages)
  , ("temperature", Json.num temp), ("n", n), ("max_tokens", 800),
  ("top_p", Json.num 0.95), ("stop", Json.arr <| stopTokens |>.map Json.str), ("frequency_penalty", 0), ("presence_penalty", 0)
  ]
  let data := dataJs.pretty
  trace[Translate.info] "OpenAI query: {data}"
  let out ←  IO.Process.output {
        cmd:= "curl",
        args:= #[← azureURL deployment,
        "-X", "POST",
        "-H", "Content-Type: application/json",
        "-H", "api-key: " ++ key,
        "--data", data]}
  trace[Translate.info] "Azure OpenAI response: {out.stdout} (stderr: {out.stderr})"
  return Lean.Json.parse out.stdout |>.toOption.get!

def genericQuery(url: String)(messages: Json)(n: Nat := 1)
  (temp : JsonNumber := 0.2)
  (stopTokens: Array String :=  #[":=", "-/"])(model: String) : CoreM Json := do
  let dataJs := Json.mkObj [("model", model), ("messages", messages)
  , ("temperature", Json.num temp), ("n", n), ("max_tokens", 800),
  ("top_p", Json.num 0.95), ("stop", Json.arr <| stopTokens |>.map Json.str), ("frequency_penalty", 0), ("presence_penalty", 0)
  ]
  let data := dataJs.pretty
  trace[Translate.info] "Model query: {data}"
  IO.eprintln s!"Querying {url} at {← IO.monoMsNow }"
  let start ← IO.monoMsNow
  let out ←  IO.Process.output {
        cmd:= "curl",
        args:= #[url++"/v1/chat/completions",
        "-X", "POST",
        "-H", "Content-Type: application/json",
        "--data", data]}
  trace[Translate.info] "Model response: {out.stdout} (stderr: {out.stderr})"
  IO.eprintln s!"Received response from {url} at {← IO.monoMsNow }; time taken: {(← IO.monoMsNow) - start}"
  return Lean.Json.parse out.stdout |>.toOption.get!
