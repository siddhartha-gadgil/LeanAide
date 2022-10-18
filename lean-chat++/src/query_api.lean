import tactic 
import prompting 


meta def get_key : io string := do
  o <- io.env.get "OPENAI_API_KEY",
  match o with 
  | some k := return k
  | none := return "dummy"
end 

section CompletionRequest


meta structure CompletionRequest : Type :=
(prompt: string)
(model: string := "code-davinci-002")
(temperature : int := 0.2)
(max_tokens : int := 150)
(stop : option string := ":=")

meta def test_completion_request : CompletionRequest := 
{
  prompt := example_prompt, 
  stop := none
}

meta def to_json : CompletionRequest → json :=
λ x, 
let pre_kvs : list (string × option json) := [
  ("prompt", json.of_string x.prompt), 
  ("model", json.of_string x.model), 
  ("temperature", json.of_int x.temperature), 
  ("max_tokens", json.of_int x.max_tokens), 
  ("stop", json.of_string <$> x.stop)
] in
json.object $ pre_kvs.filter_map (λ ⟨k,mv⟩, prod.mk k <$> mv)

/- 
Input: output of `to_json`. 
Output: `json` returned by openai api 
-/
meta def cmd_of_json : json → io io.process.spawn_args :=
λ request_json, 
do api_key ← get_key,  
return {
  cmd := "curl", 
  args := [
    "--silent",
    "https://api.openai.com/v1/completions", 
    "-H", "Content-Type: application/json", 
    "-H", "Authorization: Bearer " ++ api_key, 
    "-d", json.unparse request_json 
  ]
}

meta def get_completion_of_request : CompletionRequest → io string :=
λ request, do {
let request_json := to_json request, 
proc_cmds ← cmd_of_json request_json, 
io.cmd proc_cmds 
}

/-
run_cmd (do
  s <- tactic.unsafe_run_io (do 
    k ← get_key, 
    r <- get_completion_of_request test_completion_request,
    pure r
  ),
  tactic.trace s,
  pure ()
)
-/
end CompletionRequest 

