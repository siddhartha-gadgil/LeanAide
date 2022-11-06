import utils

/-!

Scripts to query
- The OpenAI Codex model for translations
- The `LeanAide` server to retrieve `mathlib` theorems similar to a given one.

-/


/-- Fetches the OpenAI key from the environment to query OpenAI Codex for translation. -/
meta def get_openai_key : io string := do
  some key ← io.env.get "OPENAI_API_KEY" | io.fail 
      "`OPENAI_API_KEY` environment variable not found.
        This is required for the statement translation tool.
        Set it using the bash command `export OPENAI_API_KEY=<key>`,
        where `<key>` is your personal OpenAI key.",
  return key

/-- Fetch the IP address of the `LeanAide` server. -/
meta def lean_aide_ip : io string := do
  some ip ← io.env.get "LEANAIDE_IP" | pure "localhost:5000",
  return ip


section completion_request

/-! The code in this section is modified from `Lean Chat`. -/

/-- A structure for storing data for querying Codex. -/
structure completion_request : Type :=
  (prompt : string)
  (model : string := "code-davinci-002")
  (temperature : nat := 8) -- the actual temperature times `10`
  (n : nat := 1)
  (max_tokens : int := 150)
  (stop : list string := [":=", "/-", "-/"])
  
instance completion_request.from_str : has_coe string completion_request :=
  { coe := λ s, {prompt := s} }

-- An example completion request
def test_completion_request : completion_request := 
{ prompt := "For every epsilon greater than zero, ",  stop := ["."] }

/-- Export a `completion_request` to `json` format. -/
meta def completion_request.to_json : completion_request → json
 | ⟨prompt, model, temperature, n, max_tokens, stop⟩ :=
    json.object [
    ("prompt", json.of_string prompt), 
    ("model", json.of_string model), 
    ("temperature", json.of_float $ native.float.div temperature 10), 
    ("n", json.of_int n),
    ("max_tokens", json.of_int max_tokens), 
    ("stop", json.array $ json.of_string <$> stop)
    ]

/-- Query OpenAI Codex for completions. -/
meta def completion_request.query_codex (request : completion_request) : io json := do
    api_key ← get_openai_key,
    out ← io.cmd {cmd := "curl", args := [
      "--silent",
      "https://api.openai.com/v1/completions",
      "-X", "POST",
      "-H", "Content-Type: application/json",
      "-H", "Authorization: Bearer " ++ api_key,
      "--data", json.unparse request.to_json
    ]},
    some codex_completion ← pure (json.parse out) | io.fail "failed to parse json",
    return codex_completion

/-- Get the list of Codex completions as strings. -/
meta def completion_request.get_codex_completions (request : completion_request) : io (list string) := do
  codex_out ← completion_request.query_codex request,
  io.of_except $ do
    choices ← codex_out.lookup_as "choices" json.as_array,
    choices.mmap $ λ choice, choice.lookup_as "text" json.as_string

meta def test_completions : io unit := do
  s ← test_completion_request.get_codex_completions,
  io.print s

-- #eval test_completions

end completion_request


section similarity_prompts

/-- Query the `LeanAide` server to get `mathlib` theorems similar to a given statement. -/
meta def get_similarity_prompts (s : string) (n : nat := 15) : io (list json) := do
  let data := json.object [
    ("filename", "data/safe_prompts.json"),
    ("field", "doc_string"),
    ("doc_string", s),
    ("n", n),
    ("model_name", "all-mpnet-base-v2")
    ],
  ip ← lean_aide_ip,
  out ← io.cmd {cmd := "curl", args := [
    "-X", "POST",
    "-H", "Content-Type: application/json",
    "--data", json.unparse data,
    sformat!"{ip}/nearest_prompts"
  ]},
  io.of_except $
    let sim_prompts := except.of_option (json.parse out) "failed to parse json" in
      sim_prompts >>= json.as_array 


meta def test_similarity_prompts : io unit := do
  let stmt := "Every prime number is either `2` or odd.",
  prompts ← get_similarity_prompts stmt 5,
  io.print prompts

end similarity_prompts