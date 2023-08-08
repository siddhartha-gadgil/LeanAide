import nearest_embeddings

def test (k : ℕ) (stmts : Array String) : IO (Array Lean.Json) := do
  let stdioCfg ← IO.Process.spawn {
    stdin := .piped,
    stdout := .piped,
    stderr := .piped,
    cmd := "./build/bin/nearest_embeddings",
    args := #[toString k],
    cwd := "."
  } 
  let mut outputs : Array Lean.Json := #[]
  for stmt in stmts do
    IO.println stmt
    stdioCfg.stdin.putStrLn stmt
    let out ← stdioCfg.stdout.getLine
    IO.println out
    let json ← IO.ofExcept <| Lean.Json.parse out
    outputs := outputs.push json
  stdioCfg.kill
  return outputs

-- #eval test 5 #["hello", "world"]