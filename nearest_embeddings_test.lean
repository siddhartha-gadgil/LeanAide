import Lean
open Lean

def statements := #["hello", "world"]

def main (args : List String) : IO Unit := do
  IO.println "Loading ..."
  let _stdioCfg ← IO.Process.spawn {
    stdin := .piped,
    stdout := .piped,
    stderr := .piped,
    cmd := "./build/bin/nearest_embeddings",
    args := args.toArray,
    cwd := "."
  }
  IO.println "Running process ..."
  let mut outputs : Array Lean.Json := #[]
  for stmt in statements do
    IO.println stmt
    let (stdin, stdioCfg) ← _stdioCfg.takeStdin
    stdin.putStrLn stmt
    IO.println s!"Printed {stmt} to process `stdin` ..."
    let stdout ← IO.asTask stdioCfg.stdout.getLine .dedicated
    IO.println "Fetching `stdout` ..."
    let stderr ← stdioCfg.stderr.readToEnd
    let exitCode ← stdioCfg.wait
    let stdout ← IO.ofExcept stdout.get
    IO.println s!"Output {stdout} from `stdout` retrieved ..."
    let json ← IO.ofExcept <| Lean.Json.parse stdout
    outputs := outputs.push json
  _stdioCfg.kill
  IO.println "Done. \n\n"
  IO.println outputs

def IO.Process.withStdin (args : SpawnArgs) (input : String) : IO Output := do
  let child₀ ← spawn { args with stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child₀.takeStdin
  stdin.putStr input
  stdin.flush
  let stdout ← IO.asTask child.stdout.readToEnd .dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdout.get
  pure { exitCode := exitCode, stdout := stdout, stderr := stderr }

#eval do -- works
  let out ← IO.Process.withStdin {cmd := "gp", args := #["-q"]} "(x + 1) * (x - 1)" 
  return out.stdout

#eval do -- loops
  let out ← IO.Process.withStdin {cmd := "./build/bin/nearest_embeddings", args := #["2"]} "hello" 
  return out.stdout