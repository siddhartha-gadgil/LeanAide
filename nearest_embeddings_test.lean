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