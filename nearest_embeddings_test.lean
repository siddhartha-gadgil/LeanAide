import Lean
open Lean

def nearestEmbeddingsCmd : IO.Process.SpawnArgs := {
  cmd := "./build/bin/nearest_embeddings",
  args := #[],
  cwd := "."
}

def statements := #[
  "There are infinitely many odd numbers",
  "Every vector space of dimension 2 is finite dimensional",
  "Every subgroup of an Abelian group is Abelian"]

def queryProcess (args : IO.Process.SpawnArgs) (queries : Array String) : IO (Array String) := do
  IO.println "Starting ..."
  let child ← IO.Process.spawn { args with
    stdin := .piped,
    stdout := .piped,
    stderr := .piped }
  let (stdin, child) ← child.takeStdin
  let mut outputs : Array String := #[]
  for query in queries do
    stdin.putStrLn query
    stdin.flush
    let out ← child.stdout.getLine
    outputs := outputs.push out
  return outputs

def main : IO Unit := timeit "nearest_embeddings_test" do
  let results ← queryProcess nearestEmbeddingsCmd statements
  IO.println results