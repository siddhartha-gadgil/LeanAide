import Lean
import Mathlib.Tactic
open Lean

def nearestEmbeddingsCmd : IO.Process.SpawnArgs := {
  cmd := "lake",
  args := #["exe", "nearest_embeddings"],
  cwd := ".",
  stdin := .piped,
  stdout := .piped,
  stderr := .piped
}

initialize nearestEmbeddingsProcessRef : IO.Ref 
  (Option <| IO.Process.Child nearestEmbeddingsCmd.toStdioConfig) ← IO.mkRef none

def getNearestEmbeddingsProcess : IO (IO.Process.Child nearestEmbeddingsCmd.toStdioConfig) := do
  match ← nearestEmbeddingsProcessRef.get with
    | some child => return child
    | none =>
      let child ← IO.Process.spawn nearestEmbeddingsCmd
      nearestEmbeddingsProcessRef.set child
      return child

def queryNearestEmbeddingsProcess (queries : Array String) : IO (Array String) := do
  let child ← getNearestEmbeddingsProcess 
  let stdin := child.stdin
  let mut outputs : Array String := #[]
  for query in queries do
    stdin.putStrLn query
    stdin.flush
    let out ← child.stdout.getLine
    outputs := outputs.push out
  return outputs

def statements := #[
  "There are infinitely many odd numbers",
  "Every vector space of dimension 2 is finite dimensional",
  "Every subgroup of an Abelian group is Abelian"]

def main : IO Unit := timeit "nearest_embeddings_test" do
  let results ← queryNearestEmbeddingsProcess statements
  IO.println results