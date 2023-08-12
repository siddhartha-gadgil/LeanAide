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


@[instance] axiom IO.FS.Handle.instInhabited : Inhabited IO.FS.Handle

noncomputable instance (stdio : IO.Process.Stdio) : Inhabited stdio.toHandleType :=
  match stdio with
    | .inherit | .null => inferInstanceAs <| Inhabited Unit
    | .piped => inferInstanceAs <| Inhabited IO.FS.Handle

noncomputable instance : Inhabited (IO.Process.Child nearestEmbeddingsCmd.toStdioConfig) where
  default := ⟨default, default, default⟩

initialize nearestEmbeddingsProcessRef : IO.Ref (IO.Process.Child nearestEmbeddingsCmd.toStdioConfig) ← do
  let child ← IO.Process.spawn nearestEmbeddingsCmd
  IO.mkRef child


def queryNearestEmbeddingsProcess (queries : Array String) : IO (Array String) := do
  let child ← nearestEmbeddingsProcessRef.get 
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