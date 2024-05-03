import Lean
import Mathlib.Tactic
import LeanAide.Config
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

def nearestEmbeddingsFullCmd : IO.Process.SpawnArgs := {
  cmd := "lake",
  args := #["exe", "nearest_embeddings_full"],
  cwd := ".",
  stdin := .piped,
  stdout := .piped,
  stderr := .piped
}

initialize nearestEmbeddingsFullProcessRef : IO.Ref
  (Option <| IO.Process.Child nearestEmbeddingsFullCmd.toStdioConfig) ← (do
    let child ← IO.Process.spawn nearestEmbeddingsFullCmd
    IO.mkRef <| some child)

def getNearestEmbeddingsFullProcess : IO (IO.Process.Child nearestEmbeddingsFullCmd.toStdioConfig) := do
  match ← nearestEmbeddingsFullProcessRef.get with
    | some child => return child
    | none =>
      let child ← IO.Process.spawn nearestEmbeddingsFullCmd
      nearestEmbeddingsFullProcessRef.set child
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

def getNearestEmbeddings (query : String)(numSim : Nat) : IO String := do
  let child ← getNearestEmbeddingsProcess
  let stdin := child.stdin
  let jsQuery := Json.mkObj [("n" , numSim), ("docString", query)]
  stdin.putStrLn jsQuery.compress
  stdin.flush
  child.stdout.getLine


def getNearestEmbeddingsFull
  (query : String)(numSim: Nat)(penalty: Float)
  (descField: String := "docString") : IO String := do
  logTimed "getting process"
  let child ← getNearestEmbeddingsFullProcess
  let stdin := child.stdin
  let p : JsonNumber := match JsonNumber.fromFloat? penalty with
  | Sum.inl _ => 2.0
  | Sum.inr n => n
  let jsQuery := Json.mkObj
    [("n" , numSim), ("docString", query), ("descField", descField),
    ("penalty", Json.num p)]
  stdin.putStrLn jsQuery.compress
  stdin.flush
  child.stdout.getLine

def pingEmbedding : IO Bool := do
  let proc? ← nearestEmbeddingsFullProcessRef.get
  return proc?.isSome
