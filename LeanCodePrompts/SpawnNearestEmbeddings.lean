import Lean
import Mathlib.Tactic
import LeanAide.Config
open Lean

def getNearestEmbeddingsFull
  (query : String)(numSim: Nat)(penalty: Float)
  (descField: String := "docString") : IO String := do
  let exePath := System.mkFilePath [".", ".lake", "build", "bin", "nearest_embeddings"]
  if !(← exePath.pathExists) then
    let _ ←  IO.Process.run {cmd := "lake", args := #["build",  "nearest_embeddings"], cwd := "."}
  let cmd := exePath.toString
  -- let child ← getNearestEmbeddingsFullProcess
  -- let stdin := child.stdin
  let p : JsonNumber := match JsonNumber.fromFloat? penalty with
  | Sum.inl _ => 2.0
  | Sum.inr n => n
  let jsQuery := Json.mkObj
    [("n" , numSim), ("docString", query), ("descField", descField),
    ("penalty", Json.num p)]
  logTimed "sending query"
  let inp ← IO.Process.run {cmd := cmd, args := #[jsQuery.compress]}
  logTimed "got response"
  return inp
