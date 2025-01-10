import Lean
import Mathlib.Tactic
import LeanAide.Config
import LeanCodePrompts.NearestEmbeddings
open Lean

def getNearestEmbeddingsExe
  (query : String)(numSim: Nat)(penalty: Float)
  (descField: String) : IO String := do
  let exePath := System.mkFilePath [".", ".lake", "build", "bin", "nearest_embeddings"]
  if !(← exePath.pathExists) then
    let _ ←  IO.Process.run {cmd := "lake", args := #["build",  "nearest_embeddings"], cwd := "."}
  let exePath ← reroutePath exePath
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

def getNearestEmbeddingsFull
  (query: String)(queryRes? : Except String Json)(numSim: Nat)(penalty: Float)
  (descField: String := "docString")
  (dataMap : EmbedMap := Std.HashMap.empty) : IO String := do
  match dataMap.get? descField with
  | none =>
    getNearestEmbeddingsExe query numSim penalty descField
  | some data =>
    logTimed s!"got data for {descField}"
    let embs ←
      nearestDocsToDocFromEmb data queryRes? numSim (penalty := penalty)
    let out :=
      Lean.Json.arr <|
        embs.toArray.map fun (doc, thm, isProp, name, d) =>
          Json.mkObj <| [
            ("docString", Json.str doc),
            ("type", Json.str thm),
            ("isProp", Json.bool isProp),
            ("name", Json.str name),
            ("distance", toJson d)
          ]
    return out.compress
