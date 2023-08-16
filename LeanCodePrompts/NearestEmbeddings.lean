import Lean
import LeanAide.Aides
import Mathlib
open Std Lean


def insertByMemo (l: Array <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α) (cx? : Option Float := none) : Array <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx := match cx? with
    | some c => c
    | none => cost x
    match l.findIdx? (fun (_, cy) => cx < cy) with
    | some idx => 
      l.insertAt idx (x, cx) |>.shrink (k + 1)
    | none => l.push (x, cx) |>.shrink (k + 1)


def distL2Sq (v₁ : FloatArray) (v₂ : Array Float) : Float :=
  let squaredDiffs : Array Float := 
    (v₁.data.zip v₂).map (fun (x, y) => (x - y) * (x - y)) 
  squaredDiffs.foldl (Float.add) 0.0


def nearestDocsToDocEmbedding (data : Array <| (String × String) ×  FloatArray) 
  (embedding : Array Float) (k : Nat)
  (dist: FloatArray → Array Float → Float := distL2Sq) : List (String × String) :=
  let pairs : Array <| ((String × String) × FloatArray) × Float := 
    data.foldl (fun (acc : Array <| ((String × String) × FloatArray) × Float) 
      (pair : (String × String) × FloatArray) => 
      insertByMemo acc (fun (_, flArr) ↦ dist flArr embedding) k pair) #[]
  (pairs.map <| fun ((doc, _), _) => doc).toList


def nearestDocsToDocFullEmbedding (data : Array <| (String × String × Bool) ×  FloatArray) 
  (embedding : Array Float) (k : Nat)
  (dist: FloatArray → Array Float → Float := distL2Sq)(penalty : Float) : List (String × String × Bool) :=
  let tuples : Array <| ((String × String × Bool) × FloatArray) × Float := 
    data.foldl (fun (acc : Array <| ((String × String × Bool) × FloatArray) × Float) 
      (tuple : (String × String × Bool) × FloatArray) => 
      insertByMemo acc (fun ((_, _, isProp), flArr) ↦ 
        let d := dist flArr embedding
        if isProp then d else d * penalty) k tuple) #[]
  (tuples.map <| fun (((doc, thm, isProp), _), _) => (doc, thm, isProp)).toList


def embedQuery (doc: String) : IO <| Except String Json := do
  let key? ← openAIKey
  let key := 
    match key? with
    | some k => k
    | none => panic! "OPENAI_API_KEY not set"
  let dataJs := Json.mkObj 
      [("input", doc), ("model", "text-embedding-ada-002")]
  let data := dataJs.pretty
  let out ←  IO.Process.output {
        cmd:= "curl", 
        args:= #["https://api.openai.com/v1/embeddings",
        "-H", "Authorization: Bearer " ++ key,
        "-H", "Content-Type: application/json",
        "--data", data]}
  return Lean.Json.parse out.stdout 

-- #eval embedQuery "There are infinitely many odd numbers"


def nearestDocsToDocThms (data: Array ((String × String) × FloatArray))(doc: String)(k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq) : IO (List (String × String)) := do
  let queryRes? ← embedQuery doc
  -- IO.println "query complete"
  match queryRes? with
  | Except.ok queryRes =>
    -- IO.println s!"query result obtained"
    let queryData? := queryRes.getObjVal? "data"
    match queryData? with
    | Except.error error => 
        IO.println s!"no data in query result: {error}"
        panic s!"no data in query result: {error}"
    | Except.ok queryDataArr =>
      -- IO.println s!"data in query result obtained"
      let queryData := queryDataArr.getArrVal? 0 |>.toOption.get!
      match queryData.getObjValAs? (Array Float) "embedding" with
      | Except.ok queryEmbedding => 
        -- IO.println s!"embedding in query result obtained"
        let res := nearestDocsToDocEmbedding data queryEmbedding k dist
        -- IO.println s!"getNearestDocsToEmbedding complete: {res}"
        pure res
      | Except.error error =>
        panic s!"no embedding in query result: {error} in {queryData}"
  | Except.error err => panic! s!"error querying openai: {err}"

def nearestDocsToDocFull (data: Array ((String × String × Bool) × FloatArray))
    (doc: String)(k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq)
    (penalty: Float) : IO (List (String × String × Bool)) := do
  let queryRes? ← embedQuery doc
  -- IO.println "query complete"
  match queryRes? with
  | Except.ok queryRes =>
    -- IO.println s!"query result obtained"
    let queryData? := queryRes.getObjVal? "data"
    match queryData? with
    | Except.error error => 
        IO.println s!"no data in query result: {error}"
        panic s!"no data in query result: {error}"
    | Except.ok queryDataArr =>
      -- IO.println s!"data in query result obtained"
      let queryData := queryDataArr.getArrVal? 0 |>.toOption.get!
      match queryData.getObjValAs? (Array Float) "embedding" with
      | Except.ok queryEmbedding => 
        -- IO.println s!"embedding in query result obtained"
        let res := 
          nearestDocsToDocFullEmbedding data queryEmbedding k dist penalty
        -- IO.println s!"getNearestDocsToEmbedding complete: {res}"
        pure res
      | Except.error error =>
        panic s!"no embedding in query result: {error} in {queryData}"
  | Except.error err => panic! s!"error querying openai: {err}"

