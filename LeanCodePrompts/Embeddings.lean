import Lean
import Lean.Meta
import Lean.Parser
import LeanAide.Aides
import LeanAide.IP
import Mathlib

open Std Lean

def readEmbeddings : IO <| Std.HashMap String FloatArray :=  do
  let mut count := 0
  let blob ← IO.FS.readFile "rawdata/mathlib4-thms-embeddings.json"
  let json := Json.parse blob |>.toOption.get!
  let jsonArr := json.getArr? |>.toOption.get!
  let mut accum := Std.HashMap.empty
  for jsLine in jsonArr do
    let doc := 
      match jsLine.getObjValAs? String "docString" with
      | Except.ok doc => doc
      | Except.error err => panic! s!"error reading docString: {err}" 
    let embedding':= 
      match jsLine.getObjValAs? (List Float) "embedding" with
      | Except.ok embedding => embedding
      | Except.error err => panic! s!"error reading embedding: {err}" 
    let embedding := embedding'.toFloatArray
    accum := accum.insert doc embedding
    count := count + 1
    if count % 1000 == 0 then    
      IO.println s!"read {count} embeddings"
  return accum

def readEmbeddingsArray : IO <| Array <| String ×  FloatArray :=  do
  let mut count := 0
  let blob ← IO.FS.readFile "rawdata/mathlib4-thms-embeddings.json"
  let json := Json.parse blob |>.toOption.get!
  let jsonArr := json.getArr? |>.toOption.get!
  let mut accum := #[]
  let mut docs : Array String := #[]
  for jsLine in jsonArr do
    let doc := 
      match jsLine.getObjValAs? String "docString" with
      | Except.ok doc => doc
      | Except.error err => panic! s!"error reading docString: {err}" 
    let embedding':= 
      match jsLine.getObjValAs? (List Float) "embedding" with
      | Except.ok embedding => embedding
      | Except.error err => panic! s!"error reading embedding: {err}" 
    let embedding := embedding'.toFloatArray
    unless docs.contains doc do
      docs := docs.push doc
      accum := accum.push (doc, embedding)
    count := count + 1
    if count % 1000 == 0 then    
      IO.println s!"read {count} embeddings"
  return accum

unsafe def loadEmbeddingsTest : IO Nat := 
  withUnpickle  "rawdata/mathlib4-thms-embeddings.json.olean" <| fun (data: Array <| String ×  FloatArray) => pure data.size

-- #eval loadEmbeddingsTest

def insertBy (l: List α)(cost : α → Float)(sizeBound: Nat)(x : α) : List α :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    match l with
    | [] => [x]
    | y :: ys =>
      if cost x < cost y then
        x :: l
      else
        y :: insertBy ys cost k x

def distL2Sq (v₁ : FloatArray) (v₂ : Array Float) : Float :=
  let squaredDiffs : Array Float := 
    (v₁.data.zip v₂).map (fun (x, y) => (x - y) * (x - y)) 
  squaredDiffs.foldl (Float.add) 0.0

def nearestDocsToEmbedding (data : Array <| String ×  FloatArray) 
  (embedding : Array Float) (k : Nat)
  (dist: FloatArray → Array Float → Float := distL2Sq) : List String :=
  let pairs : List <| String × FloatArray := 
    data.foldl (fun (acc : List <| String × FloatArray) (pair : String × FloatArray) => 
      insertBy acc (fun (_, flArr) ↦ dist flArr embedding) k pair) []
  pairs.map <| fun (doc, _) => doc

unsafe def getNearestDocsToEmbedding (embedding : Array Float) (k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq) : IO (List String) := do
  withUnpickle  "rawdata/mathlib4-thms-embeddings.json.olean" <| fun (data: Array <| String ×  FloatArray) =>
  pure <| nearestDocsToEmbedding data embedding k dist

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

unsafe def nearestDocsToDoc (doc: String)(k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq) : CoreM (List String) := do
  let queryRes? ← embedQuery doc
  match queryRes? with
  | Except.ok queryRes =>
    let queryData? := queryRes.getObjVal? "data"
    match queryData? with
    | Except.error error => 
        throwError s!"no data in query result: {error}"
    | Except.ok queryDataArr =>
      let queryData := queryDataArr.getArrVal? 0 |>.toOption.get!
      match queryData.getObjValAs? (Array Float) "embedding" with
      | Except.ok queryEmbedding => 
        getNearestDocsToEmbedding queryEmbedding k dist
      | Except.error error =>
        throwError s!"no embedding in query result: {error} in {queryData}"
  | Except.error err => panic! s!"error querying openai: {err}"

-- #eval nearestDocsToDoc "There are infinitely many odd numbers" 10

