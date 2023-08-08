import Lean
import Lean.Meta
import Lean.Parser
import LeanAide.Aides
import LeanAide.IP
import Mathlib

open Std Lean

initialize embeddingsRef  : IO.Ref (Array <| String ×  FloatArray)
        ← IO.mkRef #[]

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
  withUnpickle  "rawdata/mathlib4-thms-embeddings.olean" <| fun (data: Array <| String ×  FloatArray) => pure data.size

-- #eval loadEmbeddingsTest

-- Avoiding recomputing distances
def insertByMemo (l: List <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α) (cx? : Option Float := none) : List <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx := match cx? with
    | some c => c
    | none => cost x
    match l with
    | [] => [(x, cx)]
    | (y, cy) :: ys =>
      if cx < cy then
        (x, cx) :: l |>.take k
      else
        (y, cy) :: insertByMemo ys cost k x (some cx)

def insertByMemo' (l: Array <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α) (cx? : Option Float := none) : Array <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx := match cx? with
    | some c => c
    | none => cost x
    match l.findIdx? (fun (_, cy) => cx < cy) with
    | some idx => 
      l.insertAt idx (x, cx) |>.shrink k
    | none => l.push (x, cx) |>.shrink k


#check List.findIdx?
#check Array.findIdx?

#eval Array.insertAt! #[1, 3, 4] 1 2 |>.shrink 7
#check Array.pop

def distL2Sq (v₁ : FloatArray) (v₂ : Array Float) : Float :=
  let squaredDiffs : Array Float := 
    (v₁.data.zip v₂).map (fun (x, y) => (x - y) * (x - y)) 
  squaredDiffs.foldl (Float.add) 0.0

def nearestDocsToEmbedding (data : Array <| String ×  FloatArray) 
  (embedding : Array Float) (k : Nat)
  (dist: FloatArray → Array Float → Float := distL2Sq) : List String :=
  let pairs : Array <| (String × FloatArray) × Float := 
    data.foldl (fun (acc : Array <| (String × FloatArray) × Float) 
      (pair : String × FloatArray) => 
      insertByMemo' acc (fun (_, flArr) ↦ dist flArr embedding) k pair) #[]
  (pairs.map <| fun ((doc, _), _) => doc).toList

unsafe def loadEmbeddings: IO Unit := do
    if (← embeddingsRef.get).isEmpty then
      let (data, _) ← unpickle (Array <| String ×  FloatArray)  "rawdata/mathlib4-thms-embeddings.olean" 
      embeddingsRef.set data
    return ()

unsafe def getNearestDocsToEmbedding (embedding : Array Float) (k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq) : IO (List String) := do
    loadEmbeddings
    let data ← embeddingsRef.get 
    let res := nearestDocsToEmbedding data embedding k dist
    return res

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

unsafe def nearestDocsToDoc (doc: String)(k : Nat)(dist: FloatArray → Array Float → Float := distL2Sq) : IO (List String) := do
  -- IO.println s!"querying openai for embedding of {doc}"
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
        let res ← getNearestDocsToEmbedding queryEmbedding k dist
        -- IO.println s!"getNearestDocsToEmbedding complete: {res}"
        pure res
      | Except.error error =>
        panic s!"no embedding in query result: {error} in {queryData}"
  | Except.error err => panic! s!"error querying openai: {err}"

-- #eval nearestDocsToDoc "There are infinitely many odd numbers" 3

