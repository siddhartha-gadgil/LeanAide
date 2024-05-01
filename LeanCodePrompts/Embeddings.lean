import Lean
import LeanAide.Aides
import Mathlib

open Std Lean

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

def readEmbeddingsDocsArray : IO <| Array <| (String × String) ×  FloatArray :=  do
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
    let thm :=
      match jsLine.getObjValAs? String "type" with
      | Except.ok thm => thm
      | Except.error err => panic! s!"error reading thmString: {err}"
    let embedding':=
      match jsLine.getObjValAs? (List Float) "embedding" with
      | Except.ok embedding => embedding
      | Except.error err => panic! s!"error reading embedding: {err}"
    let embedding := embedding'.toFloatArray
    unless docs.contains doc do
      docs := docs.push doc
      accum := accum.push ((doc, thm), embedding)
    count := count + 1
    if count % 1000 == 0 then
      IO.println s!"read {count} embeddings"
  return accum

def readEmbeddingsFullDocsArray (blob descField: String) : IO <| Array <| (String × String × Bool × String) ×  FloatArray :=  do
  let mut count := 0
  let json := Json.parse blob |>.toOption.get!
  let jsonArr := json.getArr? |>.toOption.get!
  let mut accum := #[]
  let mut docs : Array String := #[]
  for jsLine in jsonArr do
    let doc :=
      match jsLine.getObjValAs? String descField with
      | Except.ok doc => doc
      | Except.error err => panic! s!"error reading {descField}: {err}"
    let thm :=
      match jsLine.getObjValAs? String "type" with
      | Except.ok thm => thm
      | Except.error err => panic! s!"error reading thm: {err}"
    let isProp :=
      match jsLine.getObjValAs? Bool "isProp" with
      | Except.ok isProp => isProp
      | Except.error err => panic! s!"error reading isProp: {err}"
    let name :=
      match jsLine.getObjValAs? String "name" with
      | Except.ok thm => thm
      | Except.error err => panic! s!"error reading name: {err}"
    let embedding':=
      match jsLine.getObjValAs? (List Float) "embedding" with
      | Except.ok embedding => embedding
      | Except.error err => panic! s!"error reading embedding: {err}"
    let embedding := embedding'.toFloatArray
    unless docs.contains doc do
      docs := docs.push doc
      accum := accum.push ((doc, thm, isProp, name), embedding)
    count := count + 1
    if count % 1000 == 0 then
      IO.println s!"read {count} embeddings"
  return accum


unsafe def loadEmbeddingsTest : IO Nat :=
  withUnpickle  ".lake/build/lib/mathlib4-thms-embeddings.olean" <| fun (data: Array <| String ×  FloatArray) => pure data.size

unsafe def loadEmbeddingsDocsTest : IO Nat :=
  withUnpickle  ".lake/build/lib/mathlib4-doc-thms-embeddings.olean" <| fun (data: Array <| (String × String) ×  FloatArray) => pure data.size

unsafe def loadEmbeddingsFullDocsTest : IO Nat := do
  withUnpickle  (← picklePath "docString") <| fun (data: Array <| (String × String × Bool) ×  FloatArray) => pure data.size

-- #eval loadEmbeddingsFullDocsTest
