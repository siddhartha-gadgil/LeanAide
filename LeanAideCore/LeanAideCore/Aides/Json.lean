import Lean

open Lean Json

namespace Lean.Json

def parseArrIO (s : String) : IO <| Array Json := do
  IO.ofExcept $ Json.parse s >>= Json.getArr?

def parseFile (path : System.FilePath) : IO <| Array Json :=
  IO.FS.readFile path >>= Json.parseArrIO

instance : GetElem Json String Json (λ j k => Except.toBool <| j.getObjVal? k) where
  getElem := λ j key h =>
    match j.getObjVal? key, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

instance : GetElem Json Nat Json (λ j n => Except.toBool <| j.getArrVal? n) where
  getElem := λ j n h =>
    match j.getArrVal? n, h with
      | .ok j, _ => j
      | .error _, h => by simp [Except.toBool] at h

def getStr! (j : Json) : String :=
  j.getStr?.toOption.get!

/--
Get a key-value pair from a JSON object which is a single key-value pair.
-/
def getKV? (js : Json) : Option (String × Json) :=
  match js with
  | Json.obj m =>
    match m.toArray with
    | #[⟨k, v⟩] => some (k, v)
    | _ => none
  | _ => none

/--
Get a key-value pair from a JSON object which is a single key-value pair or has a field "type".
-/
def getKVorType? (js : Json) : Option (String × Json) :=
  match js with
  | Json.obj m =>
    match m.toArray with
    | #[⟨"type", .str key⟩] =>
        (key, json% {})
    | #[⟨k, v⟩] =>
      some (k, v)
    | jsArr =>
      let keys := jsArr.map (fun ⟨k, _⟩ => k)
      let keyVals := jsArr.map (fun ⟨k, v⟩ => (k, v))
      if keys.contains "type" then
        let purged := jsArr.filter (fun ⟨k, _⟩ => k != "type")
        let purged : Array (String × Json) :=
          purged.map fun ⟨k, v⟩ => (k, v)
        let typeVal? := keyVals.findSome? (fun (k, v) => if k == "type" then some v else none)
        match typeVal? with
          | some typeVal =>
            let type? := typeVal.getStr?.toOption
            type?.map fun type =>
              (type, Json.mkObj purged.toList)
          | none => none
      else
        none
  | _ => none

partial def patch (js diff : Json) : Json :=
  match js, diff with
  | Json.obj kvs₁, Json.obj kvs₂ =>
    match kvs₁.toArray, kvs₂.toArray with
    | #[⟨k₁, v₁⟩], #[⟨k₂, v₂⟩] => -- single key-value pair; expected to be inductive type
      if k₁ == k₂ then
        let v := patch v₁ v₂
        Json.mkObj [(k₁, v)]
      else
        diff
    | _, _ =>
      let keys₁ := kvs₁.toArray.map (fun ⟨k, _⟩ => k)
      let updated := kvs₁.toArray.map fun ⟨k, v₁⟩ =>
        match kvs₂.find compare k with
        | some v₂ =>
          let v := patch v₁ v₂
          (k, v)
        | none => (k, v₁)
      let newPairs :=
        kvs₂.toArray.filter (fun ⟨k, _⟩ => !keys₁.contains k) |>.map fun ⟨k, v⟩ => (k, v)
      Json.mkObj (updated ++ newPairs).toList
  | _, Json.obj kvs₂ =>
    if kvs₂.toArray.isEmpty then
      js
    else
      diff
  | _, _ => diff

partial def getPatch? (js₁ js₂ : Json) : Option Json :=
  match js₁, js₂ with
  | Json.obj kvs₁, Json.obj kvs₂ =>
    match kvs₁.toArray, kvs₂.toArray with
    | #[⟨k₁, v₁⟩], #[⟨k₂, v₂⟩] => -- single key-value pair; expected to be inductive type
      if k₁ == k₂ then
        let vDiff := getPatch? v₁ v₂
        match vDiff with
        | some vDiff => some <| Json.mkObj [(k₁, vDiff)]
        | none => none
      else
        some js₂
    | _, _ =>
      let keys₁ := kvs₁.toArray.map (fun ⟨k, _⟩ => k)
      let updated := kvs₁.toArray.foldl (init := #[]) fun acc ⟨k, v₁⟩ =>
        match kvs₂.find compare k with
        | some v₂ =>
          let vDiff := getPatch? v₁ v₂
          match vDiff with
          | some vDiff => acc.push (k, vDiff)
          | none => acc
        | none => acc
      let newPairs :=
        kvs₂.toArray.filter (fun ⟨k, _⟩ => !keys₁.contains k) |>.map fun ⟨k, v⟩ => (k, v)
      let changes := (updated ++ newPairs).toList
      if changes.isEmpty then
        none
      else
        some <| Json.mkObj changes
  | _, _ =>
    if js₁ != js₂ then
      some js₂
    else
      none

end Lean.Json


namespace LeanAide

def jsonLines [ToJson α] (jsl : Array α) : String :=
  let lines := jsl.map (fun j => Json.compress <| toJson j)
  lines.foldl (fun acc l => acc ++ l ++ "\n") ""

partial def readableJson (js: Json) : Json :=
   match js with
  | Json.obj m =>
   match m.toArray with
   | jsArr =>
     let keyVals := jsArr.map (fun ⟨k, v⟩ => (k, v))
     let purged := jsArr.filter (fun ⟨k, _⟩ => k != "type")
     let purged := purged.map fun ⟨k, v⟩ => (k, v)
     let typeVal? := keyVals.findSome? (fun (k, v) => if k == "type" then some v else none)
     match typeVal? with
     | some typeVal =>
       let type? := typeVal.getStr?.toOption
       match type? with
       | some type =>
          Json.mkObj [(type, readableJson (Json.mkObj purged.toList))]
       | none => js
     | none =>
       let keyValsModified := keyVals.map (fun (k,v) => (k, readableJson v))
       Json.mkObj keyValsModified.toList
  | Json.arr m => (m.map (fun x => readableJson x)).toJson
  | _ => js


instance : Repr Json where
  reprPrec js n := reprPrec js.pretty n

open Lean Elab Term
def jsonToExpr (js : Json) : TermElabM Expr := do
  let jsStr := js.pretty
  let .ok stx := Lean.Parser.runParserCategory (← getEnv) `term jsStr | throwError "jsonToExpr: failed to parse {jsStr}"
  elabTerm stx (mkConst ``Json)
