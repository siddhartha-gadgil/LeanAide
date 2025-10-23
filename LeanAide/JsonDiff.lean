import Lean
import Mathlib

open Lean Json
namespace LeanAide

inductive JsonDiff where
  | message : String → JsonDiff
  | existsKey1only : String → JsonDiff
  | existsKey2only : String → JsonDiff
  | atKey : String → JsonDiff  → JsonDiff
  | atIndex : Nat → JsonDiff → JsonDiff
  deriving Repr

partial def jsonDiff : Json → Json → List JsonDiff
| arr a, arr b => do
  let la := a.toList
  let lb := b.toList
  let lena := la.length
  let lenb := lb.length
  let mut error : List JsonDiff := []
  for i in [0:max lena lenb] do
      match la[i]?,lb[i]? with
      | none, none => []
      | some _, none => error := error.append [JsonDiff.atIndex i (.message "second list does not have element")]
      | none, some _ => error := error.append [JsonDiff.atIndex i (.message "first list does not have element")]
      | some val1, some val2 => error := error.append ((jsonDiff val1 val2).map (fun d ↦ JsonDiff.atIndex i d))
  error

| obj a, obj b => do
  let oa := a.toArray.toList
  let ob := b.toArray.toList
  let mut error :List JsonDiff := []
  for ⟨k,v⟩ in oa do
      let val? := b.find compare k
      match val? with
      | none => error := error.append [JsonDiff.existsKey1only k]
      | some val => error := error.append ((jsonDiff v val).map (fun d ↦ JsonDiff.atKey k d))
  for ⟨k,_⟩ in ob do
    let val? := a.find compare k
    match val? with
    | none => error := error.append [JsonDiff.existsKey2only k]
    | some _ => continue
  error
| num a, num b => if a == b then [] else [.message s!"one has number {a} and another has number {b}"]
| .bool a, .bool b => if a == b then [] else [.message s!"one has boolean {a} and another has boolean {b}"]
| .str a, .str b => if a == b then [] else [.message s!"one has string {a} and another has string {b}"]
| .null, .null => []
| _,_ => [.message "terms have different types"]
