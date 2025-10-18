import Lean
import Mathlib

open Lean
open Json
namespace Json

inductive JsonDiff where
  | message : String → JsonDiff
  | existsKey1only : String → JsonDiff
  | existsKey2only : String → JsonDiff
  | atKey : String → JsonDiff  → JsonDiff
  | atIndex : Nat → JsonDiff → JsonDiff
  deriving Repr


partial def errorJson' : Json → Json → List JsonDiff
| arr a, arr b => do
  let la := a.toList
  let lb := b.toList
  let lena := la.length
  let lenb := lb.length
  let mut error : List JsonDiff := []
  for i in [0:max lena lenb] do
      match la[i]?,lb[i]? with
      | none, none => []
      | some _, none => error := error.append [JsonDiff.atIndex i (.message "second list does not have elements")]
      | none, some _ => error := error.append [JsonDiff.atIndex i (.message "first list does not have elements")]
      | some val1, some val2 => error := error.append ((errorJson' val1 val2).map (fun d ↦ JsonDiff.atIndex i d))
  error

| obj a, obj b => do
  let oa := a.toList
  let ob := b.toList
  let mut error :List JsonDiff := []
  for (k,v) in oa do
      let val := b.get? k
      match val with
      | none => error := error.append [JsonDiff.existsKey1only k]
      | some val => error := error.append ((errorJson' v val).map (fun d ↦ JsonDiff.atKey k d))
  for (k,_) in ob do
    if k ∉ a then
      error := error.append [JsonDiff.existsKey2only k]
  error
| num a, num b => if a == b then [] else [.message s!"one has number {a} and another has number {b}"]
| .bool a, .bool b => if a == b then [] else [.message s!"one has boolean {a} and another has boolean {b}"]
| .str a, .str b => if a == b then [] else [.message s!"one has string {a} and another has string {b}"]
| _,_ => [.message "terms have different types"]


def j1 := mkObj [("a", 1), ("b", Json.mkObj [("c", true)])]
def j2 := mkObj [("a", 1), ("b", Json.mkObj [("c", false), ("d", "extra")]), ("e", 42)]
def j3 := arr [mkObj [("x", 10)], mkObj [("y", 20)]].toArray
def j4 := arr [mkObj [("x", 10)], mkObj [("y", 30)], mkObj [("z", 40)]].toArray
def j5 := mkObj [("key", "value")]
def j6 := mkObj [("key", "value")]
/--
info: [Json.JsonDiff.atKey
   "b"
   (Json.JsonDiff.atKey "c" (Json.JsonDiff.message "one has boolean true and another has boolean false")),
 Json.JsonDiff.atKey "b" (Json.JsonDiff.existsKey2only "d"),
 Json.JsonDiff.existsKey2only "e"]
-/
#guard_msgs in
#eval errorJson' j1 j2
/--
info: [Json.JsonDiff.atIndex
   1
   (Json.JsonDiff.atKey "y" (Json.JsonDiff.message "one has number 20 and another has number 30")),
 Json.JsonDiff.atIndex 2 (Json.JsonDiff.message "first list does not have elements")]
-/
#guard_msgs in
#eval errorJson' j3 j4
/-- info: [] -/
#guard_msgs in
#eval errorJson' j5 j6
/-- info: [Json.JsonDiff.message "terms have different types"] -/
#guard_msgs in
#eval errorJson' j1 j3
