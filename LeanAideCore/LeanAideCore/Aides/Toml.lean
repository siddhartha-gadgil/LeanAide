import Lean
import Lake.Toml
import Lake.Toml.Decode
import Lake.Load.Toml

open Lean Lake Toml Parser

namespace LeanAide

partial def decodeJson (v: Value) : EDecodeM Json := match v with
    | .string _ s => do
      pure (Json.str s)
    | .integer _ n => pure (Json.num n.toNat)
    | .float _ f => match JsonNumber.fromFloat? f with
      | .inr num => pure (Json.num num)
      | .inl err => throwDecodeErrorAt v.ref s!"invalid float number: {err}"
    | .boolean _ b => pure (Json.bool b)
    | .dateTime _ dt => pure (Json.str dt.toString)
    | .array _ xs => do
      let mut accum : EDecodeM (Array Json) := pure #[]
      for x in xs do
        accum := mergeErrors accum (decodeJson x) fun arr j =>
          arr.push j
      return .arr (← accum)
    | .table _ t => do
      let mut accum : EDecodeM (Array (String × Json)) := pure #[]
      for (k, v) in t.items do
        accum := mergeErrors accum (decodeJson v) fun arr j =>
          arr.push (k.toString, j)
      return Json.mkObj (← accum).toList

instance jsonFromToml : DecodeToml Json where
  decode v := decodeJson v

instance [FromJson α] : DecodeToml α where
  decode v := do
    let j ← decodeJson v
    match fromJson? j with
    | .ok a => pure a
    | .error err => throwDecodeErrorAt v.ref s!"JSON decoding error: {err}"

def loadTableL (inp : IO String) : LogIO Table := do
  let ictx := mkInputContext (← inp) ("leanaide.toml")
  match ← loadToml ictx |>.toBaseIO with
  | Except.ok table => return table
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)

def loadTableIO? (file: System.FilePath := "leanaide.toml") :
    IO <| Option Table := do
  if ← file.pathExists then
    let inp ← IO.FS.readFile file
    loadTableL (pure inp) |>.run?'
  else
    return none

def tableToJson (table: Table) : EDecodeM Json := do
  let mut accum : EDecodeM (Array (String × Json)) := pure #[]
  for (k, v) in table.items do
    accum := mergeErrors accum (decodeJson v) fun arr j =>
      arr.push (k.toString, j)
  return Json.mkObj (← accum).toList

def decodeTable [FromJson α] (table: Table) : EDecodeM α := do
  let j ← tableToJson table
  match fromJson? j with
  | .ok a => pure a
  | .error err => throwDecodeErrorAt .missing s!"JSON decoding error: {err}"

def decodeJson? (v: Value) : Option Json :=
  EStateM.run' (s := (#[] : Array DecodeError)) (decodeJson v)

def loadTomlAsJson? (file: System.FilePath := "leanaide.toml") :
    IO <| Option Json := do
  let table? ← loadTableIO? file
  match table? with
  | some table =>
    let j? := decodeJson? (Value.table .missing table)
    return j?
  | none =>
    return none

partial def Toml.ofJson (j: Json) : Value :=
  match j with
  | Json.str s => Value.string .missing s
  | Json.num n =>
    match n with
    | ⟨n, 0⟩ => Value.integer .missing n
    | _      => Value.float .missing n.toFloat
  | Json.bool b => Value.boolean .missing b
  | Json.arr js =>
    let vs := js.map Toml.ofJson
    Value.array .missing vs
  | Json.obj kvs =>
    let items := kvs.toArray.map fun ⟨k, v⟩  => (k.toName, Toml.ofJson v)
    let tm : Table := items.foldl (init := {}) fun t (k, v) => t.insert k v
    Value.table .missing tm
  | Json.null => Value.string .missing "null"


end LeanAide
