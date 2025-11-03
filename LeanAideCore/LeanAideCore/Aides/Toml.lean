import Lean
import Lake.Toml
import Lake.Toml.Decode

open Lean Lake Toml

partial def decodeJson (v: Value) : EDecodeM Json := match v with
    | .string _ s => pure (Json.str s)
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
