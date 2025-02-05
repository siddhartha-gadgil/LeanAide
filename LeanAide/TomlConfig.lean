import Lake.Load.Toml

open Lean Parser Lake
open System (FilePath)

open Toml

def eg := "hello = 'this world'\nn = 42\n[leanaide]\nname = 'leanaide'"

def loadTable : LogIO <| Table × String × Nat × String := do
  let ictx := mkInputContext eg ("")
  match ← loadToml ictx |>.toBaseIO with
  | Except.ok table =>
    let hello ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        table.tryDecodeD  `hello "decode world"
    let n ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        table.tryDecodeD  `n 0
    let t : Table ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        table.tryDecode  `leanaide
    let name ←
      StateT.run' (s := (#[] : Array DecodeError)) do
        t.tryDecodeD `name "missing?"
    return (table, hello, n, name)
  | .error log =>
    errorWithLog <| log.forM fun msg => do logError (← msg.toString)


def loadHello : IO <| String × Nat × String:= do
  let hello? ← loadTable.toBaseIO
  match hello? with
  | some (_, hello, n, name) => return (hello, n, name)
  | none => return ("IO world", 12, "missing name")

#check Table

#eval loadHello
