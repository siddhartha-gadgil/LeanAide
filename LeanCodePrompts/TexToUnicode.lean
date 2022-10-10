import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.FromToJson

open Std Lean

example : FromJson <| List (String × String) := inferInstance 


initialize texCommandCache : IO.Ref (HashMap String String) 
  ← IO.mkRef (HashMap.empty)

def teXCommands : IO (HashMap String String)  := do
  let cache ← texCommandCache.get
  if cache.isEmpty then 
      let jsBlob ← 
        IO.FS.readFile (System.mkFilePath ["data", "texcmds.json"])
      let l? : Except String (List (String × String)) := fromJson? jsBlob
      IO.println l?
      let l := l?.toOption.getD []
      let m := HashMap.ofList l
      texCommandCache.set m
      return m
  else return cache

#check Json.obj

-- placeholder for testing
-- def texCommands : HashMap String String := 
--       HashMap.ofList [("alpha", "α"), ("to", "→"), ("beta", "β")]

partial def teXToUnicodeAux(s accum: String) : IO String := do
  if s.isEmpty then pure accum
  else
  if s.startsWith "\\\\" then 
      teXToUnicodeAux (s.drop 2) (accum ++ "\\\\")
  else
    if s.startsWith "\\" then
    let cmd := s.drop 1 |>.takeWhile (fun c =>('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')) 
    let m ← teXCommands
    match m.find? cmd with
    | some u => teXToUnicodeAux (s.drop (cmd.length + 1)) (accum ++ u)
    | none => teXToUnicodeAux (s.drop (cmd.length + 1)) (accum ++ "\\" ++ cmd)
    else
      let beforeSlash := s.takeWhile (fun c => c ≠ '\\')
      teXToUnicodeAux (s.drop beforeSlash.length) (accum ++ beforeSlash)

def teXToUnicode(s: String) : IO String := do 
   teXToUnicodeAux (s.replace "$$" "`" |>.replace "$" "`") ""

#eval "\\".length

#eval toJson ([("a", "b")])