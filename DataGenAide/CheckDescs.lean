import Lean
import LeanAide.Aides
import LeanAideCore.StatementSyntax
import Mathlib

namespace LeanAide
open Lean Meta Nat

def names : IO (Array Name) := do
  let jsLines ← IO.FS.lines ((← resourcesDir) / "mathlib4-descs.jsonl")
  let mut names := #[]
  for line in jsLines do
    let .ok js := Json.parse line | throw <| IO.userError s!"Failed to parse JSON line: {line}"
    let .ok name := js.getObjValAs? Name "name" | throw <| IO.userError s!"Failed to parse JSON line: {line}"
    names := names.push name
  return names

def namesSplit : MetaM (Array Name × Array Name) := do
  let ns ← names
  let mut valid := #[]
  let mut invalid := #[]
  let env ← getEnv
  for n in ns do
    if (env.find? n).isSome then
      valid := valid.push n
    else
      unless ← n.isBlackListed do
        invalid := invalid.push n
  return (valid, invalid)

def namesSize : MetaM (Nat × Nat) := do
  let (valid, invalid) ← namesSplit
  return (valid.size, invalid.size)

-- #eval namesSize

def writeInvalid : MetaM Unit := do
  let (_, invalid) ← namesSplit
  let h ← IO.FS.Handle.mk ((← resourcesDir) / "mathlib4-invalid-names.txt") IO.FS.Mode.write
  for n in invalid do
    h.putStrLn s!"{n}"

-- #eval writeInvalid

-- #eval json%{"n" : 1, "s" : "hello"}.mergeObj (json%{"b" : true, "s" : "goodbye"})

def update? (js: Json) : MetaM (Option Json) := do
  let .ok name := js.getObjValAs? Name "name" | throwError s!"Failed to parse JSON: {js}"
  let env ← getEnv
  match env.find? name with
  | none => return none
  | some info =>
    let typeStx ←
      delabDetailed info.type
    let typeStr ← ppExprDetailed info.type
          let isNoncomputable := Lean.isNoncomputable (← getEnv) name
    let statement ←
            mkStatement (some name) typeStx none true (isNoncomputable := isNoncomputable)
    let newJson :=
      js.mergeObj (Json.mkObj [("type" , typeStr), ("statement", statement)])
    return some newJson

def updateDescCore? (js: Json) : CoreM (Option Json) :=
  update? js |>.run'

end LeanAide
