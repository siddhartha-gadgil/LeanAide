import Lean
import LeanAide.Config
open Lean
namespace LeanAide
namespace putnam

def src : IO Json := do
  let path := (← resourcesDir)/ "putnam.json"
  let src ←  IO.FS.readFile path
  match Json.parse src with
  | Except.error e => throw <| IO.userError e
  | Except.ok j => pure j

initialize putnamSouce : IO.Ref <| Option Json ← IO.mkRef none

def getSrc : IO Json := do
  let src? ← putnamSouce.get
  match src? with
  | some src => pure src
  | none => do
    let src ← src
    putnamSouce.set <| some src
    pure src
-- #eval src

def getTheorem (index : Nat) : IO String := do
  let src ← getSrc
  let js ←  match src.getArr? with
    | Except.ok js => pure js
    | _ => IO.throwServerError "invalid json source"
  match js.get? index with
  | some j => match j.getObjValAs? String "informal_statement", j.getObjValAs? String "informal_solution" with
    | Except.ok s, Except.ok "None." => pure s
    | Except.ok s, Except.ok soln => pure <| s ++ soln
    | Except.ok s, _ => pure s
    | _, _ => IO.throwServerError s!"invalid json at index {index}; {j.pretty}"
  | _ => IO.throwServerError "invalid index"

end putnam

def putnamProblem (index : Nat) : IO String := do
  putnam.getTheorem index

end LeanAide
