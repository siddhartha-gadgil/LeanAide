import Lean
import LeanAideCore.Aides

namespace LeanAide

open Lean

inductive TaskStatus
| running (input: Json)
| completed (input result: Json)
deriving Repr, ToJson, FromJson, Inhabited

def TaskStatus.input : TaskStatus → Json
| TaskStatus.running input => input
| TaskStatus.completed input _ => input


abbrev TasksState := Std.Mutex <| Std.HashMap UInt64 TaskStatus



-- #eval toJson (TaskStatus.running <| json% {})
-- #eval toJson (TaskStatus.completed (json% {"a": 1}) (json% {"b": 2}))
namespace TasksState


def addStart (ts: TasksState) (hash: UInt64)
    (input: Json) : IO Unit :=
  ts.atomically do
    modify (·.insert hash (TaskStatus.running input))

def addResult (ts: TasksState) (hash: UInt64) (result: Json) : IO Unit :=
  ts.atomically do
    modify (fun m =>
      let ts := m[hash]!
      let input := ts.input
      m.insert hash (TaskStatus.completed input result)
      )

def lookup (ts: TasksState) (hash: UInt64) : IO (Option TaskStatus) :=
  ts.atomically do
    let m ← get
    return m[hash]?

def lookupJson (ts: TasksState) (hash: UInt64) : IO Json := do
  let state? ← lookup ts hash
  match state? with
  | some ts => return Json.mkObj [("result", "success"), ("status", toJson ts), ("hash", toJson hash)]
  | none => return Json.mkObj [("result", "error"), ("error", s!"no task found for hash {hash}")]

end TasksState

end LeanAide
