import LeanAide.TranslatorParams
import LeanCodePrompts.Translate
import LeanAide.StructToLean
import LeanAide.TranslatorParams
import LeanAide.Codegen
import LeanAide.PaperCodes
import LeanAide.Responses
import LeanAide.ResponseExt
import Lean

namespace LeanAide.Actor
open LeanAide Lean


/--
Executing a task with Json input and output. These are for the server. When a task fails, the rest of the tasks are not executed. Results are accumulated in the output.
-/
def runTask (data: Json) (translator : Translator) : TranslateM Json :=
  let translator := translator.configure data
  match data.getObjVal? "task" with
  | Except.error e  => return Json.mkObj [("result", "error"), ("error", s!"no task found: {e}")]
  | Except.ok (.str task) =>
    responseFromTaskSafe task translator data
  | Except.ok _ => return Json.mkObj [("result", "error"), ("error", s!"invalid task format")]

/--
Executing a list of tasks with Json input and output. These are for the server. When a task fails, the rest of the tasks are not executed. Results are accumulated in the output.
-/
def runTaskList (data: Json) (translator : Translator) : List String →  TranslateM Json
| [] => return data
| (task :: tasks) => do
  let data := data.setObjValAs! "task" (Json.str task)
  let result ← runTask data translator
  appendLog "server" (force := true) <| Json.mkObj [("data", data), ("output", result)]
  match result.getObjVal? "result" with
  | Except.error e =>
    return data.mergeObj <| Json.mkObj [("result", "error"), ("error", s!"error in task {task}: {e}")]
  | Except.ok "error" => return data.mergeObj result
  | Except.ok _ => do
    let data := result.mergeObj data
    runTaskList data translator tasks

/--
Executing a list of tasks with Json input and output. These are for the server. When a task fails, the rest of the tasks are not executed. Results are accumulated in the output.
-/
def runTaskChain (data: Json) (translator : Translator) : List (String × Json) →  TranslateM Json
| [] => return data
| ((task, config) :: tasks) => do
  let data := data.setObjValAs! "task" (Json.str task)
  IO.eprintln s!"running task {task}"
  let result ← runTask data <| translator.configure config
  appendLog "server" (force := true) <| Json.mkObj [("data", data), ("output", result)]
  match result.getObjVal? "result" with
  | Except.error e =>
    return data.mergeObj <| Json.mkObj [("result", "error"), ("error", s!"error in task {task}: {e}")]
  | Except.ok "error" => return data.mergeObj result
  | Except.ok _ => do
    let data := result.mergeObj data
    runTaskChain data translator tasks

/--
Responds to a request with a JSON response. The response is a JSON object that includes the input data and the output data. The output data is the result of the task or tasks. The task or tasks are specified in the input data.
-/
def response (translator : Translator)(data: Json)  :
    TranslateM Json := do
  let translator := translator.configure data
  match data.getObjValAs? (List String) "tasks" with
  | Except.ok tasks => runTaskList data translator tasks
  | _ =>
    match data.getObjValAs? (List (String × Json)) "tasks" with
    | Except.ok tasks => runTaskChain data translator tasks
    | _ =>
      let result ← runTask data translator
      appendLog "server" (force:=true) <| Json.mkObj [("data", data), ("output", result)]
      return result.mergeObj data


end LeanAide.Actor

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
