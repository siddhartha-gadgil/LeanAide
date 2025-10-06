import Lean
import Qq
import LeanCodePrompts.Translate

open Lean Meta Qq

namespace LeanAide

syntax (name := response) "response" str : attr

/-- Environment extension storing responses lemmas -/
initialize responseExt :
    SimpleScopedEnvExtension (Name × String) (Std.HashMap String Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, key) =>
        m.insert key n
    initial := {}
  }

def responseKeyM : Syntax → CoreM String
  | `(attr| response $str) => return str.getString
  | _ => throwError "invalid response attribute"

initialize registerBuiltinAttribute {
  name := `response
  descr := "Lean response given task name"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let expectedType : Q(Type) := q(Json → Translator → TranslateM (Json))
    unless ← isDefEq declTy expectedType do
      throwError
        s!"codegen: {decl} has type {declTy}, but expected {expectedType}"
    let key ← responseKeyM stx
    -- logInfo m!"codegen: {decl}; keys: {keys}"
    responseExt.add (decl, key) kind
}

def responseMatches (key: String) : CoreM Name := do
  let allKeys := (responseExt.getState (← getEnv)).toArray.map (fun (k, _) => k)
  let some fn :=
    (responseExt.getState (← getEnv)).get? key | throwError
      s!"codegen: no function found for task '{key}' available tasks are {allKeys.toList}"
  return fn

def responseFromFunc  (translator: Translator) (f: Name) (source: Json) :
    TranslateM (Json) := do
  let expectedType : Q(Type) := q(Json → Translator → TranslateM (Json))
  let f := mkConst f
  let response ←
    unsafe evalExpr
      (Json → Translator → TranslateM (Json)) expectedType f
  response source translator

def responseFromTask (task: String) (translator: Translator)
    (source: Json) : TranslateM (Json) := do
  let f ← responseMatches task
  responseFromFunc translator f source

def responseFromTaskSafe (task: String) (translator: Translator)
    (source: Json) : TranslateM (Json) := do
  try
    let f ← responseMatches task
    responseFromFunc translator f source
  catch e =>
    logError m!"Error in responseFromTaskSafe: {e.toMessageData}"
    return Json.mkObj [("result", "error"), ("error", s!"failed to get response for task '{task}': {← e.toMessageData.toString}")]
