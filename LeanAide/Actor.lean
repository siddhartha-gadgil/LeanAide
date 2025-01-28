import LeanAide.TranslatorParams
import LeanCodePrompts.Translate

namespace LeanAide.Actor
open LeanAide Lean

-- dummy for now
def response (data: Json) (translator : Translator) : TranslateM Json :=
  match data.getObjVal? "task" with
  | Except.error e  => return Json.mkObj [("result", "error"), ("error", s!"no task found: {e}")]
  | Except.ok "echo" => do
    let result := Json.mkObj [("result", "success"), ("data", data)]
    return result
  | Except.ok "translate_thm" => do
    match data.getObjValAs? String "text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
    | Except.ok text => do
      match ← translator.translateM text with
      | (Except.error e, _) =>
        return Json.mkObj [("result", "error"), ("errors", toJson e)]
      | (Except.ok translation, _) => do
        let result := Json.mkObj [("result", "success"), ("theorem", ← translation.view)]
        return result
  | Except.ok task => do
    let result := Json.mkObj [("result", "error"), ("error", s!"unknown task: {task}")]
    return result


end LeanAide.Actor
