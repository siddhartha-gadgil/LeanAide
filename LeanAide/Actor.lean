import LeanAide.TranslatorParams
import LeanCodePrompts.Translate

namespace LeanAide.Actor
open LeanAide Lean

#check Except.mapM
def response (data: Json) (translator : Translator) : TranslateM Json :=
  let fallback :=
    data.getObjValAs? Bool "fallback" |>.toOption |>.getD true
  match data.getObjVal? "task" with
  | Except.error e  => return Json.mkObj [("result", "error"), ("error", s!"no task found: {e}")]
  | Except.ok "echo" => do
    let result := Json.mkObj [("result", "success"), ("data", data)]
    return result
  | Except.ok "translate_thm" => do
    match data.getObjValAs? String "text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
    | Except.ok text => do
      let greedy :=
        data.getObjValAs? Bool "greedy" |>.toOption |>.getD true
      let res? ← if greedy then
        let (json, _) ←
          translator.getLeanCodeJson  text
        let output ← getMessageContents json
        let res' ← greedyBestExprWithErr? output
        res'.mapM fun res' => res'.view
        else
          let (res'?, _) ←
            translator.translateM  text
          res'?.mapM fun res' => res'.view
      match res? with
      | Except.error es =>
        if fallback then
          fallBackThm es
        else
          return Json.mkObj [("result", "error"), ("errors", toJson es)]
      | Except.ok translation => do
        return Json.mkObj [("result", "success"), ("theorem", translation)]
  | Except.ok "translate_def" => do
    match data.getObjValAs? String "text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
    | Except.ok text => do
      match ← translator.translateDefCmdM? text with
      | Except.error es =>
        if fallback then
          if es.isEmpty then
            return Json.mkObj [("result", "error"), ("error", "no translation found")]
          else
            let res ←  CmdElabError.fallback es
            return Json.mkObj [("result", "fallback"), ("definition", res)]
        return Json.mkObj [("result", "error"), ("errors", toJson es)]
      | Except.ok cmd => do
        let fmt ← PrettyPrinter.ppCommand cmd
        let result := Json.mkObj [("result", "success"), ("definition", fmt.pretty)]
        return result
  | Except.ok task => do
    let result := Json.mkObj [("result", "error"), ("error", s!"unknown task"), ("task", task)]
    return result
  where fallBackThm (es: Array ElabError) : TranslateM Json := do
    if es.isEmpty then
      return Json.mkObj [("result", "error"), ("error", "no translation found")]
    else
      let res ←  ElabError.fallback es
      return Json.mkObj [("result", "fallback"), ("theorem", res)]


end LeanAide.Actor
