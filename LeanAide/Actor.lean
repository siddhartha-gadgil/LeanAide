import LeanAide.TranslatorParams
import LeanCodePrompts.Translate
import LeanAide.StructToLean

namespace LeanAide.Actor
open LeanAide Lean

def runTask (data: Json) (translator : Translator) : TranslateM Json :=
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
    | Except.error e =>
      return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
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
  | Except.ok "theorem_doc" => do
    match data.getObjValAs? String "name", data.getObjValAs? String "command" with
    | Except.ok name, Except.ok cmd => do
      let type : Expr ← elabFrontThmExprM cmd name.toName true
      match ← translator.getTypeDescriptionM type {} with
      | some (desc, _) =>
        return Json.mkObj [("result", "success"), ("doc", desc)]
      | none => return Json.mkObj [("result", "error"), ("error", s!"no description found for {name} after elaboration of {cmd}")]
    | _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no name or command found")]
  | Except.ok "def_doc" => do
    match data.getObjValAs? String "name", data.getObjValAs? String "command" with
    | Except.ok name, Except.ok cmd => do
      let (type, value) ← elabFrontDefTypeValExprM cmd name.toName true
      match ← translator.getDefDescriptionM type value name.toName {} with
      | some (desc, _) =>
        return Json.mkObj [("result", "success"), ("doc", desc)]
      | none => return Json.mkObj [("result", "error"), ("error", s!"no description found for {name} after elaboration of {cmd}")]
    | _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no name or command found")]
  | Except.ok "theorem_name" => do
    match data.getObjValAs? String "text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
    | Except.ok text => do
      try
        let name ← translator.server.theoremName text
        return Json.mkObj [("result", "success"), ("name", toJson name)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in theorem name: {← e.toMessageData.format}")]
  | Except.ok "prove" => do
    match data.getObjValAs? String "theorem" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no theorem found: {e}")]
    | Except.ok thm => do
      let pfs ← translator.server.prove thm 1 translator.params
      match pfs.get? 0 with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some pf => do
        return Json.mkObj [("result", "success"), ("proof", toJson pf)]
  | Except.ok "structured_json_proof" => do
    match data.getObjValAs? String "theorem", data.getObjValAs? String "proof" with
    | Except.ok statement, Except.ok pf => do
      let block := s!"## Theorem : {statement}\n##Proof: {pf}"
      let jsons ←
        translator.server.structuredProof block 1 translator.params
      match jsons.get? 0 with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some json => do
        return Json.mkObj [("result", "success"), ("json_structured", json)]
    | _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no theorem or proof found")]
  | Except.ok "lean_from_thm_pf_json" => do
    match data.getObjValAs? String "json_structured" with
    | Except.ok js => do
      try
        let qp := translator.codeGenerator
        let (code, declarations) ← qp.mathDocumentCode js
        return Json.mkObj
          [("result", "success"), ("lean_code", code.pretty), ("declarations", toJson declarations), ("top_code", CodeGenerator.topCode)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in code generation: {← e.toMessageData.format}")]
    | _ => return Json.mkObj [("result", "error"), ("error", s!"no structured proof found")]
  | Except.ok "elaborate" => do
    let topCode := data.getObjValAs? String "top_code" |>.toOption |>.getD ""
    match data.getObjValAs? String "lean_code", data.getObjValAs? (List Name) "declarations" with
    | Except.ok code, Except.ok names => do
      try
        let (exprs, logs) ← elabFrontDefsExprM (topCode ++ code) names
        let hasErrors := logs.toList.any (fun log => log.severity == MessageSeverity.error)
        let result := if hasErrors then "fallback" else "success"
        let logs ←  logs.toList.mapM (fun log => log.data.format)
        let logs := logs.map (fun log => log.pretty)
        let sorries ← exprs.mapM fun (n, e) => do
          let ss ← Meta.getSorryTypes e
          ss.mapM (fun s => do
            let s ← PrettyPrinter.ppExpr s
            let s := s.pretty
            pure (n, s))
        return Json.mkObj
          [("result", result), ("logs", toJson logs), ("sorries", toJson sorries)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in code elaboration: {← e.toMessageData.format}")]
    | _, _ => return Json.mkObj [("result", "error"), ("error", s!"no structured proof found")]
  | Except.ok task => do
    let result := Json.mkObj [("result", "error"), ("error", s!"unknown task"), ("task", task)]
    return result
  where fallBackThm (es: Array ElabError) : TranslateM Json := do
    if es.isEmpty then
      return Json.mkObj [("result", "error"), ("error", "no translation found")]
    else
      let res ←  ElabError.fallback es
      return Json.mkObj [("result", "fallback"), ("theorem", res)]

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

def response (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? (List String) "tasks" with
  | Except.ok tasks => runTaskList data translator tasks
  | _ =>
    let result ← runTask data translator
    appendLog "server" (force:=true) <| Json.mkObj [("data", data), ("output", result)]
    return result.mergeObj data

end LeanAide.Actor
