import LeanAide.TranslatorParams
import LeanCodePrompts.Translate
import LeanAide.StructToLean
import LeanAide.TranslatorParams
import LeanAide.Codegen
import LeanAide.PaperCodes
import Lean

namespace LeanAide.Actor
open LeanAide Lean

/--
Executing various tasks with Json input and output. These are for the server.

## Tasks

* `echo`: Echoes the input data.
  * input: `data: Json`
  * output: `data: Json`
* `translate_thm`: Translates a theorem to natural language.
  * input: `text: String`
  * output: `theorem: String`
  * parameters:
    * `greedy: Bool` (default: `true`)
    * `fallback: Bool` (default: `true`)
* `translate_def`: Translates a definition to natural language.
  * input: `text: String`
  * output: `definition: String`
  * parameters:
    * `fallback: Bool` (default: `true`)
* `theorem_doc`: Generates documentation for a theorem.
  * input: `name: String`, `command: String`
  * output: `doc: String`
* `def_doc`: Generates documentation for a definition.
  * input: `name: String`, `command: String`
  * output: `doc: String`
* `theorem_name`: Names a theorem in Lean's style.
  * input: `text: String`
  * output: `name: String`
* `prove`: Attempts to prove a theorem.
  * input: `theorem: String`
  * output: `proof: String`
* `structured_json_proof`: Converts a theorem and proof to structured JSON.
  * input: `theorem: String`, `proof: String`
  * output: `json_structured: Json`
* `lean_from_json_structured`: Generates Lean code from structured JSON.
  * input: `json_structured: String`
  * output: `lean_code: String`, `declarations: List String`, `top_code: String`
* `elaborate`: Elaborates Lean code.
  * input: `lean_code: String`, `declarations: List Name`
  * output: `logs: List String`, `sorries: List Json`
  * parameters:
    * `top_code: String` (default: `""`)
    * `describe_sorries: Bool` (default: `false`)
-/
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
    match data.getObjValAs? String "theorem" |>.toOption
      |>.orElse fun _ => (data.getObjValAs? String "text" |>.toOption) with
    | none => return Json.mkObj [("result", "error"), ("error", s!"no text/theorem found")]
    | some text => do
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
  | Except.ok "prove_prop" => do
    match data.getObjValAs? String "prop" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no `prop` found: {e}")]
    | Except.ok prop => do
      match Parser.runParserCategory (← getEnv) `term prop with
      | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"error in parsing `prop`: {e}")]
      | Except.ok propStx => do
        try
          let prop ← Elab.Term.elabType propStx
          match ← translator.getTypeProofM prop with
          | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
          | some (proof, _, _) => do
            return Json.mkObj [("result", "success"), ("theorem_proof", toJson proof)]
        catch e =>
          return Json.mkObj [("result", "error"), ("error", s!"error in proving `prop`: {← e.toMessageData.format}")]
  | Except.ok "structured_json_proof" => do
    match data.getObjValAs? String "theorem", data.getObjValAs? String "proof", data.getObjValAs? String "theorem_proof" with
    | _, _, Except.ok block => do
      let jsons ←
        translator.server.structuredProof block 1 translator.params
      match jsons.get? 0 with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some json => do
        return Json.mkObj [("result", "success"), ("json_structured", json)]
    | Except.ok statement, Except.ok pf, _ => do
      let block := s!"## Theorem : {statement}\n##Proof: {pf}"
      let jsons ←
        translator.server.structuredProof block 1 translator.params
      match jsons.get? 0 with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some json => do
        return Json.mkObj [("result", "success"), ("json_structured", json)]
    | _, _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no theorem or proof found")]
  | Except.ok "lean_from_json_structured" => do
    match data.getObjVal? "json_structured" with
    | Except.ok js => do
      try
        let qp := translator.codeGenerator
        let some codeStx ←  Codegen.getCode qp none ``commandSeq js |
          throwError "Did not obtain code"
        let declarations :=
          CodeGenerator.namesFromCommands <| commands codeStx
        let code ←
          PrettyPrinter.ppCategory ``commandSeq codeStx
        return Json.mkObj
          [("result", "success"), ("lean_code", code.pretty), ("declarations", toJson declarations), ("top_code", CodeGenerator.topCode)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in code generation: {← e.toMessageData.format}")]
    | _ => return Json.mkObj [("result", "error"), ("error", s!"no structured proof found")]
  | Except.ok "lean_from_json_structured_old" => do
    match data.getObjVal? "json_structured" with
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
    -- let topCode := data.getObjValAs? String "top_code" |>.toOption |>.getD ""
    match data.getObjValAs? String "lean_code", data.getObjValAs? (List Name) "declarations" with
    | Except.ok code, Except.ok names => do
      try
        let describeSorries := data.getObjValAs? Bool "describe_sorries" |>.toOption |>.getD false
        let (exprs, logs) ← elabFrontDefsExprM (code) names
        let hasErrors := logs.toList.any
          (fun lg => lg.severity == MessageSeverity.error)
        let result := if hasErrors then "fallback" else "success"
        let logs ←  logs.toList.mapM (fun lg => lg.data.format)
        let logs := logs.map (fun lg => lg.pretty)
        let sorries ← exprs.mapM fun (n, e) => do
          let ss ← Meta.getSorryTypes e
          ss.mapM fun expr => do
            let s ← PrettyPrinter.ppExpr expr
            let s := s.pretty
            let res := Json.mkObj [("declaration_name", toJson n), ("sorry_type", s)]
            if describeSorries then
              let desc ← translator.getTypeDescriptionM expr {}
              match desc with
              | some (desc, _) =>
                let res := res.mergeObj <| Json.mkObj [("sorry_description", desc)]
                pure res
              | none => pure res
            else
              pure res
        let response := Json.mkObj
          [("result", result), ("logs", toJson logs), ("sorries", toJson sorries)]
        return response
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
def response (data: Json) (translator : Translator) :
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
