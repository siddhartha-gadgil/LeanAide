import LeanAide.TranslatorParams
import LeanCodePrompts.Translate
import LeanAide.StructToLean
import LeanAide.TranslatorParams
import LeanAide.Codegen
import LeanAide.PaperCodes
import LeanAide.ResponseExt
import LeanAideCore.Kernel
import Lean

namespace LeanAide
open LeanAide Lean

/-!
Executing various tasks with Json input and output. These are for the server. We may switch to an attribute based system instead of case-based.


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
* `translate_thm_detailed`: Translates a theorem to natural language with detailed information, including an attempted proof using `exact?`. The `statement` is the theorem statement with proof (which may be `sorry`).
  * input: `text: String`
  * output: `theorem: String`, `name: String`, `proved: Bool`, `statement: String`, `definitions_used: String`, `definitions_in_proof: Array String`
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
* `structured_json_proof`: (Deprecated) Converts a theorem and proof to structured JSON.
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
* `statement_from_name`: Generates a statement from a theorem name.
  * input: `name: String`
  * output: `statement: String`, `is_prop: Bool`, `name: String`, `type: String`, `value: Option String`
-/

/--
In case there is no translation that elaborates, this function will try to find a fallback theorem which is syntactically valid.
-/
def fallBackThm (es: Array ElabError) : TranslateM Json := do
  if es.isEmpty then
    return Json.mkObj [("result", "error"), ("error", "no translation found")]
  else
    let res ←  ElabError.fallback es
    return Json.mkObj [("result", "fallback"), ("theorem", res)]

/--
Echoes the input data as a JSON object.
-/
@[response "echo"]
def echoTask (data: Json) (_ : Translator) : TranslateM Json := do
  let result := Json.mkObj [("result", "success"), ("data", data)]
  return result

@[response "echo20"]
def echo20Task (data: Json) (_ : Translator) : TranslateM Json := do
  IO.sleep 20000
  let result := Json.mkObj [("result", "success"), ("data", data)]
  return result

def Translator.translateThm (text: String) (translator : Translator) (fallback greedy : Bool) : TranslateM <| (Except (Array ElabError) String) × Bool := do
  let res? ←
    if greedy then
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
  | .ok res => return (.ok res, false)
  | .error es =>
    if fallback then
      return (← ElabError.fallback? es, true)
    else
      return (.error es, false)

/--
Translates a theorem to Lean Code. If `greedy` is true, it uses a greedy approach to find the best expression.

The input is a JSON object with a `text` field containing the theorem text, and optional `greedy` and `fallback` fields.
-/
@[response "translate_thm"]
def translateThmTask (data: Json) (translator : Translator) : TranslateM Json := do
    let fallback :=
      data.getObjValAs? Bool "fallback" |>.toOption |>.getD true
    match data.getObjValAs? String "theorem_text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no 'theorem_text' found: {e}")]
    | Except.ok text => do
      let greedy :=
        data.getObjValAs? Bool "greedy" |>.toOption |>.getD true
      let res? ← translator.translateThm text fallback greedy
      match res? with
      | (Except.error es, _) =>
          return Json.mkObj [("result", "failure"), ("outputs", toJson es)]
      | (Except.ok translation, fb) => do
        if fb then
          return Json.mkObj [("result", "fallback"), ("theorem", translation)]
        else
          return Json.mkObj [("result", "success"), ("theorem_code", translation)]

/--
Translates a theorem to Lean Code with detailed information, including an attempted proof using `exact?`. The `statement` is the theorem statement with proof (which may be `sorry`). Definitions used in the theorem and in the proof are also returned.

The input is a JSON object with a `text` field containing the theorem text, and optional `greedy` and `fallback` fields.
-/
@[response "translate_thm_detailed"]
def translateThmDetailedTask (data: Json) (translator : Translator) : TranslateM Json := do
    let fallback :=
      data.getObjValAs? Bool "fallback" |>.toOption |>.getD true
    match data.getObjValAs? String "theorem_text" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no text found: {e}")]
    | Except.ok text => do
      let greedy :=
        data.getObjValAs? Bool "greedy" |>.toOption |>.getD true
      let res? ← if greedy then
        let (json, _) ←
          translator.getLeanCodeJson  text
        let output ← getMessageContents json
        greedyBestExprWithErr? output
        else
          let (res'?, _) ←
            translator.translateM  text
          pure <| res'?.map fun res' => res'.term
      match res? with
      | Except.error es =>
        if fallback then
          fallBackThm es
        else
          return Json.mkObj [("result", "error"), ("errors", toJson es)]
      | Except.ok translation => do
        let defs ← defsBlob? translation
        let typeStx ← delabDetailed translation
        let thmFmt ← PrettyPrinter.ppExpr translation
        let pf? ←
          getSimpOrExactTactics? translation <||> getHammerTactics? translation
        let name ← try
          translator.server.theoremName text
          catch e =>
            IO.eprintln s!"Error in theorem name: {← e.toMessageData.format}"
            let hash := hash thmFmt.pretty
            let name := s!"thm_{hash}"
            pure name.toName
        let thmName := mkIdent name
        let pf := pf?.getD (← `(tacticSeq| sorry))
        let thmStx ←
          `(command| theorem $thmName : $typeStx := by $pf)
        let statementFormat ← PrettyPrinter.ppCommand thmStx
        let defsInProof? ← getExactTermParts? translation
        return Json.mkObj [("result", "success"), ("theorem_code",  thmFmt.pretty),
          ("theorem_name", toJson name), ("proved", pf?.isSome),
          ("theorem_statement", statementFormat.pretty), ("definitions_used", toJson defs),
          ("definitions_in_proof", toJson defsInProof?)]

/--
Looks up a constant by its name and returns its statement, type, value, and whether it is a proposition.
-/
@[response "statement_from_name"]
def statementFromNameTask (data: Json) (_ : Translator) : TranslateM Json := do
    match data.getObjValAs? String "name" with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no name found: {e}")]
    | Except.ok name => do
      let name := name.toName
      let info ←
        try
          let info ← getConstInfo name
          let type := info.type
          let typeStx ← delabDetailed type
          let value? := info.value?
          let valueStx? ←  value?.mapM fun value =>
             delabDetailed value
          let p ← Meta.isProp type
          let stx ← mkStatement name typeStx valueStx? p
          let typeView ← PrettyPrinter.ppExpr type
          let valueView? ← value?.mapM
            fun value => PrettyPrinter.ppExpr value
          return Json.mkObj [("result", "success"), ("statement", stx), ("is_prop", toJson p), ("name", toJson name), ("type", toJson typeView.pretty),
            ("value", toJson <| valueView?.map (fun v => v.pretty) )]
        catch e =>
          return Json.mkObj [("result", "error"), ("error", s!"error in getting const info: {← e.toMessageData.format}")]

/--
Looks up a constant by its name and returns its description.
-/
@[response "theorem_doc"]
def theoremDocTask (data: Json) (translator : Translator) : TranslateM Json := do
    match data.getObjValAs? String "theorem_name", data.getObjValAs? String "theorem_statement" with
    | Except.ok name, Except.ok cmd => do
      let type : Expr ← elabFrontThmExprM cmd name.toName true
      match ← translator.getTypeDescriptionM type {} with
      | some (desc, _) =>
        return Json.mkObj [("result", "success"), ("theorem_doc", desc)]
      | none => return Json.mkObj [("result", "error"), ("error", s!"no description found for {name} after elaboration of {cmd}")]
    | _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no name or command found")]

/--
Translates a definition to Lean code and returns the definition.
-/
@[response "translate_def"]
def translateDefTask (data: Json) (translator : Translator) : TranslateM Json := do
    let fallback :=
      data.getObjValAs? Bool "fallback" |>.toOption |>.getD true
    match data.getObjValAs? String "definition_text" with
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
            return Json.mkObj [("result", "fallback"), ("definition_code", res)]
        return Json.mkObj [("result", "failure"), ("outputs", toJson es)]
      | Except.ok cmd => do
        let fmt ← PrettyPrinter.ppCommand cmd
        let result := Json.mkObj [("result", "success"), ("definition_code", fmt.pretty)]
        return result

/--
Generates documentation for a definition. The input is a JSON object with a `name` field containing the definition name and a `command` field containing the command to elaborate.
-/
@[response "def_doc"]
def defDocTask (data: Json) (translator : Translator) : TranslateM Json := do
    match data.getObjValAs? String "definition_name", data.getObjValAs? String "definition_code" with
    | Except.ok name, Except.ok cmd => do
      let (type, value) ← elabFrontDefTypeValExprM cmd name.toName true
      match ← translator.getDefDescriptionM type value name.toName {} with
      | some (desc, _) =>
        return Json.mkObj [("result", "success"), ("definition_doc", desc)]
      | none => return Json.mkObj [("result", "error"), ("error", s!"no description found for {name} after elaboration of {cmd}")]
    | _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no name or command found")]

/--
Assigns a name to a theorem. The input is a JSON object with a `theorem` or `text` field containing the theorem text.
-/
@[response "theorem_name"]
def theoremNameTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "theorem_text" with
  | Except.ok thm => do
    try
      let name ← translator.server.theoremName thm
      return Json.mkObj [("result", "success"), ("theorem_name", toJson name)]
    catch e =>
      return Json.mkObj [("result", "error"), ("error", s!"error in theorem name: {← e.toMessageData.format}")]
  | _ => return Json.mkObj [("result", "error"), ("error", "no theorem or text found")]

/--
Use an LLM to prove a theorem. The input is a JSON object with a `theorem` field containing the theorem text.
-/
@[response "prove"]
def proveTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "theorem_text" with
  | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no theorem found: {e}")]
  | Except.ok thm => do
    let pfs ← translator.server.prove thm 1 translator.params
    match pfs[0]? with
    | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
    | some pf => do
      return Json.mkObj [("result", "success"), ("proof_text", toJson pf)]

/--
Use an LLM to prove a theorem. The input is a JSON object with a `text` field containing the theorem text, a `theorem` field containing the statement of the theorem and `definitions` containing relevant definitions.
-/
@[response "prove_for_formalization"]
def proveForFormalizationTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "theorem_text", data.getObjValAs? String "theorem_code" with
  | Except.ok thm, Except.ok statement => do
    let .ok type ← elabThm statement | return Json.mkObj [("result", "error"), ("error", s!"error in elaboration of theorem statement")]
    let definitions := data.getObjValAs? String "definitions" |>.toOption.getD ((← defsBlob? type).getD "")
    let docs ← translator.server.proveForFormalization thm statement definitions 1 translator.params
    match docs[0]? with
    | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
    | some doc => do
      return Json.mkObj [("result", "success"), ("document", toJson doc)]
  | _, _ => return Json.mkObj [("result", "error"), ("error", s!"no theorem found")]


/--
Proves a proposition using an LLM. The input is a JSON object with a `prop` field containing the proposition in Lean Syntax.
-/
@[response "prove_prop"]
def provePropTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "prop" with
  | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no `prop` found: {e}")]
  | Except.ok p => do
    match Parser.runParserCategory (← getEnv) `term p with
    | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"error in parsing `prop`: {e}")]
    | Except.ok propStx => do
      try
        let p ← Elab.Term.elabType propStx
        match ← translator.getTypeProofM p with
        | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
        | some (proof, _, _) => do
          return Json.mkObj [("result", "success"), ("theorem_proof", toJson proof)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in proving `prop`: {← e.toMessageData.format}")]

@[response "json_structured"]
def jsonStructuredTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "document_text" with
  | Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no document found: {e}")]
  | Except.ok document => do
    let jsons ←
      translator.server.jsonStructured document 1 translator.params
    match jsons[0]? with
    | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
    | some json => do
      return Json.mkObj [("result", "success"), ("document_json", json)]

/--
Converts a theorem and proof to structured JSON. The input is a JSON object with a `theorem`, `proof`, or `theorem_proof` field containing the theorem statement and proof
-/
@[response "structured_json_proof"]
def structuredJsonTask (data: Json) (translator : Translator) : TranslateM Json := do
    match data.getObjValAs? String "theorem_text", data.getObjValAs? String "proof_text", data.getObjValAs? String "theorem_proof" with
    | _, _, Except.ok block => do
      let jsons ←
        translator.server.structuredProof block 1 translator.params
      match jsons[0]? with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some json => do
        return Json.mkObj [("result", "success"), ("json_structured", json)]
    | Except.ok statement, Except.ok pf, _ => do
      let block := s!"## Theorem : {statement}\n##Proof: {pf}"
      let jsons ←
        translator.server.structuredProof block 1 translator.params
      match jsons[0]? with
      | none => return Json.mkObj [("result", "error"), ("error", "no proof found")]
      | some json => do
        return Json.mkObj [("result", "success"), ("document_json", json)]
    | _, _, _ =>
      return Json.mkObj [("result", "error"), ("error", "no theorem or proof found")]

/--
Generates Lean code from structured JSON. The input is a JSON object with a `json_structured` field containing the structured proof in JSON format.
-/
@[response "lean_from_json_structured"]
def leanFromStructuredJsonTask (data: Json) (translator : Translator) : TranslateM Json := do
    match data.getObjVal? "document_json" with
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
          [("result", "success"), ("document_code", code.pretty), ("declarations", toJson declarations), ("top_code", CodeGenerator.topCode)]
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in code generation: {← e.toMessageData.format}")]
    | _ => return Json.mkObj [("result", "error"), ("error", s!"no structured proof found")]

/--
Elaborates Lean code. The input is a JSON object with a `lean_code` field containing the Lean code to elaborate, and an optional `declarations` field containing the names of declarations to elaborate. If the `declarations` field is not provided, the names are extracted from the code. The `top_code` field can be used to provide additional code that should be included at the top of the elaboration.
If `describe_sorries` is true, the elaboration will include descriptions of the sorry types.
The output is a JSON object with the result of the elaboration, including logs and sorries (if any).
-/
@[response "elaborate"]
def elaborateTask (data: Json) (translator : Translator) : TranslateM Json := do
    match data.getObjValAs? String "document_code" with
    | Except.ok code => do
      let names? := data.getObjValAs? (List Name) "declarations" |>.toOption
      try
        let (exprs, logs) ←
          match names? with
          | some names =>
          elabFrontDefsExprM code names
          | none =>
            elabFrontDefsNewExprM code
        let names := names?.getD <| exprs.map (fun (n, _) => n)
        let describeSorries := data.getObjValAs? Bool "describe_sorries" |>.toOption |>.getD false
        let hasErrors := logs.toList.any
          (fun lg => lg.severity == MessageSeverity.error)
        let result := if hasErrors then "fallback" else "success"
        let logs ←  logs.toList.mapM (fun lg => lg.data.format)
        let logs := logs.map (fun lg => lg.pretty)
        let sorries ← exprs.mapM fun (n, e) => do
          let ss ← getSorryTypes e
          let e' ← purgeLets e
          let ss' ← getSorryTypes e'
          ss.mapM fun expr => do
            let s ← PrettyPrinter.ppExpr expr
            let s := s.pretty
            let res := Json.mkObj [("declaration_name", toJson n), ("sorry_type", s)]
            if describeSorries then
              let desc ← translator.getTypeDescriptionM expr {}
              match desc with
              | some (desc, _) =>
                let res := res.mergeObj <| Json.mkObj [("sorry_description", desc)]
                let defs ← defsBlob? expr
                let typeStx ← delabDetailed expr
                let thmFmt ← PrettyPrinter.ppExpr expr
                let pf? ←
                  getSimpOrExactTactics? expr <||> getHammerTactics? expr
                let name ← try
                  translator.server.theoremName desc
                  catch e =>
                    IO.eprintln s!"Error in theorem name: {← e.toMessageData.format}"
                    let hash := hash thmFmt.pretty
                    let name := s!"thm_{hash}"
                    pure name.toName
                let thmName := mkIdent name
                let pf := pf?.getD (← `(tacticSeq| sorry))
                let thmStx ←
                  `(command| theorem $thmName : $typeStx := by $pf)
                let statementFormat ← PrettyPrinter.ppCommand thmStx
                let defsInProof? ← getExactTermParts? expr
                return res.mergeObj <| Json.mkObj [("theorem",  thmFmt.pretty),
                  ("name", toJson name), ("proved", pf?.isSome),
                  ("statement", statementFormat.pretty), ("definitions_used", toJson defs),
                  ("definitions_in_proof", toJson defsInProof?)]
              | none => pure res
            else
              pure res
        let sorries' ← exprs.mapM fun (n, e) => do
          let e' ← purgeLets e
          let ss' ← getSorryTypes e'
          ss'.mapM fun expr => do
            let s ← PrettyPrinter.ppExpr expr
            let s := s.pretty
            let res := Json.mkObj [("declaration_name", toJson n), ("sorry_type", s)]
            pure res
        let response := Json.mkObj
          [("result", result), ("logs", toJson logs), ("declarations", toJson names), ("sorries", toJson sorries), ("sorries_after_purge", toJson sorries')]
        return response
      catch e =>
        return Json.mkObj [("result", "error"), ("error", s!"error in code elaboration: {← e.toMessageData.format}")]
    | _ => return Json.mkObj [("result", "error"), ("error", s!"no lean code found")]

@[response "math_query"]
def mathQueryTask (data: Json) (translator : Translator) : TranslateM Json := do
  match data.getObjValAs? String "query" with
| Except.error e => return Json.mkObj [("result", "error"), ("error", s!"no query found: {e}")]
  | Except.ok query => do
    try
      let n := data.getObjValAs? Nat "n" |>.toOption |>.getD 1
      let res ← translator.server.mathCompletions query n translator.params
      return Json.mkObj [("result", "success"), ("answers", toJson res)]
    catch e =>
      return Json.mkObj [("result", "error"), ("error", s!"error in math query: {← e.toMessageData.format}")]

/--
Implementation of the `Kernel` class which provides various functionalities such as translating theorems and definitions, generating documentation, naming theorems, proving theorems, converting to and from structured JSON, and elaborating code. This is the "server-side" implementation that uses the `Translator` to perform these tasks.

```lean4
class Kernel where
  translateThm : String → TermElabM (Except (Array ElabError) Expr)
  translateDef : String → TermElabM (Except (Array CmdElabError) Syntax.Command)
  theoremDoc : Name → Syntax.Command → TermElabM String
  defDoc : Name → Syntax.Command → TermElabM String
  theoremName : String → CoreM Name
  proveForFormalization : Name → Expr → TermElabM String
  jsonStructured : String → CoreM Json
  codeFromJson : String → TermElabM (TSyntax ``commandSeq)
  elabCode : TSyntax ``commandSeq → TermElabM CodeElabResult
```
-/
instance kernel : Kernel := {
  translateThm := fun text => do
    let translator ← Translator.defaultM
    let resM? := translator.translateToProp? text
    let res? ← resM?.run' {}
    return res?
  translateDef := fun text => do
    let translator ← Translator.defaultM
    let resM? := translator.translateDefCmdM? text
    let res? ← resM?.run' {}
    return res?
  theoremDoc := fun name cmd => do
    let translator ← Translator.defaultM
    let cmdStr ← PrettyPrinter.ppCommand cmd
    let type : Expr ← elabFrontThmExprM cmdStr.pretty name true
    match ← translator.getTypeDescriptionM type {} with
      | some (desc, _) =>
        return desc
      | none => throwError  s!"no description found for {name} after elaboration of {cmd}"

  defDoc := fun name cmd => do
    let translator ← Translator.defaultDefM
    let (type, value) ← elabFrontDefTypeValExprM (← PrettyPrinter.ppCommand cmd).pretty name true
    match ← translator.getDefDescriptionM type value name {} with
    | some (desc, _) =>
      return desc
    | none => throwError s!"no description found for {name} after elaboration of {cmd}"
  theoremName := fun text => do
    let translator ← Translator.defaultM
    translator.server.theoremName text
  proveForFormalization := fun theorem_text theorem_code theorem_statement => do
    let translator ← Translator.defaultM
    let defs := (←  defsBlob? theorem_code).getD ""
    let results ← translator.server.proveForFormalization theorem_text (← PrettyPrinter.ppCommand theorem_statement).pretty defs 1 translator.params
    return results[0]?.getD (s!"No document found for {theorem_text}")
  jsonStructured := fun document => do
    let translator ← Translator.defaultM
    let jsons ←
      translator.server.jsonStructured document 1 translator.params
    match jsons[0]? with
    | none => throwError "no proof found"
    | some json => return json
  codeFromJson := fun jsonStructured => do
    let translator ← Translator.defaultM
    let qp := translator.codeGenerator
    let codeTM := Codegen.getCode qp none ``commandSeq jsonStructured
    let some codeStx ← codeTM.run' {} |
      throwError "Did not obtain code"
    return codeStx
  elabCode := fun codeStx => do
    let code ← printCommands codeStx
    let (exprs, logs) ←  elabFrontDefsNewExprM code
    let names := exprs.map (fun (n, _) => n)
    let logs ←  logs.toList.mapM (fun lg => lg.data.format)
    let logs := logs.map (fun lg => lg.pretty)
    let mut sorries := #[]
    let mut sorriesAfterPurge := #[]
    for (n, e) in exprs do
      let ss ← getSorryTypes e
      for type in ss do
        sorries := sorries.push (n, type)
      let e' ← purgeLets e
      let ss' ← getSorryTypes e'
      for type in ss' do
        sorriesAfterPurge := sorriesAfterPurge.push (n, type)
    return {declarations := names, logs := logs, sorries := sorries.toList, sorriesAfterPurge := sorriesAfterPurge.toList}
  mathQuery := fun query n => do
    let translator ← Translator.defaultM
    let res ← translator.server.mathCompletions query n translator.params
    return res.toList
}

end LeanAide
