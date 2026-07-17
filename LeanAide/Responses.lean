import LeanAide.TranslatorParams
import LeanAideCore.Translate
import LeanAide.TranslatorParams
import LeanAide.Codegen
import LeanAide.PaperCodes
import LeanAideCore.ResponseExt
import LeanAideCore.Kernel
import LeanAideCore.Responses
import Lean

namespace LeanAide
open LeanAide Lean Codegen

/-!
Executing various tasks with Json input and output. These are for the server. We may switch to an attribute based system instead of case-based.

### **Tasks with Inputs & Outputs**

* **`translate_thm`** — *Translate a natural-language theorem into Lean and elaborate its type*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement of the theorem
  * **Outputs:**

    * `Except (Array ElabError) Expr` — either a successfully elaborated theorem type (`Expr`) or a list of elaboration errors

* **`translate_thm_detailed`** — *Translate a natural-language theorem with name and produce Lean declaration*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement
    * `theorem_name : Option Name` — optional name to assign to the theorem
  * **Outputs:**

    * `(Name × Expr × Syntax.Command)`

      * `Name` — theorem name
      * `Expr` — elaborated type of the theorem
      * `Syntax.Command` — Lean command syntax for the full theorem declaration

* **`translate_def`** — *Translate a natural-language definition into Lean code*

  * **Inputs:**

    * `definition_text : String` — natural-language definition
  * **Outputs:**

    * `Except (Array CmdElabError) Syntax.Command` — either a Lean definition command or elaboration errors

* **`theorem_doc`** — *Generate natural-language documentation for a theorem*

  * **Inputs:**

    * `theorem_name : Name` — name of the theorem
    * `theorem_statement : Syntax.Command` — Lean syntax of the theorem statement
  * **Outputs:**

    * `String` — natural-language documentation of the theorem

* **`def_doc`** — *Generate natural-language documentation for a definition*

  * **Inputs:**

    * `definition_name : Name` — name of the definition
    * `definition_code : Syntax.Command` — Lean syntax of the definition
  * **Outputs:**

    * `String` — natural-language documentation for the definition

* **`theorem_name`** — *Generate a Lean Prover name for the theorem*

  * **Inputs:**

    * `theorem_text : String` — natural-language statement
  * **Outputs:**

    * `Name` — automatically generated Lean name for the theorem

* **`prove_for_formalization`** — *Generate a detailed proof or proof sketch for a theorem*

  * **Inputs:**

    * `theorem_text : String` — natural-language theorem
    * `theorem_code : Expr` — elaborated theorem type
    * `theorem_statement : Syntax.Command` — full Lean statement
  * **Outputs:**

    * `String` — a document (likely a natural-language or partially formal proof)

* **`json_structured`** — *Convert a natural-language document into a structured JSON representation*

  * **Inputs:**

    * `document_text : String` — some natural-language math text
  * **Outputs:**

    * `Json` — structured JSON representation of the document

* **`lean_from_json_structured`** — *Generate Lean code from structured JSON*

  * **Inputs:**

    * `document_json : Json` — structured JSON of a document
  * **Outputs:**

    * `TSyntax ``commandSeq` — Lean code parsed from the JSON

* **`elaborate`** — *Elaborate Lean code and collect results, logs, and unsolved goals*

  * **Inputs:**

    * `document_code : String` — Lean code (as text)
  * **Outputs:**

    * `CodeElabResult` — structured result with:

      * `declarations : List Name` — names of elaborated declarations
      * `logs : List String` — log messages
      * `sorries : List (Name × Expr)` — unproven obligations
      * `sorriesAfterPurge : List (Name × Expr)` — remaining obligations after simplification

* **`math_query`** — *Answer a math question in natural language*

  * **Inputs:**

    * `query : String` — math question
    * `history : List ChatPair` (optional, default `[]`) — conversation context
    * `n : Nat` (optional, default `3`) — number of answers to generate
  * **Outputs:**

    * `List String` — candidate answers to the math question
-/

open Translate
/--
Implementation of the `Kernel` class which provides various functionalities such as translating theorems and definitions, generating documentation, naming theorems, proving theorems, converting to and from structured JSON, and elaborating code. This is the "server-side" implementation that uses the `Translator` to perform these tasks.
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
  translateThmDetailed := fun text name? => do
    let translator ← Translator.defaultM
    let greedy := true
    let fallback := true
    let (json, _) ←
          translator.getLeanCodeJson  text |>.run' {}
    let output ← getMessageContents json
    let res? ← greedyBestExprWithErr? output |>.run' {}
    match res? with
    | Except.error es =>
        throwError s!"Errors in translation: {repr es}"
    | Except.ok translation => do
      let defs ← defsBlob? translation
      let typeStx ← delabDetailed translation
      let thmFmt ← PrettyPrinter.ppExpr translation
      let mvar ← Lean.Meta.mkFreshExprMVar translation
      let pf? ←
        getQuickTactics? mvar.mvarId! (← cmdPreludeBlob).hash
      let name := name?.getD (← try
        translator.server.theoremName text
        catch e =>
          logToStdErr `leanaide.translate.info s!"Error in theorem name: {← e.toMessageData.format}"
          let hash := hash thmFmt.pretty
          let name := s!"thm_{hash}"
          pure name.toName)
      let thmName := mkIdent name
      let pf := pf?.getD (← `(tacticSeq| sorry))
      let thmStx ←
        `(command| theorem $thmName : $typeStx := by $pf)
      return (name, translation, thmStx)
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
    match results[0]? with
    | none => return s!" No document found for {theorem_text}"
    | some document =>
      let doc := s!"# Theorem\n{theorem_text}\n\n# Proof\n{document}"
      return doc
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
    let code ← showCommandSeq codeStx
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
  mathQuery := fun query history n => do
    let translator ← Translator.defaultM
    let res ← translator.server.mathCompletions query n translator.params history.toArray
    return res.toList
}


end LeanAide
