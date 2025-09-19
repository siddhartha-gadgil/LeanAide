import Lean
import LeanAideCore.Aides
import LeanAideCore.TranslateM
import LeanAideCore.Translator
import LeanAideCore.TaskStatus


open Lean Meta Elab Term Parser

namespace LeanAide

open Translate

/-!
We want the same functions and the same syntax to work in LeanAide itself and a client. To do this, we will have:

* A typeclass `Kernel` capturing these.
* Given a connection to a LeanAide server (maybe another typeclass), an instance of `Kernel`.
* Given an instance of `Kernel`, `response` functions that expose the functions over a server.
-/


/--
The core functions of LeanAide, implemented directly in the server and via querying in the client.
-/
class Kernel where
  translateThm : String → TermElabM (Except (Array ElabError) Expr)
  translateDef : String → TermElabM (Except (Array CmdElabError) Syntax.Command)
  translateThmDetailed : String → Option Name → TermElabM (Name × Expr × Syntax.Command)
  theoremDoc : Name → Syntax.Command → TermElabM String
  defDoc : Name → Syntax.Command → TermElabM String
  theoremName : String → MetaM Name
  proveForFormalization : String → Expr → Syntax.Command → TermElabM String
  jsonStructured : String → MetaM Json
  codeFromJson : Json → TermElabM (TSyntax ``commandSeq)
  elabCode : TSyntax ``commandSeq → TermElabM CodeElabResult
  mathQuery (s: String) (history : List ChatPair := []) (n: Nat := 3) : MetaM (List String)

namespace Kernel

def leanFromDoc [kernel: Kernel] (doc: String) : TermElabM (TSyntax ``commandSeq) := do
  let json ← kernel.jsonStructured doc
  codeFromJson json

def proveWithCode [kernel: Kernel] (theorem_text: String) (theorem_code: Expr) (theorem_statement : TSyntax `command) :
    TermElabM (String × (TSyntax ``commandSeq)) := do
  let doc ← kernel.proveForFormalization theorem_text theorem_code theorem_statement
  return (doc, ← kernel.leanFromDoc doc)

end Kernel

inductive Deferred [Monad m][MonadLift MetaM m](α : Type)  where
  | done (result: α)
  | running
      (update : Unit → m (Option α)) : Deferred α

def Deferred.update [Monad m][MonadLift MetaM m]
  {α} (d: Deferred (m := m) α) : m (Deferred (m := m) α) :=
  match d with
  | .done r => return .done r
  | .running update => do
    let result ← update ()
    match result with
    | .none => return .running update
    | .some r => return .done r

def Deferred.updateM [Monad m][MonadLift MetaM m]
  {α} (dm: m (Deferred (m := m) α)) :
    m (Deferred (m := m) α)  := do
  let d ← dm
  Deferred.update d

class LeanAidePipe where
  queryResponse : Json → MetaM Json

namespace LeanAidePipe

def fromURL (url: String) : LeanAidePipe := {
  queryResponse (data: Json) := do
    let output ← IO.Process.run {cmd := "curl", args := #[url, "-X", "POST", "-H", "Content-Type: application/json", "--data", data.compress]}
    let .ok response :=
      Json.parse output | throwError "Failed to parse response"
    return response
}

def response [pipe: LeanAidePipe] (req: Json) : MetaM Json :=
  pipe.queryResponse req

def translateThmEncode (text: String) : MetaM Json :=
  return Json.mkObj [("task", "translate_thm"), ("theorem_text", text)]

def translateThmDecode (response: Json) : TermElabM (Except (Array ElabError) Expr) := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok thmCodeTxt := response.getObjValAs? String "theorem_code" | throwError "response has no 'theorem_code' field"
    match runParserCategory (← getEnv) `term thmCodeTxt with
    | .ok stx =>
        return .ok <| ← elabTerm stx none
    | .error e => throwError s!"Error while parsing {thmCodeTxt} : {e}"
  | .ok "failure" =>
      let .ok outputs := response.getObjValAs? (Array ElabError) "outputs" | throwError "response has no 'outputs' field"
      return .error outputs
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while translating theorem: {error}"
  | _ =>
    throwError "Invalid response"

def translateThm [pipe: LeanAidePipe] (text: String) : TermElabM (Except (Array ElabError) Expr) := do
  let response ← response <| ← translateThmEncode text
  translateThmDecode response

def translateThmDetailedEncode (text: String) (name? : Option Name) : MetaM Json :=
  match name? with
  | some name =>
    return Json.mkObj [("task", "translate_thm_detailed"), ("theorem_text", text), ("theorem_name", toJson name)]
  | none =>
    return Json.mkObj [("task", "translate_thm_detailed"), ("theorem_text", text)]

def translateThmDetailedDecode (response: Json) : TermElabM (Name × Expr × Syntax.Command) := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok name := response.getObjValAs? Name "theorem_name" | throwError "response has no 'theorem_name' field"
    let .ok thmCodeTxt := response.getObjValAs? String "theorem_code" | throwError "response has no 'theorem_code' field"
    let .ok thmStxTxt := response.getObjValAs? String "theorem_statement" | throwError "response has no 'theorem_statement' field"
    let thmExpr ←
      match runParserCategory (← getEnv) `term thmCodeTxt with
      | .ok stx =>
          elabType stx
      | .error e => throwError s!"Error while parsing {thmCodeTxt}  : {e}"
    let .ok thmStx := runParserCategory (← getEnv) `command thmStxTxt | throwError s!"Error while parsing {thmStxTxt}"
    return (name, thmExpr, ⟨thmStx⟩)
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while translating theorem: {error}"
  | _ =>
    throwError "Invalid response"

def translateThmDetailed [pipe: LeanAidePipe] (text: String) (name? : Option Name) : TermElabM (Name × Expr × Syntax.Command) := do
  let response ← response <| ← translateThmDetailedEncode text name?
  translateThmDetailedDecode response

def translateDefEncode (text: String) : MetaM Json :=
  return Json.mkObj [("task", "translate_def"), ("definition_text", text)]

def translateDefDecode (response: Json) : TermElabM (Except (Array CmdElabError) Syntax.Command) := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok defCodeTxt := response.getObjValAs? String "definition_code" | throwError "response has no 'definition_code' field"
    match runParserCategory (← getEnv) `command defCodeTxt with
    | .ok stx =>
        return .ok ⟨stx⟩
    | .error e => throwError s!"Error while parsing {defCodeTxt} : {e}"
  | .ok "failure" =>
      let .ok outputs := response.getObjValAs? (Array CmdElabError) "outputs" | throwError "response has no 'outputs' field"
      return .error outputs
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while translating definition: {error}"
  | _ =>
    throwError "Invalid response"

def translateDef [pipe: LeanAidePipe] (text: String) : TermElabM (Except (Array CmdElabError) Syntax.Command) := do
  let response ← response <| ← translateDefEncode text
  translateDefDecode response

def theoremDocEncode (name: Name) (stx: Syntax.Command) : MetaM Json := do
  return Json.mkObj [("task", "theorem_doc"), ("theorem_name", toString name), ("theorem_statement", (← PrettyPrinter.ppCommand stx).pretty)]

def theoremDocDecode (response: Json) : TermElabM String := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok doc := response.getObjValAs? String "theorem_doc" | throwError "response has no 'theorem_doc' field"
    return doc
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting theorem doc: {error}"
  | _ =>
    throwError "Invalid response"

def theoremDoc [pipe: LeanAidePipe] (name: Name) (stx: Syntax.Command) : TermElabM String := do
  let req ←  theoremDocEncode name stx
  let response ← response req
  theoremDocDecode response

def defDocEncode (name: Name) (stx: Syntax.Command) : MetaM Json := do
  return Json.mkObj [("task", "def_doc"), ("definition_name", toString name), ("definition_code", (← PrettyPrinter.ppCommand stx).pretty)]

def defDocDecode (response: Json) : TermElabM String := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok doc := response.getObjValAs? String "doc" | throwError "response has no 'doc' field"
    return doc
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting definition doc: {error}"
  | _ =>
    throwError "Invalid response"

def defDoc [pipe: LeanAidePipe] (name: Name) (stx: Syntax.Command) : TermElabM String := do
  let req ← defDocEncode name stx
  let response ← response req
  defDocDecode response

def theoremNameEncode (text: String) : MetaM Json :=
  return Json.mkObj [("task", "theorem_name"), ("theorem_text", text)]

def theoremNameDecode (response: Json) : MetaM Name := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok nameStr := response.getObjValAs? String "theorem_name" | throwError "response has no 'theorem_name' field"
    return Name.mkStr Name.anonymous nameStr
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting theorem name: {error}"
  | _ =>
    throwError "Invalid response"

def theoremName [pipe: LeanAidePipe] (text: String) : MetaM Name := do
  let req ← theoremNameEncode text
  let response ← response req
  theoremNameDecode response

def proveForFormalizationEncode (theoremText: String) (theoremCode: Expr) (theoremStatement : TSyntax `command) : MetaM Json := do
  return Json.mkObj [("task", "prove_for_formalization"), ("theorem_text", theoremText), ("theorem_code", (← ppExpr theoremCode).pretty), ("theorem_statement", (← PrettyPrinter.ppCommand theoremStatement).pretty)]

def proveForFormalizationDecode (response: Json) : TermElabM String := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok proof := response.getObjValAs? String "document_text" | throwError "response has no 'document_text' field"
    return proof
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while proving for formalization: {error}"
  | _ =>
    throwError "Invalid response"


def proveForFormalization [pipe: LeanAidePipe] (theoremText: String) (theoremCode: Expr) (theoremStatement : Syntax.Command) : TermElabM String := do
  let req ← proveForFormalizationEncode theoremText theoremCode theoremStatement
  let response ← response req
  proveForFormalizationDecode response

def jsonStructuredEncode (document: String) : MetaM Json :=
  return Json.mkObj [("task", "json_structured"), ("document_text", document)]

def jsonStructuredDecode (response: Json) : MetaM Json := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok json := response.getObjValAs? Json "document_json" | throwError "response has no 'document_json' field"
    return json
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting structured JSON: {error}"
  | _ =>
    throwError "Invalid response"

def jsonStructured [pipe: LeanAidePipe] (document: String) : MetaM Json := do
  let req ← jsonStructuredEncode document
  let response ← response req
  jsonStructuredDecode response

def codeFromJsonEncode (json: Json) : MetaM Json :=
  return Json.mkObj [("task", "lean_from_json_structured"), ("document_json", json)]

def codeFromJsonDecode (response: Json) : TermElabM (TSyntax ``commandSeq) := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok code := response.getObjValAs? String "document_code" | throwError "response has no 'document_code' field"
    parseCommands code
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting code from JSON: {error}"
  | _ =>
    throwError "Invalid response"

def codeFromJson [pipe: LeanAidePipe] (json: Json) : TermElabM (TSyntax ``commandSeq) := do
  let req ← codeFromJsonEncode json
  let response ← response req
  codeFromJsonDecode response

/-
structure CodeElabResult where
  declarations : List Name
  logs : List String
  sorries : List (Name × Expr)
  sorriesAfterPurge : List (Name × Expr)
-/
def elabCodeEncode (stx: TSyntax ``commandSeq) : MetaM Json := do
  let code ← printCommands stx
  return Json.mkObj [("task", "elaborate"), ("document_code", code)]

def elabCodeDecode (response: Json) : TermElabM CodeElabResult := do
  let .ok decls := response.getObjValAs? (List Name) "declarations" | throwError "response has no 'declarations' field"
  let .ok logs := response.getObjValAs? (List String) "logs" | throwError "response has no 'logs' field"
  let .ok sorries := response.getObjValAs? (List Json) "sorries" | throwError "response has no 'sorries' field"
  let sorries ←  sorries.mapM getSorriesFromJson
  let .ok sorriesAfterPurge := response.getObjValAs? (List Json) "sorries_after_purge" | throwError "response has no 'sorries_after_purge' field"
  let sorriesAfterPurge ← sorriesAfterPurge.mapM getSorriesFromJson
  return { declarations := decls, logs := logs, sorries := sorries, sorriesAfterPurge := sorriesAfterPurge }

def elabCode [pipe: LeanAidePipe] (stx: TSyntax ``commandSeq) : TermElabM CodeElabResult := do
  let req ← elabCodeEncode stx
  let response ← response req
  elabCodeDecode response

def mathQueryEncode (query: String) (history : List ChatPair := []) (n: Nat := 3) : MetaM Json := do
  return Json.mkObj [("task", "math_query"), ("query", query), ("n", n), ("history", toJson history)]

def mathQueryDecode (response: Json) : MetaM (List String) := do
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok answers := response.getObjValAs? (List String) "answers" | throwError "response has no 'answers' field"
    return answers
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while performing math query: {error}"
  | _ =>
    throwError "Invalid response"

def mathQuery [pipe: LeanAidePipe] (query: String) (history : List ChatPair := []) (n: Nat := 3) : MetaM (List String) := do
  let req ← mathQueryEncode query history n
  let response ← response req
  mathQueryDecode response

def updateByToken [pipe: LeanAidePipe] [Monad m]
    [MonadLift MetaM m][MonadError m] {α}
    (decode: Json → m α) (token: UInt64) :
    Unit → m (Option α)  := fun _ => do
  let req := Json.mkObj [("mode", "lookup"), ("token", toJson token)]
  let json ← response req
  let .ok status :=
    json.getObjValAs? TaskStatus "status" | throwError "response has no 'status' field"
  match status with
  | .completed _ result => return some <| ← decode result
  | .running _ => return none

def queryAsyncAux [pipe: LeanAidePipe]
    (encode: α → MetaM Json) (input : α)
    : MetaM UInt64 := do
  let req ← encode input
  let req := req.mergeObj (Json.mkObj [("mode", "async")])
  let json ← response req
  let .ok token := json.getObjValAs? UInt64 "token" | throwError "response has no 'token' field"
  return token

def queryAsync [pipe: LeanAidePipe] [Monad m]
    [MonadLift MetaM m][MonadError m] {α β}
    (encode: α → MetaM Json)
    (decode: Json → m β)
    (input : α) :
    m (Deferred (m := m) β) := do
  let token ← queryAsyncAux encode input
  return .running (updateByToken decode token)

end LeanAidePipe

instance [LeanAidePipe] : Kernel where
  translateThm := LeanAidePipe.translateThm
  translateDef := LeanAidePipe.translateDef
  translateThmDetailed := LeanAidePipe.translateThmDetailed
  theoremDoc := LeanAidePipe.theoremDoc
  defDoc := LeanAidePipe.defDoc
  theoremName := LeanAidePipe.theoremName
  proveForFormalization := LeanAidePipe.proveForFormalization
  jsonStructured := LeanAidePipe.jsonStructured
  codeFromJson := LeanAidePipe.codeFromJson
  elabCode := LeanAidePipe.elabCode
  mathQuery := fun s h n => LeanAidePipe.mathQuery s h n


macro "#leanaide_connect" url?:(str)? : command =>
match url? with
| some url => `(command| instance : LeanAidePipe := LeanAidePipe.fromURL $url)
| none => `(command| instance : LeanAidePipe := LeanAidePipe.fromURL "localhost:7654")

def getKernel [k: Kernel] : Kernel := k

def getKernelM : MetaM Kernel := do
  let inst ←  synthInstance (mkConst ``Kernel)
  unsafe evalExpr Kernel (mkConst ``Kernel) inst

namespace KernelM

def translateThm (text: String) : TermElabM (Except (Array ElabError) Expr) := do
  (← getKernelM).translateThm text

def translateThmFallback (text: String) : TermElabM <| Except String Expr := do
  match (← translateThm text) with
  | .ok e => return .ok e
  | .error errs =>
     return .error <| ←  ElabError.fallback errs |>.run' {}

def translateThmDetailed (text: String) (name? : Option Name) : TermElabM (Name × Expr × Syntax.Command) := do
  (← getKernelM).translateThmDetailed text name?

def translateDef (text: String) : TermElabM (Except (Array CmdElabError) Syntax.Command) := do
  (← getKernelM).translateDef text

def translateDefFallback (text: String) : TermElabM <| Except String Syntax.Command := do
  match (← translateDef text) with
  | .ok e => return .ok e
  | .error errs =>
     return .error <| ←  CmdElabError.fallback errs |>.run' {}

def theoremDoc (name: Name) (stx: Syntax.Command) : TermElabM String := do
  (← getKernelM).theoremDoc name stx

def defDoc (name: Name) (stx: Syntax.Command) : TermElabM String := do
  (← getKernelM).defDoc name stx

def theoremName (text: String) : MetaM Name := do
  (← getKernelM).theoremName text

def proveForFormalization (theorem_text: String) (theorem_code: Expr) (theorem_statement: TSyntax `command) : TermElabM String := do
  (← getKernelM).proveForFormalization theorem_text theorem_code theorem_statement

def jsonStructured (document: String) : MetaM Json := do
  (← getKernelM).jsonStructured document

def codeFromJson (json: Json) : TermElabM (TSyntax ``commandSeq) := do
  (← getKernelM).codeFromJson json

def mathQuery (s: String) (history : List ChatPair := []) (n: Nat := 3)  : MetaM (List String) := do
  (← getKernelM).mathQuery s history n

end KernelM

class DefinitionCommand (α : Type) where
  cmd (x: α)  : TermElabM <| Syntax.Command × Name

def definitionCommand {α} [r : DefinitionCommand α] (x: α)  : TermElabM Syntax.Command := do
  let pair ← r.cmd x
  return pair.1

def definitionCommandPair {α} [r : DefinitionCommand α] (x: α)  : TermElabM (Syntax.Command × Name) :=
  r.cmd x

class ReplaceCommand (α : Type) where
  replace (stx: Syntax) (x: α)  : TermElabM Unit

def replaceCommand {α} [r : ReplaceCommand α] (x: α) (stx: Syntax)   : TermElabM Unit :=
  r.replace stx x

def replaceCommandM {α} [r : ReplaceCommand α] (xm: TermElabM α) (stx: Syntax)   : TermElabM Unit := do
  r.replace stx (← xm)

open Tactic in
instance replaceByDefn {α} [r : DefinitionCommand α] : ReplaceCommand α where
  replace stx x := do
    let cmd ← r.cmd x
    TryThis.addSuggestion stx cmd.1

class RelativDefinitionCommand (α : Type) where
  cmd (x: α) : Syntax.Term →  TermElabM Syntax.Command

def relativDefinitionCommand {α} [r : RelativDefinitionCommand α] (x: α)  :
  Syntax.Term →   TermElabM Syntax.Command :=
  r.cmd x

end LeanAide
