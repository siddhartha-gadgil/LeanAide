import Lean
import LeanAideCore.Aides
import LeanAideCore.TranslateM
import LeanAideCore.Translator


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
  theoremDoc : Name → Syntax.Command → TermElabM String
  defDoc : Name → Syntax.Command → TermElabM String
  theoremName : String → CoreM Name
  proveForFormalization : String → Expr → TermElabM String
  jsonStructured : String → CoreM Json
  codeFromJson : Json → TermElabM (TSyntax ``commandSeq)
  elabCode : TSyntax ``commandSeq → TermElabM CodeElabResult
  mathQuery : String → CoreM (List String)

namespace Kernel

def leanFromDoc [kernel: Kernel] (doc: String) : TermElabM (TSyntax ``commandSeq) := do
  let json ← kernel.jsonStructured doc
  codeFromJson json

def proveWithCode [kernel: Kernel] (statement: String) (thm: Expr) :
    TermElabM (String × (TSyntax ``commandSeq)) := do
  let doc ← kernel.proveForFormalization statement thm
  return (doc, ← kernel.leanFromDoc doc)

end Kernel


class LeanAidePipe where
  queryResponse : Json → CoreM Json

namespace LeanAidePipe

def fromURL (url: String) : LeanAidePipe := {
  queryResponse (data: Json) := do
    let output ← IO.Process.run {cmd := "curl", args := #[url, "-X", "POST", "-H", "Content-Type: application/json", "--data", data.compress]}
    let .ok response :=
      Json.parse output | throwError "Failed to parse response"
    return response
}

def response [pipe: LeanAidePipe] (req: Json) : CoreM Json :=
  pipe.queryResponse req

def translateThm [pipe: LeanAidePipe] (text: String) : TermElabM (Except (Array ElabError) Expr) := do
  let req := Json.mkObj [("task", "translate_thm"), ("text", text)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok thmTxt := response.getObjValAs? String "theorem" | throwError "response has no 'theorem' field"
    match runParserCategory (← getEnv) `term thmTxt with
    | .ok stx =>
        return .ok <| ← elabTerm stx none
    | .error e => throwError s!"Error while parsing {thmTxt} : {e}"
  | .ok "failure" =>
      let .ok outputs := response.getObjValAs? (Array ElabError) "outputs" | throwError "response has no 'outputs' field"
      return .error outputs
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while translating theorem: {error}"
  | _ =>
    throwError "Invalid response"

def translateDef [pipe: LeanAidePipe] (text: String) : TermElabM (Except (Array CmdElabError) Syntax.Command) := do
  let req := Json.mkObj [("task", "translate_def"), ("text", text)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok defTxt := response.getObjValAs? String "definition" | throwError "response has no 'definition' field"
    match runParserCategory (← getEnv) `command defTxt with
    | .ok stx =>
        return .ok ⟨stx⟩
    | .error e => throwError s!"Error while parsing {defTxt} : {e}"
  | .ok "failure" =>
      let .ok outputs := response.getObjValAs? (Array CmdElabError) "outputs" | throwError "response has no 'outputs' field"
      return .error outputs
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while translating definition: {error}"
  | _ =>
    throwError "Invalid response"

def theoremDoc [pipe: LeanAidePipe] (name: Name) (stx: Syntax.Command) : TermElabM String := do
  let req :=
    Json.mkObj [("task", "theorem_doc"), ("name", toString name), ("syntax", (← PrettyPrinter.ppCommand stx).pretty)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok doc := response.getObjValAs? String "doc" | throwError "response has no 'doc' field"
    return doc
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting theorem doc: {error}"
  | _ =>
    throwError "Invalid response"

def defDoc [pipe: LeanAidePipe] (name: Name) (stx: Syntax.Command) : TermElabM String := do
  let req :=
    Json.mkObj [("task", "def_doc"), ("name", toString name), ("syntax", (← PrettyPrinter.ppCommand stx).pretty)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok doc := response.getObjValAs? String "doc" | throwError "response has no 'doc' field"
    return doc
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting definition doc: {error}"
  | _ =>
    throwError "Invalid response"

def theoremName [pipe: LeanAidePipe] (text: String) : CoreM Name := do
  let req := Json.mkObj [("task", "theorem_name"), ("text", text)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok nameStr := response.getObjValAs? String "name" | throwError "response has no 'name' field"
    return Name.mkStr Name.anonymous nameStr
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting theorem name: {error}"
  | _ =>
    throwError "Invalid response"

def proveForFormalization [pipe: LeanAidePipe] (statement: String) (thm: Expr) : TermElabM String := do
  let req :=
    Json.mkObj [("task", "prove_for_formalization"), ("text", statement), ("theorem", (← ppExpr thm).pretty)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok proof := response.getObjValAs? String "document" | throwError "response has no 'document' field"
    return proof
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while proving for formalization: {error}"
  | _ =>
    throwError "Invalid response"

def jsonStructured [pipe: LeanAidePipe] (document: String) : CoreM Json := do
  let req := Json.mkObj [("task", "json_structured"), ("document", document)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok json := response.getObjValAs? Json "json" | throwError "response has no 'json' field"
    return json
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting structured JSON: {error}"
  | _ =>
    throwError "Invalid response"

def codeFromJson [pipe: LeanAidePipe] (json: Json) : TermElabM (TSyntax ``commandSeq) := do
  let req := Json.mkObj [("task", "lean_from_json_structured"), ("json_structured", json)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok code := response.getObjValAs? String "lean_code" | throwError "response has no 'lean_code' field"
    parseCommands code
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while getting code from JSON: {error}"
  | _ =>
    throwError "Invalid response"

/-
structure CodeElabResult where
  declarations : List Name
  logs : List String
  sorries : List (Name × Expr)
  sorriesAfterPurge : List (Name × Expr)
-/
def elabCode [pipe: LeanAidePipe] (stx: TSyntax ``commandSeq) : TermElabM CodeElabResult := do
  let code ← printCommands stx
  let req := Json.mkObj [("task", "elaborate"), ("lean_code", code)]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok decls := response.getObjValAs? (List Name) "declarations" | throwError "response has no 'declarations' field"
    let .ok logs := response.getObjValAs? (List String) "logs" | throwError "response has no 'logs' field"
    let .ok sorries := response.getObjValAs? (List Json) "sorries" | throwError "response has no 'sorries' field"
    let sorries ←  sorries.mapM getSorriesFromJson
    let .ok sorriesAfterPurge := response.getObjValAs? (List Json) "sorries_after_purge" | throwError "response has no 'sorries_after_purge' field"
    let sorriesAfterPurge ← sorriesAfterPurge.mapM getSorriesFromJson
    return { declarations := decls, logs := logs, sorries := sorries, sorriesAfterPurge := sorriesAfterPurge }
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while elaborating code: {error}"
  | _ =>
    throwError "Invalid response"

def mathQuery [pipe: LeanAidePipe] (query: String) : CoreM (List String) := do
  let req := Json.mkObj [("task", "math_query"), ("query", query
  )]
  let response ← response req
  match response.getObjValAs? String "result" with
  | .ok "success" =>
    let .ok answers := response.getObjValAs? (List String) "answers" | throwError "response has no 'answers' field"
    return answers
  | .ok "error" =>
      let .ok error := response.getObjValAs? String "error" | throwError "response has no 'error' field"
      throwError s!"Error while performing math query: {error}"
  | _ =>
    throwError "Invalid response"

end LeanAidePipe

instance [LeanAidePipe] : Kernel where
  translateThm := LeanAidePipe.translateThm
  translateDef := LeanAidePipe.translateDef
  theoremDoc := LeanAidePipe.theoremDoc
  defDoc := LeanAidePipe.defDoc
  theoremName := LeanAidePipe.theoremName
  proveForFormalization := LeanAidePipe.proveForFormalization
  jsonStructured := LeanAidePipe.jsonStructured
  codeFromJson := LeanAidePipe.codeFromJson
  elabCode := LeanAidePipe.elabCode
  mathQuery := LeanAidePipe.mathQuery


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

def translateDef (text: String) : TermElabM (Except (Array CmdElabError) Syntax.Command) := do
  (← getKernelM).translateDef text

def theoremDoc (name: Name) (stx: Syntax.Command) : TermElabM String := do
  (← getKernelM).theoremDoc name stx

def defDoc (name: Name) (stx: Syntax.Command) : TermElabM String := do
  (← getKernelM).defDoc name stx

def theoremName (text: String) : MetaM Name := do
  (← getKernelM).theoremName text

def proveForFormalization (statement: String) (thm: Expr) : TermElabM String := do
  (← getKernelM).proveForFormalization statement thm

def jsonStructured (document: String) : MetaM Json := do
  (← getKernelM).jsonStructured document

def codeFromJson (json: Json) : TermElabM (TSyntax ``commandSeq) := do
  (← getKernelM).codeFromJson json


end KernelM

end LeanAide
