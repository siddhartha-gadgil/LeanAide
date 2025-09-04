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
  translateThm : String → TranslateM (Except (Array ElabError) Expr)
  translateDef : String → TranslateM (Except (Array CmdElabError) Syntax.Command)
  theoremDoc : Syntax.Command → TranslateM String
  defDoc : Syntax.Command → TranslateM String
  theoremName : Syntax.Command → IO Name
  prove : Name → Expr → TranslateM String
  structuredJson : String → IO Json
  codeFromJson? : String → IO (TSyntax ``commandSeq)
  elabCode : TSyntax ``commandSeq → TermElabM CodeElabResult


class LeanAidePipe where
  queryResponse : Json → IO Json

namespace LeanAidePipe

def fromURL (url: String) : LeanAidePipe := {
  queryResponse (data: Json) := do
    let output ← IO.Process.run {cmd := "curl", args := #[url, "-X", "POST", "-H", "Content-Type: application/json", "--data", data.compress]}
    let .ok response :=
      Json.parse output | IO.throwServerError "Failed to parse response"
    return response
}

def response [pipe: LeanAidePipe] (req: Json) : IO Json :=
  pipe.queryResponse req

def translateThm [pipe: LeanAidePipe] (text: String) : TranslateM (Except (Array ElabError) Expr) := do
  let req := Json.mkObj [("task", "translateThm"), ("text", text)]
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

end LeanAidePipe

macro "#leanaide_connect" url?:(str)? : command =>
match url? with
| some url => `(command| instance : LeanAidePipe := LeanAidePipe.fromURL $url)
| none => `(command| instance : LeanAidePipe := LeanAidePipe.fromURL "localhost:7654")

end LeanAide
