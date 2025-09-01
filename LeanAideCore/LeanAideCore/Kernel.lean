import Lean
import LeanAideCore.Aides
import LeanAideCore.TranslateM
import LeanAideCore.Translator


open Lean Meta Elab Term

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
  translateThm? : Translator → String → TranslateM (Except (Array ElabError) Expr)
  translateDef? : Translator → String → TranslateM (Except (Array CmdElabError) Syntax.Command)
  theoremDoc? : Translator → Syntax.Command → TranslateM (Except String String)
  defDoc? : Translator → Syntax.Command → TranslateM (Except String String)
  theoremName? : ChatServer → Syntax.Command → IO (Except String Name)
  prove? : ChatServer → Name → Expr → TranslateM (Except String String)
  structuredJson? : ChatServer → String → IO (Except String Json)
  codeFromJson? : ChatServer → String → IO (Except String (TSyntax ``commandSeq))
  codeElabResult? : TSyntax ``commandSeq → TermElabM (Except String CodeElabResult)

/--
# Markdown in DocStrings

Yes, it works.
-/
def HelloWorld : String :=
  "Hello from LeanAideCore!"

end LeanAide
