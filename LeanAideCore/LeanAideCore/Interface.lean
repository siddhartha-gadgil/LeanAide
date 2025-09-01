import Lean
import LeanAideCore.Aides
import LeanAideCore.TranslateM
import LeanAideCore.Translator


open Lean Meta Elab Term

namespace LeanAide

open Translate

/--
The core functions of LeanAide, implemented directly in the server and via querying in the client.
-/
class Interface where
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
