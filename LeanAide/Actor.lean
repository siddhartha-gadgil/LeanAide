import LeanAide.TranslatorParams
import LeanCodePrompts.Translate

namespace LeanAide.Actor
open LeanAide Lean

-- dummy for now
def response (data: Json) (translator : Translator) : TranslateM Json :=
  let result := Json.mkObj [("result", "success"), ("data", data)]
  return result

end LeanAide.Actor
