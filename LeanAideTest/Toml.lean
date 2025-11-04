import LeanAideCore.Aides.Toml
import LeanAideCore.Translator
import LeanAide.JsonDiff

open Lean

namespace LeanAide

#eval loadTomlAsJson? "lakefile.toml"

#eval loadTomlAsJson? "leanaide.toml"

def roundtrip : IO Lake.Toml.Value := do
  let .some json ← loadTomlAsJson? "lakefile.toml" | IO.throwServerError "Could not load lakefile.toml"
  let toml := Toml.ofJson json
  return toml

def checkRoundtrip : IO (List JsonDiff) := do
  let .some json₁ ← loadTomlAsJson? "leanaide.toml" | IO.throwServerError "Could not load leanaide.toml"
  let translator : Translator := {}
  let json₂ := Json.mkObj [("translator", toJson translator)]
  let diff := jsonDiff json₁ json₂
  return diff

/--
info: [LeanAide.JsonDiff.atKey
   "translator"
   (LeanAide.JsonDiff.atKey
     "params"
     (LeanAide.JsonDiff.atKey "temp" (LeanAide.JsonDiff.message "one has number 1 and another has number 1"))),
 LeanAide.JsonDiff.atKey
   "translator"
   (LeanAide.JsonDiff.atKey
     "reasoningServer"
     (LeanAide.JsonDiff.atKey "openAI" (LeanAide.JsonDiff.existsKey2only "authHeader?" "null"))),
 LeanAide.JsonDiff.atKey
   "translator"
   (LeanAide.JsonDiff.atKey
     "server"
     (LeanAide.JsonDiff.atKey "openAI" (LeanAide.JsonDiff.existsKey2only "authHeader?" "null")))]
-/
#guard_msgs in
#eval checkRoundtrip

-- #eval writeTranslatorJson

end LeanAide
