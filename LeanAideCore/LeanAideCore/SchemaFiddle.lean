import LeanAideCore.Resources
import LeanAideCore.JsonSchemas
open Lean Meta

-- temporary exploration and code generation

def defs := LeanAide.Resources.paperStructure.getObjValAs? (Json) "$defs" |>.toOption.get!

def defsList' := defs.getObj?.toOption.map (·.toArray) |>.get!
def defsList := defsList'.map (fun ⟨k, v⟩  => (k, v))

#eval defs.getObjVal? "Section"

#eval defsList

def mkElem (name: String) (json: Json) : String := s!"#schema_element {name} := json% {json.pretty}"

#eval mkElem "Section" <| (defs.getObjVal?  "Section").toOption.get!

open Elab Tactic
elab h:"#sec_command" : command =>
  Command.liftTermElabM do
    let s := mkElem "Section" <| (defs.getObjVal?  "Section").toOption.get!
    TryThis.addSuggestion h s

#sec_command
