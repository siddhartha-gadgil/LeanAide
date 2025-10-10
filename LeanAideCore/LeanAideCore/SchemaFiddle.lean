import LeanAideCore.Resources
import LeanAideCore.JsonSchemas
open Lean Meta

-- temporary exploration and code generation

def defs := LeanAide.Resources.paperStructure.getObjVal?  "$defs" |>.toOption.get!

def defsList' := defs.getObj?.toOption.map (·.toArray) |>.get!
def defsList := defsList'.map (fun ⟨k, v⟩  => (k, v))

def purgeDefs : Json :=
  let rbNode? := LeanAide.Resources.paperStructure.getObj?.toOption
  match rbNode? with
  | some rbNode =>
    let filtered := rbNode.toArray.filter (fun ⟨k, _⟩ => k != "$defs")
    let filtered : Array (String × Json) := filtered.map (fun ⟨k, v⟩ => (k, v))
    Json.mkObj filtered.toList
  | none =>
    panic! "purgeDefs: not an object: {defs}"

#eval defs.getObjVal? "Section"

#eval defsList

def mkElem (name: String) (json: Json) : String := s!"#schema_element \"{name}\" := json% {json.pretty}"

#eval mkElem "Section" <| (defs.getObjVal?  "Section").toOption.get!

open Elab Tactic
elab h:"#sec_command" : command =>
  Command.liftTermElabM do
    let s := mkElem "Section" <| (defs.getObjVal?  "Section").toOption.get!
    TryThis.addSuggestion h s

#sec_command

elab h:"#schema_commands" : command =>
  Command.liftTermElabM do
    let mut s := ""
    for (k, v) in defsList do
      s := s ++ mkElem k v ++ "\n\n"
    TryThis.addSuggestion h s
#schema_commands

#eval purgeDefs.pretty

elab h:"#schema_head" : command =>
  Command.liftTermElabM do
    let s := "def schemaHead : Json := json% " ++ purgeDefs.pretty
    TryThis.addSuggestion h s

#schema_head
