import Lean
import LeanAideCore.Aides

namespace LeanAide

namespace JsonSchemas

open Lean Json

abbrev Description := String

structure State where
  schemaElements : Std.HashMap String Json := {}
  anyOfGroupDescs : Std.HashMap String Description := {}
  anyOfGroupMembers : Std.HashMap String (Array String) := {}
  deriving Inhabited, Repr

inductive AddToState where
  | schemaElement (label: String) (schema : Json) (groups: Array String) : AddToState
  | anyOfGroup (groupId : String) (desc : Description) (members : Array String := #[]) : AddToState
  | addToGroup (groupId : String) (members : Array String) : AddToState
  deriving Inhabited
open AddToState

namespace State

def addMemberToGroup (st : State) (groupId : String) (member : String) : State :=
  let updatedMembers :=
    match st.anyOfGroupMembers.get? groupId with
    | some members => members.push member
    | none => #[member]
  { st with anyOfGroupMembers := st.anyOfGroupMembers.insert groupId updatedMembers }

def addMemberToGroups (st : State) (groupIds : Array String) (member : String) : State :=
  groupIds.foldl (init := st) fun st gid => st.addMemberToGroup gid member

def add (st : State) (atst : AddToState) : State :=
  match atst with
  | schemaElement label schema groups =>
    { st with schemaElements := st.schemaElements.insert label schema } |>.addMemberToGroups groups label
  | anyOfGroup groupId desc members =>
    { st with
      anyOfGroupDescs := st.anyOfGroupDescs.insert groupId desc
      anyOfGroupMembers := st.anyOfGroupMembers.insert groupId members }
  | addToGroup groupId members =>
    let updatedMembers :=
      match st.anyOfGroupMembers.get? groupId with
      | some existingMembers => existingMembers ++ members
      | none => members
    { st with anyOfGroupMembers := st.anyOfGroupMembers.insert groupId updatedMembers }


end State

initialize jsonSchemasExt :
  SimpleScopedEnvExtension AddToState State ←
  registerSimpleScopedEnvExtension {
    initial := {}, addEntry := State.add }

def State.get : MetaM State := do
  let env ← getEnv
  return jsonSchemasExt.getState env


elab "#schema_group" n:ident desc:str "with" "[" ms:ident,* "]" : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := desc.getString
  let membersExpr := ms.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.anyOfGroup groupId descVal membersExpr)

elab "#schema_group" n:ident desc:str  : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := desc.getString
  jsonSchemasExt.add (.anyOfGroup groupId descVal #[])

elab "#add_to_schema_group" n:ident m:ident,* : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let members := m.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.addToGroup groupId members)

open Meta Elab Term

elab "#schema_element" n:ident  "in" "[" gs:ident,* "]" ":=" schema:term : command => Elab.Command.liftTermElabM do
  let label := n.getId.toString
  let schemaVal ← Elab.Term.elabTerm schema (mkConst ``Json)
  let schemaJson ← unsafe evalExpr Json (mkConst ``Json) schemaVal
  let groupIds := gs.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.schemaElement label schemaJson groupIds)

elab "#schema_element" n:ident ":=" schema:term : command => Elab.Command.liftTermElabM do
  let label := n.getId.toString
  let schemaVal ← Elab.Term.elabTerm schema (mkConst ``Json)
  let schemaJson ← unsafe evalExpr Json (mkConst ``Json) schemaVal
  jsonSchemasExt.add (.schemaElement label schemaJson #[])

end JsonSchemas

end LeanAide
