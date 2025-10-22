import Lean
import LeanAideCore.Aides

namespace LeanAide

namespace JsonSchemas

open Lean Json

abbrev Description := String

partial def getDefs (js: Json) : Array String :=
  let head := "#/$defs/"
  match js with
  | Json.str s =>
    if s.startsWith head then
      #[(s.drop head.length)]
    else
      #[]
  | Json.obj kvs =>
    let values := kvs.toArray.map (·.2)
    values.foldl (fun r v => r ++ getDefs v) #[] |>.eraseReps
  | Json.arr js =>
    js.foldl (fun r j => r ++ getDefs j) #[] |>.eraseReps
  | _ => #[]


structure SchemaData where
  schemaElements : Std.HashMap String Json := {}
  anyOfGroupDescs : Std.HashMap String Description := {}
  anyOfGroupMembers : Std.HashMap String (Array String) := {}
  deriving Inhabited, Repr

inductive AddToSchemaData where
  | schemaElement (label: String) (schema : Json) (groups: Array String) : AddToSchemaData
  | anyOfGroup (groupId : String) (desc : Option Description) (members : Array String := #[]) : AddToSchemaData
  | addToGroup (groupId : String) (members : Array String) : AddToSchemaData
  deriving Inhabited
open AddToSchemaData

namespace SchemaData

def addMemberToGroup (st : SchemaData) (groupId : String) (member : String) : SchemaData :=
  let updatedMembers :=
    match st.anyOfGroupMembers.get? groupId with
    | some members => members.push member
    | none => #[member]
  { st with anyOfGroupMembers := st.anyOfGroupMembers.insert groupId updatedMembers }

def addMemberToGroups (st : SchemaData) (groupIds : Array String) (member : String) : SchemaData :=
  groupIds.foldl (init := st) fun st gid => st.addMemberToGroup gid member

def add (st : SchemaData) (atst : AddToSchemaData) : SchemaData :=
  match atst with
  | schemaElement label schema groups =>
    { st with schemaElements := st.schemaElements.insert label schema } |>.addMemberToGroups groups label
  | anyOfGroup groupId desc? members =>
    { st with
      anyOfGroupDescs :=
        match desc? with
        | some desc => st.anyOfGroupDescs.insert groupId desc
        | none => st.anyOfGroupDescs
      anyOfGroupMembers := st.anyOfGroupMembers.insert groupId members }
  | addToGroup groupId members =>
    let updatedMembers :=
      match st.anyOfGroupMembers.get? groupId with
      | some existingMembers => existingMembers ++ members
      | none => members
    { st with anyOfGroupMembers := st.anyOfGroupMembers.insert groupId updatedMembers }

def groupJson? (data : SchemaData) (groupId : String) : Option Json :=
  data.anyOfGroupMembers.get? groupId |>.map fun members =>
  let refs := members.map (fun m => mkObj [("$ref", s!"#/$defs/{m}")])
  let desc? := data.anyOfGroupDescs.get? groupId
  match desc? with
  | some desc =>  mkObj [("description", desc), ("anyOf", toJson refs)]
  | none => mkObj [("anyOf", toJson refs)]

def groupJsonDef? (data : SchemaData) (groupId : String) :
Option Json :=
  groupJson? data groupId |>.map fun groupJson =>
  mkObj [(groupId, groupJson)]

def elementJson? (data : SchemaData) (elem: String) : Option Json :=
  data.schemaElements.get? elem

def elementJsonDef? (data : SchemaData) (elem: String) : Option Json :=
  data.schemaElements.get? elem |>.map fun schema =>
  mkObj [(elem, schema)]

def jsonDef? (data: SchemaData) (label: String) : Option Json :=
  match data.elementJsonDef? label with
  | some elemDef => some elemDef
  | none => data.groupJsonDef? label

def labelJson? (data: SchemaData) (label: String) : Option Json :=
  match data.elementJson? label with
  | some elem => some elem
  | none => data.groupJson? label

/--
Getting definitions recursively, starting from the given names. Here
* `upperNames` are names that should not be included in the result (e.g., because they are
  already included in the schema being built);
* `accum` are names that have already been found in the recursion;
* `names` are names to be processed in this step of the recursion.
-/
partial def getAllDefsAux (data: SchemaData) (upperNames : Array String) (accum : Array String) (names: Array String) : Array String :=
  let jsons := names.foldl (init := #[]) fun js n =>
    match data.labelJson? n with
    | some j => js.push j
    | none => js
  let newNames := jsons.foldl (init := #[]) fun ns j => ns ++ getDefs j |>.eraseReps
  let newNames := newNames.filter (fun n => !(upperNames ++ accum ++ names).contains n)
  if newNames.isEmpty then
    accum ++ names
  else
    getAllDefsAux data upperNames (accum ++ names) newNames

def getAllDefsFrom (data: SchemaData) (top: Json) (upperNames: Array String := #[]) : Array String :=
  getAllDefsAux data upperNames #[] (getDefs top |>.eraseReps)

end SchemaData

initialize jsonSchemasExt :
  SimpleScopedEnvExtension AddToSchemaData SchemaData ←
  registerSimpleScopedEnvExtension {
    initial := {}, addEntry := SchemaData.add }

def SchemaData.get : MetaM SchemaData := do
  let env ← getEnv
  return jsonSchemasExt.getState env

def schemaGroupMembers (groupId : String) : MetaM (Option (Array String)) := do
  let data ← SchemaData.get
  return data.anyOfGroupMembers.get? groupId

def schemaElementJson? (label: String) : MetaM (Option Json) := do
  let data ← SchemaData.get
  return data.elementJson? label

def schemaElementsList : MetaM (Array String) := do
  let data ← SchemaData.get
  return data.schemaElements.keys.toArray

def groupList : MetaM (Array String) := do
  let data ← SchemaData.get
  return data.anyOfGroupMembers.keys.toArray

def getAllDefLabelsFrom (top: Json) (upperNames: Array String := #[]) : MetaM (Array String) := do
  let data ← SchemaData.get
  return data.getAllDefsFrom top upperNames

def getAllDefJsonsFrom (top: Json) (upperNames: Array String := #[]) : MetaM (Json) := do
  let data ← SchemaData.get
  let labels := data.getAllDefsFrom top upperNames |>.toList
  return Json.mkObj <| labels.filterMap (fun l => data.labelJson? l |>.map (fun j => (l, j)))

def withAllDefs (top: Json) (upperNames: Array String := #[]) : MetaM Json := do
  let defList ← getAllDefJsonsFrom top upperNames
  let defs := mkObj [("$defs", defList)]
  return top.mergeObj defs

elab "schema_element%" n:ident : term => do
  let label := n.getId.toString
  let data ← SchemaData.get
  match data.elementJson? label with
  | some js => jsonToExpr js
  | none => throwError "No schema element named '{label}'"

elab "#schema_group" n:ident desc:str "with" "[" ms:ident,* "]" : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := desc.getString
  let membersExpr := ms.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.anyOfGroup groupId descVal membersExpr)

elab "#schema_group" n:ident desc:str  : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := desc.getString
  jsonSchemasExt.add (.anyOfGroup groupId descVal #[])

elab "#schema_group" n:ident "with" "[" ms:ident,* "]" : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := none
  let membersExpr := ms.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.anyOfGroup groupId descVal membersExpr)

elab "#schema_group" n:ident   : command => Elab.Command.liftTermElabM do
  let groupId := n.getId.toString
  let descVal := none
  jsonSchemasExt.add (.anyOfGroup groupId descVal #[])

elab "#schema_group" n:str desc:str "with" "[" ms:str,* "]" : command => Elab.Command.liftTermElabM do
  let groupId := n.getString
  let descVal := desc.getString
  let membersExpr := ms.getElems.map (·.getString)
  jsonSchemasExt.add (.anyOfGroup groupId descVal membersExpr)

elab "#schema_group" n:str desc:str  : command => Elab.Command.liftTermElabM do
  let groupId := n.getString
  let descVal := desc.getString
  jsonSchemasExt.add (.anyOfGroup groupId descVal #[])

elab "#schema_group" n:str "with" "[" ms:str,* "]" : command => Elab.Command.liftTermElabM do
  let groupId := n.getString
  let descVal := none
  let membersExpr := ms.getElems.map (·.getString)
  jsonSchemasExt.add (.anyOfGroup groupId descVal membersExpr)

elab "#schema_group" n:str   : command => Elab.Command.liftTermElabM do
  let groupId := n.getString
  let descVal := none
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

elab "#schema_element" n:str  "in" "[" gs:ident,* "]" ":=" schema:term : command => Elab.Command.liftTermElabM do
  let label := n.getString
  let schemaVal ← Elab.Term.elabTerm schema (mkConst ``Json)
  let schemaJson ← unsafe evalExpr Json (mkConst ``Json) schemaVal
  let groupIds := gs.getElems.map (·.getId.toString)
  jsonSchemasExt.add (.schemaElement label schemaJson groupIds)

elab "#schema_element" n:str ":=" schema:term : command => Elab.Command.liftTermElabM do
  let label := n.getString
  let schemaVal ← Elab.Term.elabTerm schema (mkConst ``Json)
  let schemaJson ← unsafe evalExpr Json (mkConst ``Json) schemaVal
  jsonSchemasExt.add (.schemaElement label schemaJson #[])


end JsonSchemas

end LeanAide
