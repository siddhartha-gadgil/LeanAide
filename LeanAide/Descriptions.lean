import LeanAide.ConstDeps
import LeanAide.TheoremElab
import LeanCodePrompts.ChatClient
open Lean Meta Elab

namespace LeanAide.Meta

def theoremAndDefs (name: Name) : MetaM <|
  Option (String × (List String)) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let statement ←
          mkStatement (some name) typeStx valueStx? true
        let doc? ← findDocString? env name
        let statement := match doc? with
          | some doc => s!"/-- {doc} -/\n" ++ statement
          | none => statement
        let defNames := idents typeStx |>.eraseDups
        let defs ←  defNames.filterMapM <| fun n =>
          DefnTypes.defFromName? n.toName
        let defViews := defs.map <| fun df => df.withDoc
        let defViews := defViews.filter fun df => df.length < 600
        return some (statement, defViews)
    | _ => return none

#eval theoremAndDefs ``List.length_cons


def theoremPrompt (name: Name) : MetaM <| Option (String × String) := do
  (← theoremAndDefs name).mapM fun (statement, dfns) =>
    if dfns.isEmpty then
      return (← fromTemplate "describe_theorem" [("theorem", statement)], statement)
    else
      let defsBlob := dfns.foldr (fun acc df => acc ++ "\n\n" ++ df) ""
      return (← fromTemplate "describe_theorem_with_defs" [("theorem", statement), ("definitions", defsBlob.trim)],
      statement)

def needsInd (name: Name) : MetaM <| Option (List Name) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let typeStx ← PrettyPrinter.delab type
        let valueStx? := none
        let _ ←
          mkStatement (some name) typeStx valueStx? true
        let defNames := idents typeStx |>.eraseDups
        let defs ←  defNames.filterMapM <| fun n =>
          DefnTypes.defFromName? n.toName
        if defs.isEmpty then
          let inds ←  defNames.filterMapM <| fun n =>
            InductiveTypes.fromName? n.toName
          let ctors ←  defNames.filterMapM <| fun n =>
            ConstructorTypes.fromName? n.toName
          let names := inds.map (·.name) ++ ctors.map (·.name)
          let names:= names.filter (fun n => !(``Nat).isPrefixOf n)
          if names.isEmpty then return none
          else return some names
        else return none
    | _ => return none

#eval theoremPrompt ``List.length_cons

#eval theoremPrompt ``Nat.le_succ

#eval theoremPrompt ``Eq.subst

def getDescriptionM (name: Name) : MetaM <| Option (String × String) := do
  let prompt? ← theoremPrompt name
  let server := ChatServer.azure
  prompt?.mapM fun (prompt, statement) => do
    let messages ← GPT.mkMessages prompt #[] (← sysPrompt)
    let fullJson ←  server.query messages {}
    let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let contents ← getMessageContents outJson
    return (contents[0]!, statement)

-- #eval getDescriptionM ``Iff.rfl

def egFreq := Json.mkObj [("name", "Iff.rfl"), ("freq", 4882)]

def addDescription (js: Json) : MetaM (Json × Bool) := do
  let name? := js.getObjValAs? String "name"
  let modified? ← name?.mapM fun name => do
    let desc? ← getDescriptionM name.toName
    match desc? with
      | some (desc, statement) =>
        let newObj := Json.mkObj [("statement", statement), ("description", desc)]
        return (js.mergeObj newObj, true)
      | none => return (js, false)
  return modified?.toOption.getD (js, false)

-- #eval addDescription egFreq

def getDescriptionCore (name: Name) : CoreM <| Option (String × String) :=
  (getDescriptionM name).run' {}

def addDescriptionCore (js: Json) : CoreM (Json × Bool) :=
  (addDescription js).run' {}

def needsIndCore (name: Name) : CoreM <| Option (List Name)  :=
  (needsInd name).run' {}

def modulePairs : CoreM <| Array (Name × Array Name) := do
  let env ← getEnv
  let modData := env.header.moduleData
  let mods := env.header.moduleNames
  let internal := [`LeanAide, `LeanCodePrompts, `Scratch]
  let pairs := (mods.zip modData).filter fun (name, _) =>
    !internal.any (fun pre => pre.isPrefixOf name)
  return pairs.map (fun (name, data) => (name, data.constNames))

end LeanAide.Meta
