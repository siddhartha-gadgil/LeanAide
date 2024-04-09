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


def theoremPrompt (name: Name) : MetaM <| Option String := do
  (← theoremAndDefs name).mapM fun (statement, dfns) =>
    if dfns.isEmpty then
      fromTemplate "describe_theorem" [("theorem", statement)]
    else
      let defsBlob := dfns.foldr (fun acc df => acc ++ "\n\n" ++ df) ""
      fromTemplate "describe_theorem_with_defs" [("theorem", statement), ("definitions", defsBlob.trim)]

#eval theoremPrompt ``List.length_cons

#eval theoremPrompt ``Nat.le_succ

#eval theoremPrompt ``Eq.subst

def getDescriptionM (name: Name) : MetaM <| Option String := do
  let prompt? ← theoremPrompt name
  let server := ChatServer.azure
  prompt?.mapM fun prompt => do
    let messages ← GPT.mkMessages prompt #[] (← sysPrompt)
    let fullJson ←  server.query messages {}
    let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let contents ← getMessageContents outJson
    return contents[0]!

-- #eval getDescriptionM ``Iff.rfl

def egFreq := Json.mkObj [("name", "Iff.rfl"), ("freq", 4882)]

def addDescription (js: Json) : MetaM Json := do
  let name? := js.getObjValAs? String "name"
  let modified? ← name?.mapM fun name => do
    let desc? ← getDescriptionM name.toName
    match desc? with
      | some desc =>
        let newObj := Json.mkObj [("description", desc)]
        return js.mergeObj newObj
      | none => return js
  return modified?.toOption.getD js

-- #eval addDescription egFreq

def getDescriptionCore (name: Name) : CoreM <| Option String :=
  (getDescriptionM name).run' {}

def addDescriptionCore (js: Json) : CoreM Json :=
  (addDescription js).run' {}

end LeanAide.Meta
