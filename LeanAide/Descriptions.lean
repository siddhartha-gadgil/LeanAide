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

end LeanAide.Meta
