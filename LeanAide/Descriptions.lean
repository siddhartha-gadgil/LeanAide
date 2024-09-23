import LeanAide.ConstDeps
import LeanAide.TheoremElab
import LeanCodePrompts.ChatClient
open Lean Meta Elab

namespace LeanAide.Meta

def theoremAndDefs (name: Name) (depth: Nat := 2) : MetaM <|
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
        let defNames ← defsInTypeRec name type depth
        let defs ←  defNames.filterMapM <| fun n =>
          DefnTypes.defFromName? n
        let defViews := defs.map <| fun df => df.withDoc
        let defViews := defViews.filter fun df => df.length < 600
        return some (statement, defViews.toList)
    | _ => return none

def theoremStatement (name: Name) : MetaM <|
  Option (String) := do
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
        return some statement
    | _ => return none

def filteredNames (names: Array Name) : Array Name :=
  let common := [``Eq.mp, ``Eq.mpr, ``congrArg, ``id, ``Eq.refl, ``trans, ``of_eq_true, ``trans, ``rfl, `symm, ``eq_self, `Eq, ``congr, ``propext, ``funext, ``Exists.intro, `left, `right, ``Iff.rfl, ``iff_self, `CategoryTheory.Functor.toPrefunctor, ``forall_congr, ``Eq.rec, ``Eq.ndrec, `Iff, ``And.left, ``And.right, ``And.intro, ``And.elim, ``And.rec, ``implies_congr, `obj, `map, ``And, `app, `hom, ``Not, ``Exists, ``eq_true, `self, ``HEq, ``HEq.refl, `congr_arg, `congr_fun, ``Subtype.property, ``Iff.trans, ``False, ``eq_false, ``true, ``false, ``not_false_eq_true, ``Trans.trans, ``True, ``inferInstance, `Set.ext,
  `elim, `inst]
  names.filter fun n =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf n)) &&
    !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf n)) &&
    !common.contains n


def theoremAndLemmas (name: Name)
  (lemmaFilter : Array Name → Array Name := id) : MetaM <|
  Option (String × (Array String)) := do
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
        let consts := dfn.value.getUsedConstants
        let consts := consts.filter fun name =>
          !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name)) && !(excludeSuffixes.any (fun pfx => pfx.isSuffixOf name))
        let consts := consts.filter fun name =>
          ![``Eq.mp, ``Eq.mpr, ``congrArg, ``id].contains name
        let consts := lemmaFilter consts
        let lemmas ← consts.filterMapM theoremStatement
        return some (statement, lemmas)
    | _ => return none

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

-- #eval theoremPrompt ``List.length_cons

-- #eval theoremPrompt ``Nat.le_succ

-- #eval theoremPrompt ``Eq.subst

def getDescriptionM (name: Name)(server := ChatServer.openAI)(params: ChatParams) : MetaM <| Option (String × String) := do
  let prompt? ← theoremPrompt name
  prompt?.mapM fun (prompt, statement) => do
    let messages ← mkMessages prompt #[] (← sysPrompt)
    let fullJson ←  server.query messages params
    let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let contents ← getMessageContents outJson
    return (contents[0]!, statement)

-- #eval getDescriptionM ``Iff.rfl

def egFreq := Json.mkObj [("name", "Iff.rfl"), ("freq", 4882)]

def addDescription (js: Json)(server := ChatServer.openAI)(params: ChatParams) : MetaM (Json × Bool) := do
  let name? := js.getObjValAs? String "name"
  let modified? ← name?.mapM fun name => do
    let desc? ← getDescriptionM name.toName server params
    match desc? with
      | some (desc, statement) =>
        let newObj := Json.mkObj [("statement", statement), ("description", desc)]
        return (js.mergeObj newObj, true)
      | none => return (js, false)
  return modified?.toOption.getD (js, false)

-- #eval addDescription egFreq

def getDescriptionCore (name: Name)(server := ChatServer.openAI)(params: ChatParams := {}) : CoreM <| Option (String × String) :=
  (getDescriptionM name server params).run' {}

def addDescriptionCore (js: Json)(server := ChatServer.openAI)(params: ChatParams := {}) : CoreM (Json × Bool) :=
  (addDescription js server params).run' {}

def needsIndCore (name: Name) : CoreM <| Option (List Name)  :=
  (needsInd name).run' {}

def modulePairs : CoreM <| Array (Name × Array Name × Array String) := do
  let env ← getEnv
  let modData := env.header.moduleData
  let mods := env.header.moduleNames
  let internal := [`LeanAide, `LeanCodePrompts, `Scratch]
  let pairs := (mods.zip modData).filter fun (name, _) =>
    !internal.any (fun pre => pre.isPrefixOf name)
  let withDocs ←   pairs.mapM fun (name, data) => do
    let docs? := getModuleDoc? env name
    let docs := docs?.getD #[]
    let docs := docs.map <| fun md : ModuleDoc => md.doc
    return (name, data, docs)
  return withDocs.map
      (fun (name, data, docs) => (name, data.constNames, docs))

def descCachePath : IO System.FilePath := pure
  ("rawdata"/ "premises" / "ident_pairs"/"extra-descriptions.jsonl")

def getCachedDescriptions : IO (Array Json) := do
  let path ← descCachePath
  if ← path.pathExists then
    let lines ← IO.FS.lines path
    let jsons := lines.filterMap fun js => Json.parse js |>.toOption
    return jsons
  else return #[]

def cacheDescription (js: Json) : IO Unit := do
  let path ← descCachePath
  let jsStr := js.compress
  if ← path.pathExists then
    let h ← IO.FS.Handle.mk path IO.FS.Mode.append
    h.putStrLn jsStr
  else IO.FS.writeFile path (jsStr ++ "\n")

def getCachedDescriptionsMap : IO (HashMap String Json) := do
  let cached ← getCachedDescriptions
  let pairs := cached.filterMap fun js => do
    let name? := js.getObjValAs? String "name" |>.toOption
    name?.map fun name => (name, js)
  return pairs.foldl (init := {}) fun m (name, js) => m.insert name js

def getDescriptionCached (name: String)(server := ChatServer.openAI)(params: ChatParams)
  (cacheMap: HashMap String Json) : MetaM (Option Json) := do
  match cacheMap.find? name with
  | some js => return some js
  | none =>
    let desc? ← getDescriptionM name.toName server params
    match desc? with
      | some (desc, statement) =>
        let js := Json.mkObj [("name", name),
          ("statement", statement), ("description", desc)]
        cacheDescription js
        return some js
      | none => return none

def getDescriptionCachedCore (name: String)(server := ChatServer.openAI)(params: ChatParams := {})
  (cacheMap: HashMap String Json) : CoreM (Option Json) :=
  (getDescriptionCached name server params cacheMap).run' {}

def lemmaUserPrompt' (name: Name)(description: String) :
  MetaM <| Option String := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let thm ← ppExpr type
        let thm := thm.pretty
        fromTemplate "suggest_lemma"
          [("description", description), ("theorem", thm), ("name", name.toString)]
    | _ => return none

/--
If theorem type is known, which is the case for nearest embeddings.
-/
def lemmaUserPrompt (name: Name)(thm description: String) :
  IO <| String := do
      fromTemplate "suggest_lemma"
          [("description", description), ("theorem", thm), ("name", name.toString)]


def lemmaChatExamples (name: Name)(description: String) : MetaM <|
  Option (Array ChatExample) := do
  let env ← getEnv
  let info? := env.find? name
  match info? with
    | some (.thmInfo dfn) =>
        let type := dfn.type
        let thm ← ppExpr type
        let thm := thm.pretty
        let consts := dfn.value.getUsedConstants
        let consts := filteredNames consts
        let lemmas ← consts.filterMapM theoremStatement
        let userPrompt ← lemmaUserPrompt name thm description
        return some <| lemmas.map fun l =>
          {user := userPrompt, assistant := l}
    | _ => return none

def allLemmaChatExamples (pairs: List (Name × String)) : MetaM <|
  Array ChatExample := do
  let examples ← pairs.filterMapM fun (name, desc) =>
    lemmaChatExamples name desc
  return examples.foldl (init := #[]) (· ++ ·)

def selectedChatExamples (n: Nat) (pairs: List (Name × String)) : MetaM <|
  List ChatExample := do
  let examples ← allLemmaChatExamples pairs
  List.range n |>.mapM fun _ => do
    let i ← IO.rand 0 (examples.size - 1)
    pure <| examples.get! i

def lemmaChatMessageM? (name: Name)(description: String)(n: Nat)
  (lemmaPairs: List (Name × String)) : MetaM <| Option Json := do
  let examples ← selectedChatExamples n lemmaPairs
  let query? ← lemmaUserPrompt' name description
  let sys ← sysPrompt
  query?.mapM fun query =>
    mkMessages query examples.toArray sys

def lemmaChatQueryM? (name: Name)(description: String)(n: Nat)
  (lemmaPairs: List (Name × String)) : MetaM <| Option (Array String × String × Array String) := do
  let messages? ← lemmaChatMessageM? name description n lemmaPairs
  let thmLemmas? ← theoremAndLemmas name filteredNames
  let server := ChatServer.azure
  let params : ChatParams := {n := 12, temp := 1.2}
  match (messages?, thmLemmas?) with
  | (some messages, some (thm, lemmas)) =>
    let fullJson ←  server.query messages params
    let outJson :=
        (fullJson.getObjVal? "choices").toOption.getD (Json.arr #[])
    let contents ←  getMessageContents outJson
    return some (contents, thm, lemmas)
  | _ => return none

def lemmaChatQueryCore? (name: Name)(description: String)(n: Nat)
  (lemmaPairs: List (Name × String)) :
    CoreM <| Option (Array String × String × Array String) :=
  (lemmaChatQueryM? name description n lemmaPairs).run' {}

end LeanAide.Meta
