import LeanAideCore.PromptExampleBuilder
import LeanAideCore.ChatClient
import LeanAideCore.TranslateM
import Lean
open Lean

namespace LeanAide
variable [LeanAideBaseDir]

open Translate
inductive RelevantDefs where
  | select (bound? : Option Nat) : RelevantDefs
  | closure (num : Nat)(depth: Nat := 1) : RelevantDefs
  | env : RelevantDefs
  | data (d: Array (Name × String)) : RelevantDefs
  | seq : List RelevantDefs → RelevantDefs
  deriving Repr, FromJson, ToJson

instance : Append RelevantDefs where
  append := fun x y =>
    match x, y with
    | RelevantDefs.seq xs, RelevantDefs.seq ys => RelevantDefs.seq <| xs ++ ys
    | RelevantDefs.seq xs, y => RelevantDefs.seq <| xs ++ [y]
    | x, RelevantDefs.seq ys => RelevantDefs.seq <|  x :: ys
    | x, y => RelevantDefs.seq [x, y]

instance : HAppend RelevantDefs (Array (Name × String)) RelevantDefs where
  hAppend x y := x ++ RelevantDefs.data y

def RelevantDefs.empty := RelevantDefs.seq []

def RelevantDefs.base := RelevantDefs.env

def RelevantDefs.addDefs (nbs: Array (Name × String)) (nbd: RelevantDefs) : RelevantDefs :=
  nbd ++ nbs

open LeanAide

partial def RelevantDefs.names (nbd: RelevantDefs)(s: String) (pairs : Array (String × Json)) : TranslateM (Array Name) := do
  match nbd with
  | RelevantDefs.select bound? =>
    let pairs := pairs.filter fun (doc, _) => match bound? with
      | some bound => doc.length < bound
      | none => true
    return pairs.filterMap fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
  | RelevantDefs.closure num depth =>
    let searchNames : Array Name := pairs.filterMap (fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
    )
    bestDefsInConsts num searchNames.toList depth
  | RelevantDefs.env => do
    let env ← get
    return env.defs.map (·.name)
  | .data d => return d.map (·.1)
  | RelevantDefs.seq nbs => do
    let names ← nbs.mapM fun nb => nb.names s pairs
    return names.toArray.flatten

partial def RelevantDefs.blob (nbd: RelevantDefs)(s: String) (pairs : Array (String × Json)) : TranslateM (Array String) := do
  match nbd with
  | RelevantDefs.select bound? =>
    let pairs := pairs.filter fun (doc, _) => match bound? with
      | some bound => doc.length < bound
      | none => true
    return pairs.filterMap fun (doc, js) =>
      fullStatement? js |>.map fun s => s!"/-- {doc} -/" ++ "\n" ++ s
  | RelevantDefs.closure num depth =>
    let searchNames : Array Name := pairs.filterMap (fun (_, js) => do
      js.getObjValAs? Name "name" |>.toOption
    )
    let names ← bestDefsInConsts num searchNames.toList depth
    names.filterMapM fun n => do
      let info ← getConstInfo n
      let doc? ← findDocString? (← getEnv) n
      match doc? with
      | some doc =>
        let value? ← info.value?.mapM fun e => PrettyPrinter.delab e
        mkStatementWithDoc n
          (← PrettyPrinter.delab info.type) value? false (doc := doc) (isNoncomputable := Lean.isNoncomputable (← getEnv) n)
      | none =>
        mkStatement n (← PrettyPrinter.delab info.type) none false
  | RelevantDefs.env => do
    defsBlob
  | .data d => return d.map (·.2)
  | RelevantDefs.seq nbs => do
    let names ← nbs.mapM fun nb => nb.blob s pairs
    return names.toArray.flatten


def translatePromptPairs (docPairs: Array (String × Json))
      : Array (String × Json) :=
  docPairs.map fun (doc, thm) =>
    let isThm :=
      thm.getObjValAs? Bool "isProp" |>.toOption |>.getD true
    let head := if isThm then "Theorem" else "Definition"
    (s!"Translate the following statement into Lean 4:\n## {head}: " ++ doc ++ "\n\nGive ONLY the Lean code", thm)

def translateMessages (s: String)(promptPairs: Array (String × Json))
      (header: String) (dfns: Array String) (toChat : ChatExampleType)
      (sysPrompt: Bool) : TranslateM Json := do
  let examples ←  promptPairs.filterMapM fun pair =>
    toChat.map? pair
  let preludeCode :=
    if dfns.isEmpty then ""
    else
        let defsBlob := dfns.foldr (fun acc df => acc ++ "\n\n" ++ df) ""
        s!"Your goal is to translate from natural language to Lean. The following are some definitions that may be relevant:\n\n{defsBlob}"

  trace[Translate.info] m!"examples: \n{(examples).size}"
  let s' := preludeCode ++ s!"Translate the following statement into Lean 4:\n## {header}: " ++ s ++ "\n\nGive ONLY the Lean code"
  mkMessages s' examples (← transPrompt) !sysPrompt

/--
Structure collecting together parameters used in translation.
-/
structure Translator where
  /-- The LLM server being used. -/
  server : ChatServer := .default
  /-- Parameters for the LLM server called. -/
  params : ChatParams := {n := 8}
  /-- Builder for prompt examples given sentence. -/
  pb : PromptExampleBuilder := .default
  /-- Chat examples, i.e., the dialogues of `user` and `assistant`, from the examples. -/
  toChat : ChatExampleType := .simple
  /-- Relevant definitions to include in the prompt -/
  relDefs : RelevantDefs := .empty
  /-- Whether to do a roundtrip test -/
  roundTrip : Bool := false
  /-- Whether to select the first elaboration that passes a roundtrip-/
  roundTripSelect : Bool := false -- selecting first to pass roundtrip
  reasoningServer : ChatServer := .openAI "o3-mini"
deriving Repr, FromJson, ToJson

def Translator.forDef (t: Translator)  : Translator :=
  let chat : ChatExampleType := match t.toChat with
  | .simple => .doc
  | .detailed => .detailedDoc
  | x => x
  {t with toChat := chat}

def Translator.reasoning (t: Translator) : Translator :=
  {t with params := {t.params with n := 1, temp := 1.0}}

/--
Structure collecting together parameters used in code generation.
-/
structure CodeGenerator extends Translator where
  numLeanSearch : Nat := 6
  numMoogle : Nat := 6
  numLeanSearchDirect : Nat := 2
  numMoogleDirect : Nat := 2
deriving Repr, FromJson, ToJson

def Translator.codeGenerator (t: Translator) : CodeGenerator := {t with}

def CodeGenerator.default : CodeGenerator :=
  {}
-- #eval toJson <| ({} : CodeGenerator)
-- #eval (fromJson? (toJson <| ({} : CodeGenerator)) : Except _ Translator)
