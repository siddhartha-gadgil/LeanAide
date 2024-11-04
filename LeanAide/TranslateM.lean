import Lean
import LeanAide.Aides
import Batteries.Util.Pickle
import LeanAide.SimpleFrontend
import LeanAide.ConstDeps
import LeanAide.PremiseData
import LeanAide.PromptExampleBuilder
import LeanCodePrompts.ChatClient

open Lean Meta Elab Term
namespace LeanAide

structure DefSource where
  doc : String
  isProp : Bool
deriving ToJson, FromJson, Repr

structure DefWithDoc extends DefData where
  doc : String

inductive ElabError : Type where
| unparsed (text parseError: String) (context? : Option String) : ElabError
| parsed (text elabError : String) (cmdErrors : List String)
    (context? : Option String) : ElabError
deriving Repr, ToJson, FromJson

instance : ToMessageData (ElabError) where
  toMessageData (err) := match err with
  | .unparsed text parseError _ => m!"Parsing error: {parseError} for {text}"
  | .parsed text elabError cmdErrors _ =>
      m!"Elaboration errors : {elabError} for {text}; front-end errors: {cmdErrors}"

structure ElabErrorData where
  source : String
  prompt? : Option Json
  elabErrors : Array ElabError
deriving FromJson, ToJson, Repr

inductive CmdElabError : Type where
| unparsed (text parseError: String) (context? : Option String) : CmdElabError
| parsed (text : String) (cmdErrors : List String)
    (context? : Option String) : CmdElabError
deriving Repr, ToJson, FromJson

inductive DefTranslateResult : Type where
  | success (dfns : Array DefWithDoc) : DefTranslateResult
  | failure
    (progress : Array DefWithDoc) (error : Array CmdElabError) : DefTranslateResult

inductive TranslateBackResult where
  | success (statement translation: String)
    (checks : Array Bool) (checksData : Array String) : TranslateBackResult
  | failure  : TranslateBackResult
  deriving Repr, ToJson, FromJson

def TranslateBackResult.checkFailed (r: TranslateBackResult) : Bool :=
  match r with
  | TranslateBackResult.success _ _ checks _ => checks.any id
  | TranslateBackResult.failure => true

structure ElabSuccessResult where
  term : Expr
  allElaborated : Array String
  allElaboratedExprs : Array Expr
  groups : Array (Array String)
  groupsExprs : Array (Array Expr)
  roundTripCheck? : Option Bool := none
  roundTripFailures : Array (String × Array (Bool × String)) := #[]
  deriving Repr

def ElabSuccessResult.view (er: ElabSuccessResult) : MetaM String :=
  er.term.view

structure TranslateSuccessResult extends ElabSuccessResult where
  view : String

def ElabSuccessResult.withView (er: ElabSuccessResult) : MetaM TranslateSuccessResult := do
  return {er with view := (← er.view)}

abbrev TranslateResult := Except (Array ElabErrorData) ElabSuccessResult

structure Translate.State where
  /-- Embeddings to preload -/
  embedMap : EmbedMap := HashMap.empty
  /-- Embedding response associated to the query -/
  queryEmbeddingCache : HashMap String (Except String Json) := HashMap.empty
  /-- Descriptions, docstrings etc -/
  descriptionMap : HashMap Name Json := HashMap.empty
  cmdPrelude : Array String := #[]
  defs : Array (DefWithDoc) := #[]
  errorLog : Array ElabErrorData := #[]
  context : Option String := none
deriving Inhabited

abbrev TranslateM := StateT Translate.State TermElabM

instance [MetaEval α] : MetaEval (TranslateM α) :=
  let me : MetaEval (TermElabM α) := inferInstance
  { eval := fun env opts x b =>
    me.eval env opts (x.run' {}) b}

namespace Translate

def getEmbedMap : TranslateM EmbedMap := do
  return (← get).embedMap

def addEmbeddings (descField: String) (embeddings: EmbedData) : TranslateM Unit := do
  modify fun s => {s with embedMap := s.embedMap.insert descField embeddings}

def setEmbedMap (em : EmbedMap) : TranslateM Unit := do
  modify fun s => {s with embedMap := em}

def withEmbeddings (em : EmbedMap) (x: TranslateM α) :
    TranslateM α := do
  setEmbedMap em
  x

def setContext (ctx : String) : TranslateM Unit := do
  modify fun s => {s with context := some ctx}

def getContext : TranslateM <| Option String := do
  return (← get).context

def logError (source: String) (prompt?: Option Json) (errs: Array ElabError) : TranslateM Unit := do
  modify fun s => {s with errorLog := s.errorLog.push {source := source, prompt? := prompt?, elabErrors := errs}}

def getErrors : TranslateM <| Array ElabErrorData := do
  return (← get).errorLog

def printKeys : TranslateM Unit := do
  let em := (← getEmbedMap)
  IO.println s!"Embeddings: {em.toList.map Prod.fst}"

def getDescMap : TranslateM (HashMap Name Json) := do
  return (← get).descriptionMap

def addDescription (desc: Json) : TranslateM Unit := do
  match desc.getObjValAs? String "name" with
  | Except.ok name => do
    let m ← getDescMap
    let newDesc :=
      match m.find? name.toName with
      | some d => d.mergeObj desc
      | none =>  desc
    modify fun s =>
      {s with descriptionMap := s.descriptionMap.insert name.toName newDesc}
  | Except.error _ => return

def uploadDesciptions (file: System.FilePath) : TranslateM Unit := do
  let lines ← IO.FS.lines file
  for line in lines do
    match Json.parse line with
    | Except.ok desc =>
      Translate.addDescription desc
    | Except.error _ => continue

def preloadDescriptions : TranslateM Unit := do
  uploadDesciptions <| "resources" / "mathlib4-prompts.jsonl"
  uploadDesciptions <| "resources" / "mathlib4-descs.jsonl"

def getDescriptionData (name: Name) : TranslateM <| Option Json := do
  let m ← getDescMap
  if m.isEmpty then preloadDescriptions
  let m ← getDescMap
  match m.find? name with
  | some desc => return desc
  | none => return none

def cmdPreludeBlob : TranslateM String := do
  let cmds := (← get).cmdPrelude
  return cmds.foldr (· ++ "\n" ++ · ) "\n\n"

def runCommand (cmd: String) : TranslateM Unit := do
  discard <|  runFrontendM cmd true
  modify fun s  => {s with cmdPrelude := s.cmdPrelude.push cmd}

def addDefn (dfn: DefWithDoc) : TranslateM Unit := do
  runCommand <| ← dfn.statement
  modify fun s => {s with defs := s.defs.push dfn}

def clearDefs : TranslateM Unit := do
  modify fun s => {s with defs := #[]}

def defsBlob : TranslateM <| Array String := do
  let defs := (← get).defs
  defs.mapM <| fun dfn => dfn.statementWithDoc dfn.doc

def defsNameBlob : TranslateM <| Array <| Name × String := do
  let defs := (← get).defs
  defs.mapM <| fun dfn => do pure (dfn.name, ← dfn.statementWithDoc dfn.doc)
end Translate

namespace TranslateM
open Translate
def runWithEmbeddings (em : EmbedMap)
    (x: TranslateM α) : CoreM α := do
  let x :=
    withEmbeddings em do
      printKeys
      x
  x.run' {} |>.run'.run'


def runToCore (x: TranslateM α) : CoreM α := do
  x.run' {} |>.run'.run'

end TranslateM

open Translate
def timedTest : TranslateM (Nat × Nat × Nat × Json × Json × Json) := do
  let t₀ ← IO.monoMsNow
  let d₁ ← getDescriptionData ``Nat.add_assoc
  let t₁ ← IO.monoMsNow
  let d₂ ← getDescriptionData ``Nat.add_comm
  let t₂ ← IO.monoMsNow
  let d₃ ← getDescriptionData ``Nat.mul_comm
  let t₃ ← IO.monoMsNow
  return (t₁ - t₀, t₂ - t₁, t₃ - t₂, d₁.getD Json.null, d₂.getD Json.null, d₃.getD Json.null)

-- #eval timedTest

-- Should probably purge everything below
unsafe def withLoadedEmbeddings (descField: String)
    (x: TranslateM α) :TranslateM α := do
  withUnpickle (← picklePath descField)
    <|fun (descData : EmbedData) =>  do
      addEmbeddings descField descData
      x

unsafe def withAllEmbeddings (descFields : List String)
    (x: TranslateM α) : TranslateM α := do
  match descFields with
  | [] => x
  | descField::descFields => do
    withLoadedEmbeddings descField do
      withAllEmbeddings descFields x



unsafe def TranslateM.runWithLoadingEmbeddings (descFields : List String)
    (x: TranslateM α) : CoreM α := do
  let x :=
    withAllEmbeddings descFields do
    printKeys
    x
  x.run' {} |>.run'.run'


end LeanAide
