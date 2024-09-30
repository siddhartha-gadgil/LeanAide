import Lean
import LeanAide.Aides
import Batteries.Util.Pickle
import LeanAide.SimpleFrontend

open Lean Meta Elab Term

namespace LeanAide.Meta

structure Translate.State where
  /-- Embeddings to preload -/
  embedMap : EmbedMap := HashMap.empty
  /-- Embedding response associated to the query -/
  queryEmbeddingCache : HashMap String (Except String Json) := HashMap.empty
  /-- Descriptions, docstrings etc -/
  descriptionMap : HashMap Name Json := HashMap.empty
  cmdPrelude : Array String := #[]
  context : Option String := none
deriving Inhabited

abbrev TranslateM := StateT Translate.State TermElabM

instance [MetaEval α] : MetaEval (TranslateM α) :=
  let me : MetaEval (TermElabM α) := inferInstance
  { eval := fun env opts x b =>
    me.eval env opts (x.run' {}) b}

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

def printKeys : TranslateM Unit := do
  let em := (← getEmbedMap)
  IO.println s!"Embeddings: {em.toList.map Prod.fst}"

def TranslateM.runWithEmbeddings (em : EmbedMap)
    (x: TranslateM α) : CoreM α := do
  let x :=
    withEmbeddings em do
      printKeys
      x
  x.run' {} |>.run'.run'

def getDescMap : TranslateM (HashMap Name Json) := do
  return (← get).descriptionMap

def Translate.addDescription (desc: Json) : TranslateM Unit := do
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

namespace TranslateM

def runToCore (x: TranslateM α) : CoreM α := do
  x.run' {} |>.run'.run'

end TranslateM

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

end LeanAide.Meta
