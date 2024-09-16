import Lean
import LeanAide.Aides
import Batteries.Util.Pickle

open Lean Meta Elab Term

namespace LeanAide.Meta

structure Translate.State where
  embedMap : EmbedMap := HashMap.empty
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

def TranslateM.runToCore (x: TranslateM α) : CoreM α := do
  x.run' {} |>.run'.run'

end LeanAide.Meta
