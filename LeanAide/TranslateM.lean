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

unsafe def withEmbeddings (descField: String)
    (x: TranslateM α) :TranslateM α := do
  withUnpickle (← picklePath descField)
    <|fun (descData : EmbedData) =>  do
      addEmbeddings descField descData
      x

unsafe def withAllEmebddings (descFields : List String)
    (x: TranslateM α) : TranslateM α := do
  match descFields with
  | [] => x
  | descField::descFields => do
    withEmbeddings descField do
      withAllEmebddings descFields x

def printKeys : TranslateM Unit := do
  let em := (← getEmbedMap)
  IO.println s!"Embeddings: {em.toList.map Prod.fst}"

unsafe def runWithEmbeddings (descFields : List String)
    (x: TranslateM α) : CoreM α := do
  let x :=
    withAllEmebddings descFields do
    printKeys -- for debugging
    x
  x.run' {} |>.run'.run'

def runToCore (x: TranslateM α) : CoreM α := do
  x.run' {} |>.run'.run'

end LeanAide.Meta
