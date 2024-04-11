import Lean.Data
open Lean

variable (α : Type)[DecidableEq α][Inhabited α]

structure Cluster where
  pivot : α
  elements : Array α

partial def epsilonClustersAux  (epsilon: Float)
    (distance : α -> α -> Float) (elements : Array α)
    (accum : Array <| Cluster α) : IO (Array (Cluster α))  := do
  if elements.isEmpty then
    return accum
  else
    let idx ← IO.rand 0 (elements.size - 1)
    let pivot := elements[idx]!
    let (group, rest) :=
      elements.split (fun x => distance x pivot < epsilon)
    let cluster : Cluster α := {pivot := pivot, elements := group}
    epsilonClustersAux epsilon distance rest (accum.push cluster)

def epsilonClusters (epsilon: Float) (distance : α -> α -> Float)
    (elements : Array α) : IO (Array (Cluster α))  := do
  epsilonClustersAux α epsilon distance elements #[]
