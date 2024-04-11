import Lean.Data
open Lean

variable (α : Type)[DecidableEq α][Inhabited α]

structure Cluster where
  pivot : α
  elements : Array α
deriving Repr, Inhabited

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

def Cluster.nearest (epsilon: Float)(cs : Array <| Cluster α)(x : α)
  (distance : α -> α -> Float) : α :=
  let sorted :=
    cs.qsort (fun c1 c2 => distance c1.pivot x < distance c2.pivot x)
  let d₀ := distance sorted[0]!.pivot x
  let candidates := sorted.takeWhile (fun c =>
    distance c.pivot x < epsilon + d₀)
  let allElements :=
    candidates.foldl (fun acc c => acc ++ c.elements) #[]
  let sorted' :=
    allElements.qsort (fun a b => distance a x < distance b x)
  sorted'[0]!

inductive EpsilonTree where
  | leaf : Array α -> EpsilonTree
  | node : Float × Array (α × EpsilonTree) -> EpsilonTree

def randomClustered : IO <| Float ×  (Array <| Cluster Float) := do
  let randoms ←  (List.replicate 1000 0).mapM
    (fun _ => do
      let n ←  IO.rand 0 1000
      pure <| n.toFloat / 10.0)
  let clusters ←
    epsilonClusters Float 7.0 (fun x y => (x - y).abs) randoms.toArray
  let best := Cluster.nearest Float 7.0 clusters 53.3295
    (fun x y => (x - y).abs)
  return (best, clusters)


#eval randomClustered
