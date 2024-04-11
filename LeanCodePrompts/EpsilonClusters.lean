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
  let (best, _) :=
    candidates.foldl (fun (best, bd) cl =>
      let d := distance cl.pivot x
      if d < bd + epsilon then
        let (best', dist') :=
          arrayMin cl.elements x distance best bd
        if dist' < bd then (best', dist')
          else (best, bd)
      else (best, bd)) (sorted[0]!.pivot, d₀)
  -- let allElements :=
  --   candidates.foldl (fun acc c => acc ++ c.elements) #[]
  -- let sorted' :=
  --   allElements.qsort (fun a b => distance a x < distance b x)
  -- sorted'[0]!
  best
  where
    arrayMin (a : Array α)(x : α)(distance : α -> α -> Float)
      (best: α)(bound: Float) : α × Float :=
      a.foldl (fun (b, bd) y =>
        let d := distance y x
        if d < bd then (y, d)
        else (b, bd)) (best, bound)

inductive EpsilonTree where
  | leaf : Array α -> EpsilonTree
  | node : Float × Array (α × EpsilonTree) -> EpsilonTree
deriving Inhabited, Repr

namespace EpsilonTree
partial def refine (tree: EpsilonTree α)(epsilon: Float)
  (distance : α -> α -> Float):
    IO (EpsilonTree α) := do
  match tree with
  | EpsilonTree.leaf elements =>
    let clusters ← epsilonClusters α epsilon distance (elements)
    return EpsilonTree.node (epsilon, clusters.map (fun c =>
      (c.pivot, EpsilonTree.leaf c.elements)))
  | EpsilonTree.node (ε, children) =>
    let children' ← children.mapM (fun (x, t) => do
      let t' ← t.refine epsilon distance
      return (x, t'))
    return EpsilonTree.node (ε, children')

def multiRefine (tree: EpsilonTree α)(epsilons : List Float)
  (distance : α -> α -> Float) : IO (EpsilonTree α) :=
  match epsilons with
  | [] => return tree
  | ε::rest => do
    let tree' ← tree.refine α ε distance
    multiRefine tree' rest distance

def build (elements : Array α)(epsilons : List Float)
  (distance : α -> α -> Float) : IO (EpsilonTree α) :=
  multiRefine α (EpsilonTree.leaf elements) epsilons distance

partial def nearest (tree : EpsilonTree α)(x : α)
    (distance : α -> α -> Float): α :=
  match tree with
  | .leaf elements =>
    let sorted := elements.qsort (fun a b => distance a x < distance b x)
    sorted[0]!
  | .node (ε, children) =>
    let sorted := children.qsort (fun (a, _) (b, _) =>
      distance a x < distance b x)
    let d₀ := distance sorted[0]!.1 x
    let candidates := sorted.takeWhile (fun (a, _) =>
      distance a x < d₀ + ε)
    let (best, _) := candidates.foldl (fun (best, bd) (pivot, t) =>
      let d := distance pivot x
      if d < bd + ε then
        let best' := t.nearest x distance
        let dist' := distance best' x
        if dist' < bd then (best', dist')
          else (best, bd)
      else (best, bd)) (sorted[0]!.1, d₀)
    best

end EpsilonTree

def randomClustered : IO <| Float × Float ×
   (Array <| Cluster Float) := do
  let randoms ←  (List.replicate 10 0).mapM
    (fun _ => do
      let n ←  IO.rand 0 10000
      pure <| n.toFloat / 100.0)
  let clusters ←
    epsilonClusters Float 7.0 (fun x y => (x - y).abs) randoms.toArray
  let best := Cluster.nearest Float 7.0 clusters 43.3295
    (fun x y => (x - y).abs)
  let tree ←
    EpsilonTree.build Float randoms.toArray [7.0, 1.5]
      (fun x y => (x - y).abs)
  let best' := tree.nearest Float 43.3295 (fun x y => (x - y).abs)
  return (best, best', clusters)


#eval randomClustered
