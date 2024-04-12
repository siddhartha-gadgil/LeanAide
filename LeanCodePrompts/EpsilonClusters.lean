import Lean.Data
import LeanAide.Aides
import Mathlib
open Lean

def insertByMemo (l: Array <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α) (cx? : Option Float := none) : Array <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx := match cx? with
    | some c => c
    | none => cost x
    match l.findIdx? (fun (_, cy) => cx < cy) with
    | some idx =>
      l.insertAt idx (x, cx) |>.shrink (k + 1)
    | none => l.push (x, cx) |>.shrink (k + 1)

def insertBy (l: Array <| α × Float)(cost : α → Float)(sizeBound: Nat)
    (x : α)  : Array <| α × Float :=
  match sizeBound with
  | 0 => l
  | k + 1 =>
    let cx :=  cost x
    match l.findIdx? (fun (_, cy) => cx < cy) with
    | some idx =>
      l.insertAt idx (x, cx) |>.shrink (k + 1)
    | none => l.push (x, cx) |>.shrink (k + 1)

def bestWithCost (l: Array <| α)
  (cost : α → Float)(n: Nat)(accum : Array <| α × Float := #[]): Array <| α × Float :=
  l.foldl (fun (acc : Array <| α × Float) (x: α) =>
    insertBy acc cost n x) accum

def bestWithCostConc (l: Array <| α)
  (cost : α → Float)(n: Nat): IO <| Array <| α × Float := do
  let groups := l.batches' <| ← threadNum
  let tasks := groups.map <| fun group => Task.spawn <| fun _ =>
    bestWithCost group cost n
  let resultGroups := tasks.map Task.get
  let results := resultGroups.foldl (fun acc group => acc ++ group) #[]
  return results.qsort (fun (_, c₁) (_, c₂) => c₁ < c₂) |>.shrink n


structure Cluster(α : Type)[Inhabited α] where
  pivot : α
  ε : Float
  elements : Array α
deriving Repr, Inhabited

variable {α : Type}[Inhabited α][BEq α]

partial def epsilonClustersAux  (ε: Float)
    (distance : α -> α -> Float) (minSize : Nat) (elements : Array α)
    (accum : Array <| Cluster α) : IO (Array (Cluster α))  := do
  if elements.isEmpty then
    return accum
  else
    let idx ← IO.rand 0 (elements.size - 1)
    let pivot := elements[idx]!
    -- IO.eprintln s!"Found pivot"
    let (group, rest) :=
      elements.split (fun x => distance x pivot < ε)
    -- IO.eprintln s!"Split into {group.size} and {rest.size}"
    let (cluster, tail) ← do
      if group.size ≥ minSize then
        pure ({pivot := pivot, elements := group, ε := ε},
        rest)
      else
        let elementsWithWeights :=
          bestWithCost elements (fun x => distance x pivot) minSize
        let max := elementsWithWeights.reverse[0]!.2
        let group := elementsWithWeights.map (·.1)
        let rest := elements.filter (fun x => !(group.contains x))
        pure
          ({pivot := pivot, elements := group,ε := max}, rest)
    epsilonClustersAux ε distance minSize tail (accum.push cluster)

def epsilonClusters (ε: Float) (distance : α -> α -> Float)
    (minSize: Nat) (elements : Array α) : IO (Array (Cluster α))  := do
  epsilonClustersAux ε distance minSize elements #[]

variable {β : Type}[Inhabited β][BEq β]

def Cluster.nearest (cs : Array <| Cluster α)(x : β)
  (distance : α -> β  -> Float) : α :=
  let withDistance := cs.map (fun c => (c, distance c.pivot x))
  let sorted :=
    withDistance.qsort (fun (_, d1) (_, d2) => d1 < d2)
  let d₀ := sorted[0]!.2
  let candidates := sorted.filter (fun (c, d) =>
    d < c.ε + d₀)
  let (best, _) :=
    candidates.foldl (fun (best, bd) (cl, d) =>
      if d < bd + cl.ε then
        let (best', dist') :=
          arrayMin cl.elements x distance best bd
        if dist' < bd then (best', dist')
          else (best, bd)
      else (best, bd)) (sorted[0]!.1.pivot, d₀)
  best
  where
    arrayMin (a : Array α)(x : β)(distance : α -> β -> Float)
      (best: α)(bound: Float) : α × Float :=
      a.foldl (fun (b, bd) y =>
        let d := distance y x
        if d < bd then (y, d)
        else (b, bd)) (best, bound)

def Cluster.kNearest (k: Nat)(cs : Array <| Cluster α)(x : β)
  (distance : α -> β  -> Float) : Array (α × Float) :=
  let withDistance := cs.map (fun c => (c, distance c.pivot x))
  let sorted :=
    withDistance.qsort (fun (_, d1) (_, d2) => d1 < d2)
  let best :=
    sorted.foldl (fun best (cl, d) =>
      let check: Bool := match best[k - 1]? with
        | some (_, bd) => d < bd + cl.ε
        | none => true
      if check == true then
        bestWithCost cl.elements (fun y => distance y x) k best
      else
        best) #[]
  best

inductive EpsilonTree (α : Type)[Inhabited α] where
  | leaf : Array α -> EpsilonTree α
  | node : Array (Float × α × EpsilonTree α ) -> EpsilonTree α
deriving Inhabited, Repr

namespace EpsilonTree
partial def refine (tree: EpsilonTree α)(ε: Float)
  (distance : α -> α -> Float)(minSize: Nat):
    IO (EpsilonTree α) := do
  match tree with
  | EpsilonTree.leaf elements =>
    let clusters ← epsilonClusters ε distance minSize (elements)
    return EpsilonTree.node (clusters.map (fun c =>
      (c.ε, c.pivot, EpsilonTree.leaf c.elements)))
  | EpsilonTree.node children =>
    let children' ← children.mapM (fun (ε', (x, t)) => do
      let t' ← t.refine ε distance minSize
      return (ε', x, t'))
    return EpsilonTree.node children'

def multiRefine (tree: EpsilonTree α)(epsilons : List (Float × Nat))
  (distance : α -> α -> Float) : IO (EpsilonTree α) :=
  match epsilons with
  | [] => return tree
  | (ε, minSize)::rest => do
    let tree' ← tree.refine ε distance minSize
    multiRefine tree' rest distance

def build (elements : Array α)(epsilons : List (Float × Nat))
  (distance : α -> α -> Float) : IO (EpsilonTree α) :=
  multiRefine (EpsilonTree.leaf elements) epsilons distance

partial def nearest (tree : EpsilonTree α)(x : α)
    (distance : α -> α -> Float): α :=
  match tree with
  | .leaf elements =>
    let best := bestWithCost elements (fun y => distance y x) 1
    best[0]!.1
  | .node children =>
    let sorted := children.qsort (fun (_, a, _) (_, b, _) =>
      distance a x < distance b x)
    let d₀ := distance sorted[0]!.2.1 x
    let candidates := sorted.filter (fun (ε, a, _) =>
      distance a x < d₀ + ε)
    let (best, _) := candidates.foldl (fun (best, bd) (ε, pivot, t) =>
      let d := distance pivot x
      if d < bd + ε then
        let best' := t.nearest x distance
        let dist' := distance best' x
        if dist' < bd then (best', dist')
          else (best, bd)
      else (best, bd)) (sorted[0]!.2.1, d₀)
    best

end EpsilonTree

def randomClustered : IO <| Float × Float × (Array (Float × Float)) ×
   (Array <| Cluster Float) := do
  let randoms ←  (List.replicate 20 0).mapM
    (fun _ => do
      let n ←  IO.rand 0 10000
      pure <| n.toFloat / 100.0)
  let clusters ←
    epsilonClusters 3.0 (fun x y => (x - y).abs)
    2  randoms.toArray
  let best := Cluster.nearest clusters 43.3295
    (fun x y => (x - y).abs)
  let best2 := Cluster.kNearest 3 clusters 43.3295
    (fun x y => (x - y).abs)
  let tree ←
    EpsilonTree.build randoms.toArray [(7.0, 2), (1.5, 1)]
      (fun x y => (x - y).abs)
  let best' := tree.nearest 43.3295 (fun x y => (x - y).abs)
  return (best, best', best2, clusters)


#eval randomClustered
