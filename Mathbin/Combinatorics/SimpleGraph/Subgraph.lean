/-
Copyright (c) 2021 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe, Kyle Miller, Alena Gusakov
-/
import Mathbin.Combinatorics.SimpleGraph.Basic

/-!
# Subgraphs of a simple graph

A subgraph of a simple graph consists of subsets of the graph's vertices and edges such that the
endpoints of each edge are present in the vertex subset. The edge subset is formalized as a
sub-relation of the adjacency relation of the simple graph.

## Main definitions

* `subgraph G` is the type of subgraphs of a `G : simple_graph`

* `subgraph.neighbor_set`, `subgraph.incidence_set`, and `subgraph.degree` are like their
  `simple_graph` counterparts, but they refer to vertices from `G` to avoid subtype coercions.

* `subgraph.coe` is the coercion from a `G' : subgraph G` to a `simple_graph G'.verts`.
  (This cannot be a `has_coe` instance since the destination type depends on `G'`.)

* `subgraph.is_spanning` for whether a subgraph is a spanning subgraph and
  `subgraph.is_induced` for whether a subgraph is an induced subgraph.

* Instances for `lattice (subgraph G)` and `bounded_order (subgraph G)`.

* `simple_graph.to_subgraph`: If a `simple_graph` is a subgraph of another, then you can turn it
  into a member of the larger graph's `simple_graph.subgraph` type.

* Graph homomorphisms from a subgraph to a graph (`subgraph.map_top`) and between subgraphs
  (`subgraph.map`).

## Implementation notes

* Recall that subgraphs are not determined by their vertex sets, so `set_like` does not apply to
  this kind of subobject.

## Todo

* Images of graph homomorphisms as subgraphs.

-/


universe u v

namespace SimpleGraph

/-- A subgraph of a `simple_graph` is a subset of vertices along with a restriction of the adjacency
relation that is symmetric and is supported by the vertex subset.  They also form a bounded lattice.

Thinking of `V → V → Prop` as `set (V × V)`, a set of darts (i.e., half-edges), then
`subgraph.adj_sub` is that the darts of a subgraph are a subset of the darts of `G`. -/
@[ext]
structure Subgraph {V : Type u} (G : SimpleGraph V) where
  Verts : Set V
  Adj : V → V → Prop
  adj_sub : ∀ {v w : V}, adj v w → G.Adj v w
  edge_vert : ∀ {v w : V}, adj v w → v ∈ verts
  symm : Symmetric adj := by
    run_tac
      obviously

namespace Subgraph

variable {V : Type u} {W : Type v} {G : SimpleGraph V}

protected theorem loopless (G' : Subgraph G) : Irreflexive G'.Adj := fun v h => G.loopless v (G'.adj_sub h)

theorem adj_comm (G' : Subgraph G) (v w : V) : G'.Adj v w ↔ G'.Adj w v :=
  ⟨fun x => G'.symm x, fun x => G'.symm x⟩

@[symm]
theorem adj_symm (G' : Subgraph G) {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

protected theorem Adj.symm {G' : Subgraph G} {u v : V} (h : G'.Adj u v) : G'.Adj v u :=
  G'.symm h

/-- Coercion from `G' : subgraph G` to a `simple_graph ↥G'.verts`. -/
@[simps]
protected def coe (G' : Subgraph G) : SimpleGraph G'.Verts where
  Adj := fun v w => G'.Adj v w
  symm := fun v w h => G'.symm h
  loopless := fun v h => loopless G v (G'.adj_sub h)

@[simp]
theorem coe_adj_sub (G' : Subgraph G) (u v : G'.Verts) (h : G'.coe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

/-- A subgraph is called a *spanning subgraph* if it contains all the vertices of `G`. --/
def IsSpanning (G' : Subgraph G) : Prop :=
  ∀ v : V, v ∈ G'.Verts

theorem is_spanning_iff {G' : Subgraph G} : G'.IsSpanning ↔ G'.Verts = Set.Univ :=
  Set.eq_univ_iff_forall.symm

/-- Coercion from `subgraph G` to `simple_graph V`.  If `G'` is a spanning
subgraph, then `G'.spanning_coe` yields an isomorphic graph.
In general, this adds in all vertices from `V` as isolated vertices. -/
@[simps]
protected def spanningCoe (G' : Subgraph G) : SimpleGraph V where
  Adj := G'.Adj
  symm := G'.symm
  loopless := fun v hv => G.loopless v (G'.adj_sub hv)

@[simp]
theorem Adj.of_spanning_coe {G' : Subgraph G} {u v : G'.Verts} (h : G'.spanningCoe.Adj u v) : G.Adj u v :=
  G'.adj_sub h

/-- `spanning_coe` is equivalent to `coe` for a subgraph that `is_spanning`.  -/
@[simps]
def spanningCoeEquivCoeOfSpanning (G' : Subgraph G) (h : G'.IsSpanning) : G'.spanningCoe ≃g G'.coe where
  toFun := fun v => ⟨v, h v⟩
  invFun := fun v => v
  left_inv := fun v => rfl
  right_inv := fun ⟨v, hv⟩ => rfl
  map_rel_iff' := fun v w => Iff.rfl

/-- A subgraph is called an *induced subgraph* if vertices of `G'` are adjacent if
they are adjacent in `G`. -/
def IsInduced (G' : Subgraph G) : Prop :=
  ∀ {v w : V}, v ∈ G'.Verts → w ∈ G'.Verts → G.Adj v w → G'.Adj v w

/-- `H.support` is the set of vertices that form edges in the subgraph `H`. -/
def Support (H : Subgraph G) : Set V :=
  Rel.Dom H.Adj

theorem mem_support (H : Subgraph G) {v : V} : v ∈ H.Support ↔ ∃ w, H.Adj v w :=
  Iff.rfl

theorem support_subset_verts (H : Subgraph G) : H.Support ⊆ H.Verts := fun v ⟨w, h⟩ => H.edge_vert h

/-- `G'.neighbor_set v` is the set of vertices adjacent to `v` in `G'`. -/
def NeighborSet (G' : Subgraph G) (v : V) : Set V :=
  SetOf (G'.Adj v)

theorem neighbor_set_subset (G' : Subgraph G) (v : V) : G'.NeighborSet v ⊆ G.NeighborSet v := fun w h => G'.adj_sub h

theorem neighbor_set_subset_verts (G' : Subgraph G) (v : V) : G'.NeighborSet v ⊆ G'.Verts := fun _ h =>
  G'.edge_vert (adj_symm G' h)

@[simp]
theorem mem_neighbor_set (G' : Subgraph G) (v w : V) : w ∈ G'.NeighborSet v ↔ G'.Adj v w :=
  Iff.rfl

/-- A subgraph as a graph has equivalent neighbor sets. -/
def coeNeighborSetEquiv {G' : Subgraph G} (v : G'.Verts) : G'.coe.NeighborSet v ≃ G'.NeighborSet v where
  toFun := fun w =>
    ⟨w, by
      obtain ⟨w', hw'⟩ := w
      simpa using hw'⟩
  invFun := fun w =>
    ⟨⟨w, G'.edge_vert (G'.adj_symm w.2)⟩, by
      simpa using w.2⟩
  left_inv := fun w => by
    simp
  right_inv := fun w => by
    simp

/-- The edge set of `G'` consists of a subset of edges of `G`. -/
def EdgeSet (G' : Subgraph G) : Set (Sym2 V) :=
  Sym2.FromRel G'.symm

theorem edge_set_subset (G' : Subgraph G) : G'.EdgeSet ⊆ G.EdgeSet := fun e => Quotientₓ.ind (fun e h => G'.adj_sub h) e

@[simp]
theorem mem_edge_set {G' : Subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ G'.EdgeSet ↔ G'.Adj v w :=
  Iff.rfl

theorem mem_verts_if_mem_edge {G' : Subgraph G} {e : Sym2 V} {v : V} (he : e ∈ G'.EdgeSet) (hv : v ∈ e) :
    v ∈ G'.Verts := by
  refine' Quotientₓ.ind (fun e he hv => _) e he hv
  cases' e with v w
  simp only [← mem_edge_set] at he
  cases' sym2.mem_iff.mp hv with h h <;> subst h
  · exact G'.edge_vert he
    
  · exact G'.edge_vert (G'.symm he)
    

/-- The `incidence_set` is the set of edges incident to a given vertex. -/
def IncidenceSet (G' : Subgraph G) (v : V) : Set (Sym2 V) :=
  { e ∈ G'.EdgeSet | v ∈ e }

theorem incidence_set_subset_incidence_set (G' : Subgraph G) (v : V) : G'.IncidenceSet v ⊆ G.IncidenceSet v :=
  fun e h => ⟨G'.edge_set_subset h.1, h.2⟩

theorem incidence_set_subset (G' : Subgraph G) (v : V) : G'.IncidenceSet v ⊆ G'.EdgeSet := fun _ h => h.1

/-- Give a vertex as an element of the subgraph's vertex type. -/
@[reducible]
def vert (G' : Subgraph G) (v : V) (h : v ∈ G'.Verts) : G'.Verts :=
  ⟨v, h⟩

/-- Create an equal copy of a subgraph (see `copy_eq`) with possibly different definitional equalities.
See Note [range copy pattern].
-/
def copy (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.Verts) (adj' : V → V → Prop) (hadj : adj' = G'.Adj) :
    Subgraph G where
  Verts := V''
  Adj := adj'
  adj_sub := hadj.symm ▸ G'.adj_sub
  edge_vert := hV.symm ▸ hadj.symm ▸ G'.edge_vert
  symm := hadj.symm ▸ G'.symm

theorem copy_eq (G' : Subgraph G) (V'' : Set V) (hV : V'' = G'.Verts) (adj' : V → V → Prop) (hadj : adj' = G'.Adj) :
    G'.copy V'' hV adj' hadj = G' :=
  Subgraph.ext _ _ hV hadj

/-- The union of two subgraphs. -/
def union (x y : Subgraph G) : Subgraph G where
  Verts := x.Verts ∪ y.Verts
  Adj := x.Adj⊔y.Adj
  adj_sub := fun v w h => Or.cases_on h (fun h => x.adj_sub h) fun h => y.adj_sub h
  edge_vert := fun v w h => Or.cases_on h (fun h => Or.inl (x.edge_vert h)) fun h => Or.inr (y.edge_vert h)
  symm := fun v w h => by
    rwa [Pi.sup_apply, Pi.sup_apply, x.adj_comm, y.adj_comm]

/-- The intersection of two subgraphs. -/
def inter (x y : Subgraph G) : Subgraph G where
  Verts := x.Verts ∩ y.Verts
  Adj := x.Adj⊓y.Adj
  adj_sub := fun v w h => x.adj_sub h.1
  edge_vert := fun v w h => ⟨x.edge_vert h.1, y.edge_vert h.2⟩
  symm := fun v w h => by
    rwa [Pi.inf_apply, Pi.inf_apply, x.adj_comm, y.adj_comm]

/-- The `top` subgraph is `G` as a subgraph of itself. -/
def top : Subgraph G where
  Verts := Set.Univ
  Adj := G.Adj
  adj_sub := fun v w h => h
  edge_vert := fun v w h => Set.mem_univ v
  symm := G.symm

/-- The `bot` subgraph is the subgraph with no vertices or edges. -/
def bot : Subgraph G where
  Verts := ∅
  Adj := ⊥
  adj_sub := fun v w h => False.ndrec _ h
  edge_vert := fun v w h => False.ndrec _ h
  symm := fun u v h => h

instance subgraphInhabited : Inhabited (Subgraph G) :=
  ⟨bot⟩

/-- The relation that one subgraph is a subgraph of another. -/
def IsSubgraph (x y : Subgraph G) : Prop :=
  x.Verts ⊆ y.Verts ∧ ∀ ⦃v w : V⦄, x.Adj v w → y.Adj v w

instance : Lattice (Subgraph G) where
  le := IsSubgraph
  sup := union
  inf := inter
  le_refl := fun x => ⟨rfl.Subset, fun _ _ h => h⟩
  le_trans := fun x y z hxy hyz => ⟨hxy.1.trans hyz.1, fun _ _ h => hyz.2 (hxy.2 h)⟩
  le_antisymm := by
    intro x y hxy hyx
    ext1 v
    exact Set.Subset.antisymm hxy.1 hyx.1
    ext v w
    exact Iff.intro (fun h => hxy.2 h) fun h => hyx.2 h
  sup_le := fun x y z hxy hyz =>
    ⟨Set.union_subset hxy.1 hyz.1, fun v w h => h.casesOn (fun h => hxy.2 h) fun h => hyz.2 h⟩
  le_sup_left := fun x y => ⟨Set.subset_union_left x.Verts y.Verts, fun v w h => Or.inl h⟩
  le_sup_right := fun x y => ⟨Set.subset_union_right x.Verts y.Verts, fun v w h => Or.inr h⟩
  le_inf := fun x y z hxy hyz => ⟨Set.subset_inter hxy.1 hyz.1, fun v w h => ⟨hxy.2 h, hyz.2 h⟩⟩
  inf_le_left := fun x y => ⟨Set.inter_subset_left x.Verts y.Verts, fun v w h => h.1⟩
  inf_le_right := fun x y => ⟨Set.inter_subset_right x.Verts y.Verts, fun v w h => h.2⟩

instance : BoundedOrder (Subgraph G) where
  top := top
  bot := bot
  le_top := fun x => ⟨Set.subset_univ _, fun v w h => x.adj_sub h⟩
  bot_le := fun x => ⟨Set.empty_subset _, fun v w h => False.ndrec _ h⟩

-- TODO simp lemmas for the other lattice operations on subgraphs
@[simp]
theorem top_verts : (⊤ : Subgraph G).Verts = Set.Univ :=
  rfl

@[simp]
theorem top_adj_iff {v w : V} : (⊤ : Subgraph G).Adj v w ↔ G.Adj v w :=
  Iff.rfl

@[simp]
theorem bot_verts : (⊥ : Subgraph G).Verts = ∅ :=
  rfl

@[simp]
theorem not_bot_adj {v w : V} : ¬(⊥ : Subgraph G).Adj v w :=
  not_false

@[simp]
theorem inf_adj {H₁ H₂ : Subgraph G} {v w : V} : (H₁⊓H₂).Adj v w ↔ H₁.Adj v w ∧ H₂.Adj v w :=
  Iff.rfl

@[simp]
theorem sup_adj {H₁ H₂ : Subgraph G} {v w : V} : (H₁⊔H₂).Adj v w ↔ H₁.Adj v w ∨ H₂.Adj v w :=
  Iff.rfl

@[simp]
theorem edge_set_top : (⊤ : Subgraph G).EdgeSet = G.EdgeSet :=
  rfl

@[simp]
theorem edge_set_bot : (⊥ : Subgraph G).EdgeSet = ∅ :=
  Set.ext <|
    Sym2.ind
      (by
        simp )

@[simp]
theorem edge_set_inf {H₁ H₂ : Subgraph G} : (H₁⊓H₂).EdgeSet = H₁.EdgeSet ∩ H₂.EdgeSet :=
  Set.ext <|
    Sym2.ind
      (by
        simp )

@[simp]
theorem edge_set_sup {H₁ H₂ : Subgraph G} : (H₁⊔H₂).EdgeSet = H₁.EdgeSet ∪ H₂.EdgeSet :=
  Set.ext <|
    Sym2.ind
      (by
        simp )

@[simp]
theorem spanning_coe_top : (⊤ : Subgraph G).spanningCoe = G := by
  ext
  rfl

@[simp]
theorem spanning_coe_bot : (⊥ : Subgraph G).spanningCoe = ⊥ :=
  rfl

/-- Turn a subgraph of a `simple_graph` into a member of its subgraph type. -/
@[simps]
def _root_.simple_graph.to_subgraph (H : SimpleGraph V) (h : H ≤ G) : G.Subgraph where
  Verts := Set.Univ
  Adj := H.Adj
  adj_sub := h
  edge_vert := fun v w h => Set.mem_univ v
  symm := H.symm

theorem support_mono {H H' : Subgraph G} (h : H ≤ H') : H.Support ⊆ H'.Support :=
  Rel.dom_mono h.2

theorem _root_.simple_graph.to_subgraph.is_spanning (H : SimpleGraph V) (h : H ≤ G) : (H.toSubgraph h).IsSpanning :=
  Set.mem_univ

theorem spanning_coe_le_of_le {H H' : Subgraph G} (h : H ≤ H') : H.spanningCoe ≤ H'.spanningCoe :=
  h.2

/-- The top of the `subgraph G` lattice is equivalent to the graph itself. -/
def topEquiv : (⊤ : Subgraph G).coe ≃g G where
  toFun := fun v => ↑v
  invFun := fun v => ⟨v, trivialₓ⟩
  left_inv := fun ⟨v, _⟩ => rfl
  right_inv := fun v => rfl
  map_rel_iff' := fun a b => Iff.rfl

/-- The bottom of the `subgraph G` lattice is equivalent to the empty graph on the empty
vertex type. -/
def botEquiv : (⊥ : Subgraph G).coe ≃g (⊥ : SimpleGraph Empty) where
  toFun := fun v => v.property.elim
  invFun := fun v => v.elim
  left_inv := fun ⟨_, h⟩ => h.elim
  right_inv := fun v => v.elim
  map_rel_iff' := fun a b => Iff.rfl

theorem edge_set_mono {H₁ H₂ : Subgraph G} (h : H₁ ≤ H₂) : H₁.EdgeSet ≤ H₂.EdgeSet := fun e => Sym2.ind h.2 e

theorem _root_.disjoint.edge_set {H₁ H₂ : Subgraph G} (h : Disjoint H₁ H₂) : Disjoint H₁.EdgeSet H₂.EdgeSet := by
  simpa using edge_set_mono h

/-- Graph homomorphisms induce a covariant function on subgraphs. -/
@[simps]
protected def map {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) : G'.Subgraph where
  Verts := f '' H.Verts
  Adj := Relation.Map H.Adj f f
  adj_sub := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact f.map_rel (H.adj_sub h)
  edge_vert := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact Set.mem_image_of_mem _ (H.edge_vert h)
  symm := by
    rintro _ _ ⟨u, v, h, rfl, rfl⟩
    exact ⟨v, u, H.symm h, rfl, rfl⟩

theorem map_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.map f) := by
  intro H H' h
  constructor
  · intro
    simp only [← map_verts, ← Set.mem_image, ← forall_exists_index, ← and_imp]
    rintro v hv rfl
    exact ⟨_, h.1 hv, rfl⟩
    
  · rintro _ _ ⟨u, v, ha, rfl, rfl⟩
    exact ⟨_, _, h.2 ha, rfl, rfl⟩
    

/-- Graph homomorphisms induce a contravariant function on subgraphs. -/
@[simps]
protected def comap {G' : SimpleGraph W} (f : G →g G') (H : G'.Subgraph) : G.Subgraph where
  Verts := f ⁻¹' H.Verts
  Adj := fun u v => G.Adj u v ∧ H.Adj (f u) (f v)
  adj_sub := by
    rintro v w ⟨ga, ha⟩
    exact ga
  edge_vert := by
    rintro v w ⟨ga, ha⟩
    simp [← H.edge_vert ha]

theorem comap_monotone {G' : SimpleGraph W} (f : G →g G') : Monotone (Subgraph.comap f) := by
  intro H H' h
  constructor
  · intro
    simp only [← comap_verts, ← Set.mem_preimage]
    apply h.1
    
  · intro v w
    simp (config := { contextual := true })only [← comap_adj, ← and_imp, ← true_andₓ]
    intro
    apply h.2
    

theorem map_le_iff_le_comap {G' : SimpleGraph W} (f : G →g G') (H : G.Subgraph) (H' : G'.Subgraph) :
    H.map f ≤ H' ↔ H ≤ H'.comap f := by
  refine' ⟨fun h => ⟨fun v hv => _, fun v w hvw => _⟩, fun h => ⟨fun v => _, fun v w => _⟩⟩
  · simp only [← comap_verts, ← Set.mem_preimage]
    exact h.1 ⟨v, hv, rfl⟩
    
  · simp only [← H.adj_sub hvw, ← comap_adj, ← true_andₓ]
    exact h.2 ⟨v, w, hvw, rfl, rfl⟩
    
  · simp only [← map_verts, ← Set.mem_image, ← forall_exists_index, ← and_imp]
    rintro w hw rfl
    exact h.1 hw
    
  · simp only [← Relation.Map, ← map_adj, ← forall_exists_index, ← and_imp]
    rintro u u' hu rfl rfl
    have := h.2 hu
    simp only [← comap_adj] at this
    exact this.2
    

/-- Given two subgraphs, one a subgraph of the other, there is an induced injective homomorphism of
the subgraphs as graphs. -/
@[simps]
def inclusion {x y : Subgraph G} (h : x ≤ y) : x.coe →g y.coe where
  toFun := fun v => ⟨↑v, And.left h v.property⟩
  map_rel' := fun v w hvw => h.2 hvw

theorem inclusion.injective {x y : Subgraph G} (h : x ≤ y) : Function.Injective (inclusion h) := fun v w h => by
  simp only [← inclusion, ← RelHom.coe_fn_mk, ← Subtype.mk_eq_mk] at h
  exact Subtype.ext h

/-- There is an induced injective homomorphism of a subgraph of `G` into `G`. -/
@[simps]
protected def hom (x : Subgraph G) : x.coe →g G where
  toFun := fun v => v
  map_rel' := fun v w hvw => x.adj_sub hvw

theorem hom.injective {x : Subgraph G} : Function.Injective x.hom := fun v w h => Subtype.ext h

/-- There is an induced injective homomorphism of a subgraph of `G` as
a spanning subgraph into `G`. -/
@[simps]
def spanningHom (x : Subgraph G) : x.spanningCoe →g G where
  toFun := id
  map_rel' := fun v w hvw => x.adj_sub hvw

theorem spanningHom.injective {x : Subgraph G} : Function.Injective x.spanningHom := fun v w h => h

theorem neighbor_set_subset_of_subgraph {x y : Subgraph G} (h : x ≤ y) (v : V) : x.NeighborSet v ⊆ y.NeighborSet v :=
  fun w h' => h.2 h'

instance NeighborSet.decidablePred (G' : Subgraph G) [h : DecidableRel G'.Adj] (v : V) :
    DecidablePred (· ∈ G'.NeighborSet v) :=
  h v

/-- If a graph is locally finite at a vertex, then so is a subgraph of that graph. -/
instance finiteAt {G' : Subgraph G} (v : G'.Verts) [DecidableRel G'.Adj] [Fintype (G.NeighborSet v)] :
    Fintype (G'.NeighborSet v) :=
  Set.fintypeSubset (G.NeighborSet v) (G'.neighbor_set_subset v)

/-- If a subgraph is locally finite at a vertex, then so are subgraphs of that subgraph.

This is not an instance because `G''` cannot be inferred. -/
def finiteAtOfSubgraph {G' G'' : Subgraph G} [DecidableRel G'.Adj] (h : G' ≤ G'') (v : G'.Verts)
    [hf : Fintype (G''.NeighborSet v)] : Fintype (G'.NeighborSet v) :=
  Set.fintypeSubset (G''.NeighborSet v) (neighbor_set_subset_of_subgraph h v)

instance (G' : Subgraph G) [Fintype G'.Verts] (v : V) [DecidablePred (· ∈ G'.NeighborSet v)] :
    Fintype (G'.NeighborSet v) :=
  Set.fintypeSubset G'.Verts (neighbor_set_subset_verts G' v)

instance coeFiniteAt {G' : Subgraph G} (v : G'.Verts) [Fintype (G'.NeighborSet v)] : Fintype (G'.coe.NeighborSet v) :=
  Fintype.ofEquiv _ (coeNeighborSetEquiv v).symm

theorem IsSpanning.card_verts [Fintype V] {G' : Subgraph G} [Fintype G'.Verts] (h : G'.IsSpanning) :
    G'.Verts.toFinset.card = Fintype.card V := by
  rw [is_spanning_iff] at h
  simpa [← h]

/-- The degree of a vertex in a subgraph. It's zero for vertices outside the subgraph. -/
def degree (G' : Subgraph G) (v : V) [Fintype (G'.NeighborSet v)] : ℕ :=
  Fintype.card (G'.NeighborSet v)

theorem finset_card_neighbor_set_eq_degree {G' : Subgraph G} {v : V} [Fintype (G'.NeighborSet v)] :
    (G'.NeighborSet v).toFinset.card = G'.degree v := by
  rw [degree, Set.to_finset_card]

theorem degree_le (G' : Subgraph G) (v : V) [Fintype (G'.NeighborSet v)] [Fintype (G.NeighborSet v)] :
    G'.degree v ≤ G.degree v := by
  rw [← card_neighbor_set_eq_degree]
  exact Set.card_le_of_subset (G'.neighbor_set_subset v)

theorem degree_le' (G' G'' : Subgraph G) (h : G' ≤ G'') (v : V) [Fintype (G'.NeighborSet v)]
    [Fintype (G''.NeighborSet v)] : G'.degree v ≤ G''.degree v :=
  Set.card_le_of_subset (neighbor_set_subset_of_subgraph h v)

@[simp]
theorem coe_degree (G' : Subgraph G) (v : G'.Verts) [Fintype (G'.coe.NeighborSet v)] [Fintype (G'.NeighborSet v)] :
    G'.coe.degree v = G'.degree v := by
  rw [← card_neighbor_set_eq_degree]
  exact Fintype.card_congr (coe_neighbor_set_equiv v)

@[simp]
theorem degree_spanning_coe {G' : G.Subgraph} (v : V) [Fintype (G'.NeighborSet v)]
    [Fintype (G'.spanningCoe.NeighborSet v)] : G'.spanningCoe.degree v = G'.degree v := by
  rw [← card_neighbor_set_eq_degree, subgraph.degree]
  congr

theorem degree_eq_one_iff_unique_adj {G' : Subgraph G} {v : V} [Fintype (G'.NeighborSet v)] :
    G'.degree v = 1 ↔ ∃! w : V, G'.Adj v w := by
  rw [← finset_card_neighbor_set_eq_degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [← Set.mem_to_finset, ← mem_neighbor_set]

/-! ## Subgraphs of subgraphs -/


/-- Given a subgraph of a subgraph of `G`, construct a subgraph of `G`. -/
@[reducible]
protected def coeSubgraph {G' : G.Subgraph} : G'.coe.Subgraph → G.Subgraph :=
  Subgraph.map G'.hom

/-- Given a subgraph of `G`, restrict it to being a subgraph of another subgraph `G'` by
taking the portion of `G` that intersects `G'`. -/
@[reducible]
protected def restrict {G' : G.Subgraph} : G.Subgraph → G'.coe.Subgraph :=
  Subgraph.comap G'.hom

theorem restrict_coe_subgraph {G' : G.Subgraph} (G'' : G'.coe.Subgraph) : G''.coeSubgraph.restrict = G'' := by
  ext
  · simp
    
  · simp only [← Relation.Map, ← comap_adj, ← coe_adj, ← Subtype.coe_prop, ← hom_apply, ← map_adj, ← SetCoe.exists, ←
      Subtype.coe_mk, ← exists_and_distrib_right, ← exists_eq_right_rightₓ, ← Subtype.coe_eta, ← exists_true_left, ←
      exists_eq_right, ← and_iff_right_iff_imp]
    apply G''.adj_sub
    

theorem coe_subgraph_injective (G' : G.Subgraph) :
    Function.Injective (Subgraph.coeSubgraph : G'.coe.Subgraph → G.Subgraph) :=
  Function.LeftInverse.injective restrict_coe_subgraph

/-! ## Edge deletion -/


/-- Given a subgraph `G'` and a set of vertex pairs, remove all of the corresponding edges
from its edge set, if present.

See also: `simple_graph.delete_edges`. -/
def deleteEdges (G' : G.Subgraph) (s : Set (Sym2 V)) : G.Subgraph where
  Verts := G'.Verts
  Adj := G'.Adj \ Sym2.ToRel s
  adj_sub := fun a b h' => G'.adj_sub h'.1
  edge_vert := fun a b h' => G'.edge_vert h'.1
  symm := fun a b => by
    simp [← G'.adj_comm, ← Sym2.eq_swap]

section DeleteEdges

variable {G' : G.Subgraph} (s : Set (Sym2 V))

@[simp]
theorem delete_edges_verts : (G'.deleteEdges s).Verts = G'.Verts :=
  rfl

@[simp]
theorem delete_edges_adj (v w : V) : (G'.deleteEdges s).Adj v w ↔ G'.Adj v w ∧ ¬⟦(v, w)⟧ ∈ s :=
  Iff.rfl

@[simp]
theorem delete_edges_delete_edges (s s' : Set (Sym2 V)) : (G'.deleteEdges s).deleteEdges s' = G'.deleteEdges (s ∪ s') :=
  by
  ext <;> simp [← and_assoc, ← not_or_distrib]

@[simp]
theorem delete_edges_empty_eq : G'.deleteEdges ∅ = G' := by
  ext <;> simp

@[simp]
theorem delete_edges_spanning_coe_eq : G'.spanningCoe.deleteEdges s = (G'.deleteEdges s).spanningCoe := by
  ext
  simp

theorem delete_edges_coe_eq (s : Set (Sym2 G'.Verts)) :
    G'.coe.deleteEdges s = (G'.deleteEdges (Sym2.map coe '' s)).coe := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp only [← SimpleGraph.delete_edges_adj, ← coe_adj, ← Subtype.coe_mk, ← delete_edges_adj, ← Set.mem_image, ←
    not_exists, ← not_and, ← And.congr_right_iff]
  intro h
  constructor
  · intro hs
    refine' Sym2.ind _
    rintro ⟨v', hv'⟩ ⟨w', hw'⟩
    simp only [← Sym2.map_pair_eq, ← Subtype.coe_mk, ← Quotientₓ.eq]
    contrapose!
    rintro (_ | _) <;> simpa [← Sym2.eq_swap]
    
  · intro h' hs
    exact h' _ hs rfl
    

theorem coe_delete_edges_eq (s : Set (Sym2 V)) : (G'.deleteEdges s).coe = G'.coe.deleteEdges (Sym2.map coe ⁻¹' s) := by
  ext ⟨v, hv⟩ ⟨w, hw⟩
  simp

theorem delete_edges_le : G'.deleteEdges s ≤ G' := by
  constructor <;> simp (config := { contextual := true })

theorem delete_edges_le_of_le {s s' : Set (Sym2 V)} (h : s ⊆ s') : G'.deleteEdges s' ≤ G'.deleteEdges s := by
  constructor <;>
    simp (config := { contextual := true })only [← delete_edges_verts, ← delete_edges_adj, ← true_andₓ, ← and_imp]
  exact fun v w hvw hs' hs => hs' (h hs)

@[simp]
theorem delete_edges_inter_edge_set_left_eq : G'.deleteEdges (G'.EdgeSet ∩ s) = G'.deleteEdges s := by
  ext <;> simp (config := { contextual := true })[← imp_false]

@[simp]
theorem delete_edges_inter_edge_set_right_eq : G'.deleteEdges (s ∩ G'.EdgeSet) = G'.deleteEdges s := by
  ext <;> simp (config := { contextual := true })[← imp_false]

theorem coe_delete_edges_le : (G'.deleteEdges s).coe ≤ (G'.coe : SimpleGraph G'.Verts) := fun v w => by
  simp (config := { contextual := true })

theorem spanning_coe_delete_edges_le (G' : G.Subgraph) (s : Set (Sym2 V)) :
    (G'.deleteEdges s).spanningCoe ≤ G'.spanningCoe :=
  spanning_coe_le_of_le (delete_edges_le s)

end DeleteEdges

/-! ## Induced subgraphs -/


/-- The induced subgraph of a subgraph. The expectation is that `s ⊆ G'.verts` for the usual
notion of an induced subgraph, but, in general, `s` is taken to be the new vertex set and edges
are induced from the subgraph `G'`. -/
/- Given a subgraph, we can change its vertex set while removing any invalid edges, which
gives induced subgraphs. See also `simple_graph.induce` for the `simple_graph` version, which,
unlike for subgraphs, results in a graph with a different vertex type. -/
@[simps]
def induce (G' : G.Subgraph) (s : Set V) : G.Subgraph where
  Verts := s
  Adj := fun u v => u ∈ s ∧ v ∈ s ∧ G'.Adj u v
  adj_sub := fun u v => by
    rintro ⟨-, -, ha⟩
    exact G'.adj_sub ha
  edge_vert := fun u v => by
    rintro ⟨h, -, -⟩
    exact h

theorem _root_.simple_graph.induce_eq_coe_induce_top (s : Set V) : G.induce s = ((⊤ : G.Subgraph).induce s).coe := by
  ext v w
  simp

section Induce

variable {G' G'' : G.Subgraph} {s s' : Set V}

theorem induce_mono (hg : G' ≤ G'') (hs : s ⊆ s') : G'.induce s ≤ G''.induce s' := by
  constructor
  · simp [← hs]
    
  · simp (config := { contextual := true })only [← induce_adj, ← true_andₓ, ← and_imp]
    intro v w hv hw ha
    exact ⟨hs hv, hs hw, hg.2 ha⟩
    

@[mono]
theorem induce_mono_left (hg : G' ≤ G'') : G'.induce s ≤ G''.induce s :=
  induce_mono hg
    (by
      rfl)

@[mono]
theorem induce_mono_right (hs : s ⊆ s') : G'.induce s ≤ G'.induce s' :=
  induce_mono
    (by
      rfl)
    hs

@[simp]
theorem induce_empty : G'.induce ∅ = ⊥ := by
  ext <;> simp

end Induce

end Subgraph

end SimpleGraph

