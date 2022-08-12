/-
Copyright (c) 2020 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Arthur Paulino, Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.DegreeSum
import Mathbin.Combinatorics.SimpleGraph.Subgraph

/-!
# Matchings

A *matching* for a simple graph is a set of disjoint pairs of adjacent vertices, and the set of all
the vertices in a matching is called its *support* (and sometimes the vertices in the support are
said to be *saturated* by the matching). A *perfect matching* is a matching whose support contains
every vertex of the graph.

In this module, we represent a matching as a subgraph whose vertices are each incident to at most
one edge, and the edges of the subgraph represent the paired vertices.

## Main definitions

* `simple_graph.subgraph.is_matching`: `M.is_matching` means that `M` is a matching of its
  underlying graph.
  denoted `M.is_matching`.

* `simple_graph.subgraph.is_perfect_matching` defines when a subgraph `M` of a simple graph is a
  perfect matching, denoted `M.is_perfect_matching`.

## TODO

* Define an `other` function and prove useful results about it (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/266205863)

* Provide a bicoloring for matchings (https://leanprover.zulipchat.com/#narrow/stream/252551-graph-theory/topic/matchings/near/265495120)

* Tutte's Theorem

* Hall's Marriage Theorem (see combinatorics.hall)
-/


universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} (M : Subgraph G)

namespace Subgraph

/-- The subgraph `M` of `G` is a matching if every vertex of `M` is incident to exactly one edge in `M`.
We say that the vertices in `M.support` are *matched* or *saturated*.
-/
def IsMatching : Prop :=
  ∀ ⦃v⦄, v ∈ M.Verts → ∃! w, M.Adj v w

/-- Given a vertex, returns the unique edge of the matching it is incident to. -/
noncomputable def IsMatching.toEdge {M : Subgraph G} (h : M.IsMatching) (v : M.Verts) : M.EdgeSet :=
  ⟨⟦(v, (h v.property).some)⟧, (h v.property).some_spec.1⟩

theorem IsMatching.to_edge_eq_of_adj {M : Subgraph G} (h : M.IsMatching) {v w : V} (hv : v ∈ M.Verts)
    (hvw : M.Adj v w) : h.toEdge ⟨v, hv⟩ = ⟨⟦(v, w)⟧, hvw⟩ := by
  simp only [← is_matching.to_edge, ← Subtype.mk_eq_mk]
  congr
  exact ((h (M.edge_vert hvw)).some_spec.2 w hvw).symm

theorem IsMatching.toEdge.surjective {M : Subgraph G} (h : M.IsMatching) : Function.Surjective h.toEdge := by
  rintro ⟨e, he⟩
  refine' Sym2.ind (fun x y he => _) e he
  exact ⟨⟨x, M.edge_vert he⟩, h.to_edge_eq_of_adj _ he⟩

theorem IsMatching.to_edge_eq_to_edge_of_adj {M : Subgraph G} {v w : V} (h : M.IsMatching) (hv : v ∈ M.Verts)
    (hw : w ∈ M.Verts) (ha : M.Adj v w) : h.toEdge ⟨v, hv⟩ = h.toEdge ⟨w, hw⟩ := by
  rw [h.to_edge_eq_of_adj hv ha, h.to_edge_eq_of_adj hw (M.symm ha), Subtype.mk_eq_mk, Sym2.eq_swap]

/-- The subgraph `M` of `G` is a perfect matching on `G` if it's a matching and every vertex `G` is
matched.
-/
def IsPerfectMatching : Prop :=
  M.IsMatching ∧ M.IsSpanning

theorem IsMatching.support_eq_verts {M : Subgraph G} (h : M.IsMatching) : M.Support = M.Verts := by
  refine' M.support_subset_verts.antisymm fun v hv => _
  obtain ⟨w, hvw, -⟩ := h hv
  exact ⟨_, hvw⟩

theorem is_matching_iff_forall_degree {M : Subgraph G} [∀ v : V, Fintype (M.NeighborSet v)] :
    M.IsMatching ↔ ∀ v : V, v ∈ M.Verts → M.degree v = 1 := by
  simpa [← degree_eq_one_iff_unique_adj]

theorem IsMatching.even_card {M : Subgraph G} [Fintype M.Verts] (h : M.IsMatching) : Even M.Verts.toFinset.card := by
  classical
  rw [is_matching_iff_forall_degree] at h
  use M.coe.edge_finset.card
  rw [← two_mul, ← M.coe.sum_degrees_eq_twice_card_edges]
  simp [← h, ← Finset.card_univ]

theorem is_perfect_matching_iff : M.IsPerfectMatching ↔ ∀ v, ∃! w, M.Adj v w := by
  refine' ⟨_, fun hm => ⟨fun v hv => hm v, fun v => _⟩⟩
  · rintro ⟨hm, hs⟩ v
    exact hm (hs v)
    
  · obtain ⟨w, hw, -⟩ := hm v
    exact M.edge_vert hw
    

theorem is_perfect_matching_iff_forall_degree {M : Subgraph G} [∀ v, Fintype (M.NeighborSet v)] :
    M.IsPerfectMatching ↔ ∀ v, M.degree v = 1 := by
  simp [← degree_eq_one_iff_unique_adj, ← is_perfect_matching_iff]

theorem IsPerfectMatching.even_card {M : Subgraph G} [Fintype V] (h : M.IsPerfectMatching) : Even (Fintype.card V) := by
  classical
  simpa [← h.2.card_verts] using is_matching.even_card h.1

end Subgraph

end SimpleGraph

