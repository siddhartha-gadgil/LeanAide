/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Parity
import Mathbin.Data.Zmod.Parity

/-!
# Degree-sum formula and handshaking lemma

The degree-sum formula is that the sum of the degrees of the vertices in
a finite graph is equal to twice the number of edges.  The handshaking lemma,
a corollary, is that the number of odd-degree vertices is even.

## Main definitions

- `simple_graph.sum_degrees_eq_twice_card_edges` is the degree-sum formula.
- `simple_graph.even_card_odd_degree_vertices` is the handshaking lemma.
- `simple_graph.odd_card_odd_degree_vertices_ne` is that the number of odd-degree
  vertices different from a given odd-degree vertex is odd.
- `simple_graph.exists_ne_odd_degree_of_exists_odd_degree` is that the existence of an
  odd-degree vertex implies the existence of another one.

## Implementation notes

We give a combinatorial proof by using the facts that (1) the map from
darts to vertices is such that each fiber has cardinality the degree
of the corresponding vertex and that (2) the map from darts to edges is 2-to-1.

## Tags

simple graphs, sums, degree-sum formula, handshaking lemma
-/


open Finset

open BigOperators

namespace SimpleGraph

universe u

variable {V : Type u} (G : SimpleGraph V)

section DegreeSum

variable [Fintype V] [DecidableRel G.Adj]

theorem dart_fst_fiber [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v) = univ.Image (G.dartOfNeighborSet v) := by
  ext d
  simp only [← mem_image, ← true_andₓ, ← mem_filter, ← SetCoe.exists, ← mem_univ, ← exists_prop_of_true]
  constructor
  · rintro rfl
    exact
      ⟨_, d.is_adj, by
        ext <;> rfl⟩
    
  · rintro ⟨e, he, rfl⟩
    rfl
    

theorem dart_fst_fiber_card_eq_degree [DecidableEq V] (v : V) :
    (univ.filter fun d : G.Dart => d.fst = v).card = G.degree v := by
  simpa only [← dart_fst_fiber, ← Finset.card_univ, ← card_neighbor_set_eq_degree] using
    card_image_of_injective univ (G.dart_of_neighbor_set_injective v)

theorem dart_card_eq_sum_degrees : Fintype.card G.Dart = ∑ v, G.degree v := by
  have := Classical.decEq V
  simp only [card_univ, dart_fst_fiber_card_eq_degree]
  exact
    card_eq_sum_card_fiberwise
      (by
        simp )

variable {G} [DecidableEq V]

theorem Dart.edge_fiber (d : G.Dart) : (univ.filter fun d' : G.Dart => d'.edge = d.edge) = {d, d.symm} :=
  Finset.ext fun d' => by
    simpa using dart_edge_eq_iff d' d

variable (G)

theorem dart_edge_fiber_card (e : Sym2 V) (h : e ∈ G.EdgeSet) : (univ.filter fun d : G.Dart => d.edge = e).card = 2 :=
  by
  refine' Sym2.ind (fun v w h => _) e h
  let d : G.dart := ⟨(v, w), h⟩
  convert congr_arg card d.edge_fiber
  rw [card_insert_of_not_mem, card_singleton]
  rw [mem_singleton]
  exact d.symm_ne.symm

theorem dart_card_eq_twice_card_edges : Fintype.card G.Dart = 2 * G.edgeFinset.card := by
  rw [← card_univ]
  rw
    [@card_eq_sum_card_fiberwise _ _ _ dart.edge _ G.edge_finset fun d h => by
      rw [mem_edge_finset]
      apply dart.edge_mem]
  rw [← mul_comm, sum_const_nat]
  intro e h
  apply G.dart_edge_fiber_card e
  rwa [← mem_edge_finset]

/-- The degree-sum formula.  This is also known as the handshaking lemma, which might
more specifically refer to `simple_graph.even_card_odd_degree_vertices`. -/
theorem sum_degrees_eq_twice_card_edges : (∑ v, G.degree v) = 2 * G.edgeFinset.card :=
  G.dart_card_eq_sum_degrees.symm.trans G.dart_card_eq_twice_card_edges

end DegreeSum

/-- The handshaking lemma.  See also `simple_graph.sum_degrees_eq_twice_card_edges`. -/
theorem even_card_odd_degree_vertices [Fintype V] [DecidableRel G.Adj] :
    Even (univ.filter fun v => Odd (G.degree v)).card := by
  classical
  have h := congr_arg (fun n => ↑n : ℕ → Zmod 2) G.sum_degrees_eq_twice_card_edges
  simp only [← Zmod.nat_cast_self, ← zero_mul, ← Nat.cast_mulₓ] at h
  rw [Nat.cast_sum, ← sum_filter_ne_zero] at h
  rw [@sum_congr _ _ _ _ (fun v => (G.degree v : Zmod 2)) (fun v => (1 : Zmod 2)) _ rfl] at h
  · simp only [← filter_congr_decidable, ← mul_oneₓ, ← nsmul_eq_mul, ← sum_const, ← Ne.def] at h
    rw [← Zmod.eq_zero_iff_even]
    convert h
    ext v
    rw [← Zmod.ne_zero_iff_odd]
    
  · intro v
    simp only [← true_andₓ, ← mem_filter, ← mem_univ, ← Ne.def]
    rw [Zmod.eq_zero_iff_even, Zmod.eq_one_iff_odd, Nat.odd_iff_not_even, imp_self]
    trivial
    

theorem odd_card_odd_degree_vertices_ne [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V)
    (h : Odd (G.degree v)) : Odd (univ.filter fun w => w ≠ v ∧ Odd (G.degree w)).card := by
  rcases G.even_card_odd_degree_vertices with ⟨k, hg⟩
  have hk : 0 < k := by
    have hh : (filter (fun v : V => Odd (G.degree v)) univ).Nonempty := by
      use v
      simp only [← true_andₓ, ← mem_filter, ← mem_univ]
      use h
    rwa [← card_pos, hg, ← two_mul, zero_lt_mul_left] at hh
    exact zero_lt_two
  have hc : (fun w : V => w ≠ v ∧ Odd (G.degree w)) = fun w : V => Odd (G.degree w) ∧ w ≠ v := by
    ext w
    rw [and_comm]
  simp only [← hc, ← filter_congr_decidable]
  rw [← filter_filter, filter_ne', card_erase_of_mem]
  · refine' ⟨k - 1, tsub_eq_of_eq_add <| hg.trans _⟩
    rw [add_assocₓ, one_add_one_eq_two, ← Nat.mul_succ, ← two_mul]
    congr
    exact (tsub_add_cancel_of_le <| Nat.succ_le_iff.2 hk).symm
    
  · simpa only [← true_andₓ, ← mem_filter, ← mem_univ]
    

theorem exists_ne_odd_degree_of_exists_odd_degree [Fintype V] [DecidableRel G.Adj] (v : V) (h : Odd (G.degree v)) :
    ∃ w : V, w ≠ v ∧ Odd (G.degree w) := by
  have := Classical.decEq V
  rcases G.odd_card_odd_degree_vertices_ne v h with ⟨k, hg⟩
  have hg' : (filter (fun w : V => w ≠ v ∧ Odd (G.degree w)) univ).card > 0 := by
    rw [hg]
    apply Nat.succ_posₓ
  rcases card_pos.mp hg' with ⟨w, hw⟩
  simp only [← true_andₓ, ← mem_filter, ← mem_univ, ← Ne.def] at hw
  exact ⟨w, hw⟩

end SimpleGraph

