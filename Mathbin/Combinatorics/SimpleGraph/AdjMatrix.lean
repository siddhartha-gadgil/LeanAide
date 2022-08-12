/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Combinatorics.SimpleGraph.Connectivity
import Mathbin.Data.Rel
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.LinearAlgebra.Matrix.Symmetric

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `matrix.is_adj_matrix`: `A : matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `matrix.is_adj_matrix.to_graph`: for `A : matrix V V α` and `h : A.is_adj_matrix`,
  `h.to_graph` is the simple graph induced by `A`.

* `matrix.compl`: for `A : matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `simple_graph.adj_matrix`: the adjacency matrix of a `simple_graph`.

* `simple_graph.adj_matrix_pow_apply_eq_card_walk`: each entry of the `n`th power of
  a graph's adjacency matrix counts the number of length-`n` walks between the corresponding
  pair of vertices.

-/


open BigOperators Matrix

open Finset Matrix SimpleGraph

variable {V α β : Type _}

namespace Matrix

/-- `A : matrix V V α` is qualified as an "adjacency matrix" if
    (1) every entry of `A` is `0` or `1`,
    (2) `A` is symmetric,
    (3) every diagonal entry of `A` is `0`. -/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : ∀ i j, A i j = 0 ∨ A i j = 1 := by
    run_tac
      obviously
  symm : A.IsSymm := by
    run_tac
      obviously
  apply_diag : ∀ i, A i i = 0 := by
    run_tac
      obviously

namespace IsAdjMatrix

variable {A : Matrix V V α}

@[simp]
theorem apply_diag_ne [MulZeroOneClassₓ α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) : ¬A i i = 1 := by
  simp [← h.apply_diag i]

@[simp]
theorem apply_ne_one_iff [MulZeroOneClassₓ α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) : ¬A i j = 1 ↔ A i j = 0 :=
  by
  obtain h | h := h.zero_or_one i j <;> simp [← h]

@[simp]
theorem apply_ne_zero_iff [MulZeroOneClassₓ α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) : ¬A i j = 0 ↔ A i j = 1 :=
  by
  rw [← apply_ne_one_iff h, not_not]

/-- For `A : matrix V V α` and `h : is_adj_matrix A`,
    `h.to_graph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
def toGraph [MulZeroOneClassₓ α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj := fun i j => A i j = 1
  symm := fun i j hij => by
    rwa [h.symm.apply i j]
  loopless := fun i => by
    simp [← h]

instance [MulZeroOneClassₓ α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) : DecidableRel h.toGraph.Adj := by
  simp only [← to_graph]
  infer_instance

end IsAdjMatrix

/-- For `A : matrix V V α`, `A.compl` is supposed to be the adjacency matrix of
    the complement graph of the graph induced by `A.adj_matrix`. -/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α := fun i j =>
  ite (i = j) 0 (ite (A i j = 0) 1 0)

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by
  simp [← compl]

@[simp]
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  unfold compl
  split_ifs <;> simp

@[simp]
theorem is_symm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [← compl, ← h.apply, ← eq_comm]

@[simp]
theorem is_adj_matrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by
      simp [← h] }

namespace IsAdjMatrix

variable {A}

@[simp]
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  is_adj_matrix_compl A h.symm

theorem to_graph_compl_eq [MulZeroOneClassₓ α] [Nontrivial α] (h : IsAdjMatrix A) : h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  cases' h.zero_or_one v w with h h <;> by_cases' hvw : v = w <;> simp [← Matrix.compl, ← h, ← hvw]

end IsAdjMatrix

end Compl

end Matrix

open Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (α)

/-- `adj_matrix G α` is the matrix `A` such that `A i j = (1 : α)` if `i` and `j` are
  adjacent in the simple graph `G`, and otherwise `A i j = 0`. -/
def adjMatrix [Zero α] [One α] : Matrix V V α
  | i, j => if G.Adj i j then 1 else 0

variable {α}

@[simp]
theorem adj_matrix_apply (v w : V) [Zero α] [One α] : G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl

@[simp]
theorem transpose_adj_matrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [← adj_comm]

@[simp]
theorem is_symm_adj_matrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adj_matrix G

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
theorem is_adj_matrix_adj_matrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix :=
  { zero_or_one := fun i j => by
      by_cases' G.adj i j <;> simp [← h] }

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
theorem to_graph_adj_matrix_eq [MulZeroOneClassₓ α] [Nontrivial α] : (G.is_adj_matrix_adj_matrix α).toGraph = G := by
  ext
  simp only [← is_adj_matrix.to_graph_adj, ← adj_matrix_apply, ← ite_eq_left_iff, ← zero_ne_one]
  apply not_not

variable {α} [Fintype V]

@[simp]
theorem adj_matrix_dot_product [NonAssocSemiringₓ α] (v : V) (vec : V → α) :
    dotProduct (G.adjMatrix α v) vec = ∑ u in G.neighborFinset v, vec u := by
  simp [← neighbor_finset_eq_filter, ← dot_product, ← sum_filter]

@[simp]
theorem dot_product_adj_matrix [NonAssocSemiringₓ α] (v : V) (vec : V → α) :
    dotProduct vec (G.adjMatrix α v) = ∑ u in G.neighborFinset v, vec u := by
  simp [← neighbor_finset_eq_filter, ← dot_product, ← sum_filter, ← Finset.sum_apply]

@[simp]
theorem adj_matrix_mul_vec_apply [NonAssocSemiringₓ α] (v : V) (vec : V → α) :
    ((G.adjMatrix α).mulVec vec) v = ∑ u in G.neighborFinset v, vec u := by
  rw [mul_vec, adj_matrix_dot_product]

@[simp]
theorem adj_matrix_vec_mul_apply [NonAssocSemiringₓ α] (v : V) (vec : V → α) :
    ((G.adjMatrix α).vecMul vec) v = ∑ u in G.neighborFinset v, vec u := by
  rw [← dot_product_adj_matrix, vec_mul]
  refine' congr rfl _
  ext
  rw [← transpose_apply (adj_matrix α G) x v, transpose_adj_matrix]

@[simp]
theorem adj_matrix_mul_apply [NonAssocSemiringₓ α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α ⬝ M) v w = ∑ u in G.neighborFinset v, M u w := by
  simp [← mul_apply, ← neighbor_finset_eq_filter, ← sum_filter]

@[simp]
theorem mul_adj_matrix_apply [NonAssocSemiringₓ α] (M : Matrix V V α) (v w : V) :
    (M ⬝ G.adjMatrix α) v w = ∑ u in G.neighborFinset w, M v u := by
  simp [← mul_apply, ← neighbor_finset_eq_filter, ← sum_filter, ← adj_comm]

variable (α)

@[simp]
theorem trace_adj_matrix [AddCommMonoidₓ α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [← Matrix.trace]

variable {α}

theorem adj_matrix_mul_self_apply_self [NonAssocSemiringₓ α] (i : V) :
    (G.adjMatrix α ⬝ G.adjMatrix α) i i = degree G i := by
  simp [← degree]

variable {G}

@[simp]
theorem adj_matrix_mul_vec_const_apply [Semiringₓ α] {a : α} {v : V} :
    (G.adjMatrix α).mulVec (Function.const _ a) v = G.degree v * a := by
  simp [← degree]

theorem adj_matrix_mul_vec_const_apply_of_regular [Semiringₓ α] {d : ℕ} {a : α} (hd : G.IsRegularOfDegree d) {v : V} :
    (G.adjMatrix α).mulVec (Function.const _ a) v = d * a := by
  simp [← hd v]

-- ./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc1.lean:253:2: unsupported tactic unify_equations
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: unify_equations ... #[[ident hqp, ident hrp]]
theorem adj_matrix_pow_apply_eq_card_walk [DecidableEq V] [Semiringₓ α] (n : ℕ) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction' n with n ih generalizing u v
  · obtain rfl | h := eq_or_ne u v <;> simp [← finset_walk_length, *]
    
  · nth_rw 0[Nat.succ_eq_one_add]
    simp only [← pow_addₓ, ← pow_oneₓ, ← finset_walk_length, ← ih, ← mul_eq_mul, ← adj_matrix_mul_apply]
    rw [Finset.card_bUnion]
    · norm_cast
      rw [Set.sum_indicator_subset _ (subset_univ (G.neighbor_finset u))]
      congr 2
      ext x
      split_ifs with hux <;> simp [← hux]
      
    -- Disjointness for card_bUnion
    · intro x hx y hy hxy p hp
      split_ifs  at hp with hx hy <;>
        simp only [← inf_eq_inter, ← empty_inter, ← inter_empty, ← not_mem_empty, ← mem_inter, ← mem_map, ←
            Function.Embedding.coe_fn_mk, ← exists_prop] at hp <;>
          try
            simpa using hp
      obtain ⟨⟨qx, hql, hqp⟩, ⟨rx, hrl, hrp⟩⟩ := hp
      «./././Mathport/Syntax/Translate/Tactic/Mathlib/Misc1.lean:253:2: unsupported tactic unify_equations»
      exact absurd rfl hxy
      
    

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClassₓ α] [Nontrivial α]

variable {A : Matrix V V α} (h : IsAdjMatrix A)

/-- If `A` is qualified as an adjacency matrix,
    then the adjacency matrix of the graph induced by `A` is itself. -/
theorem adj_matrix_to_graph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [← h']

end Matrix.IsAdjMatrix

