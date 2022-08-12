/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Combinatorics.SimpleGraph.Prod
import Mathbin.Data.Fin.SuccPred
import Mathbin.Order.SuccPred.Relation

/-!
# The Hasse diagram as a graph

This file defines the Hasse diagram of an order (graph of `covby`, the covering relation) and the
path graph on `n` vertices.

## Main declarations

* `simple_graph.hasse`: Hasse diagram of an order.
* `simple_graph.path_graph`: Path graph on `n` vertices.
-/


open Order OrderDual Relation

namespace SimpleGraph

variable (α β : Type _)

section Preorderₓ

variable [Preorderₓ α] [Preorderₓ β]

/-- The Hasse diagram of an order as a simple graph. The graph of the covering relation. -/
def hasse : SimpleGraph α where
  Adj := fun a b => a ⋖ b ∨ b ⋖ a
  symm := fun a b => Or.symm
  loopless := fun a h => h.elim (irrefl _) (irrefl _)

variable {α β} {a b : α}

@[simp]
theorem hasse_adj : (hasse α).Adj a b ↔ a ⋖ b ∨ b ⋖ a :=
  Iff.rfl

/-- `αᵒᵈ` and `α` have the same Hasse diagram. -/
def hasseDualIso : hasse αᵒᵈ ≃g hasse α :=
  { ofDual with
    map_rel_iff' := fun a b => by
      simp [← or_comm] }

@[simp]
theorem hasse_dual_iso_apply (a : αᵒᵈ) : hasseDualIso a = ofDual a :=
  rfl

@[simp]
theorem hasse_dual_iso_symm_apply (a : α) : hasseDualIso.symm a = toDual a :=
  rfl

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α] [PartialOrderₓ β]

@[simp]
theorem hasse_prod : hasse (α × β) = hasse α □ hasse β := by
  ext x y
  simp_rw [box_prod_adj, hasse_adj, Prod.covby_iff, or_and_distrib_right, @eq_comm _ y.1, @eq_comm _ y.2, or_or_or_comm]

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

theorem hasse_preconnected_of_succ [SuccOrder α] [IsSuccArchimedean α] : (hasse α).Preconnected := fun a b => by
  rw [reachable_iff_refl_trans_gen]
  exact
    refl_trans_gen_of_succ _ (fun c hc => Or.inl <| covby_succ_of_not_is_max hc.2.not_is_max) fun c hc =>
      Or.inr <| covby_succ_of_not_is_max hc.2.not_is_max

theorem hasse_preconnected_of_pred [PredOrder α] [IsPredArchimedean α] : (hasse α).Preconnected := fun a b => by
  rw [reachable_iff_refl_trans_gen, ← refl_trans_gen_swap]
  exact
    refl_trans_gen_of_pred _ (fun c hc => Or.inl <| pred_covby_of_not_is_min hc.1.not_is_min) fun c hc =>
      Or.inr <| pred_covby_of_not_is_min hc.1.not_is_min

end LinearOrderₓ

/-- The path graph on `n` vertices. -/
def pathGraph (n : ℕ) : SimpleGraph (Finₓ n) :=
  hasse _

theorem path_graph_preconnected (n : ℕ) : (pathGraph n).Preconnected :=
  hasse_preconnected_of_succ _

theorem path_graph_connected (n : ℕ) : (pathGraph (n + 1)).Connected :=
  ⟨path_graph_preconnected _⟩

end SimpleGraph

