/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Algebra.BigOperators.Order

/-!
# Double countings

This file gathers a few double counting arguments.

## Bipartite graphs

In a bipartite graph (considered as a relation `r : α → β → Prop`), we can bound the number of edges
between `s : finset α` and `t : finset β` by the minimum/maximum of edges over all `a ∈ s` times the
the size of `s`. Similarly for `t`. Combining those two yields inequalities between the sizes of `s`
and `t`.

* `bipartite_below`: `s.bipartite_below r b` are the elements of `s` below `b` wrt to `r`. Its size
  is the number of edges of `b` in `s`.
* `bipartite_above`: `t.bipartite_above r a` are the elements of `t` above `a` wrt to `r`. Its size
  is the number of edges of `a` in `t`.
* `card_mul_le_card_mul`, `card_mul_le_card_mul'`: Double counting the edges of a bipartite graph
  from below and from above.
* `card_mul_eq_card_mul`: Equality combination of the previous.
-/


open Finset Function

open BigOperators

/-! ### Bipartite graph -/


namespace Finset

section Bipartite

variable {α β : Type _} (r : α → β → Prop) (s : Finset α) (t : Finset β) (a a' : α) (b b' : β) [DecidablePred (r a)]
  [∀ a, Decidable (r a b)] {m n : ℕ}

/-- Elements of `s` which are "below" `b` according to relation `r`. -/
def bipartiteBelow : Finset α :=
  s.filter fun a => r a b

/-- Elements of `t` which are "above" `a` according to relation `r`. -/
def bipartiteAbove : Finset β :=
  t.filter (r a)

theorem bipartite_below_swap : t.bipartiteBelow (swap r) a = t.bipartiteAbove r a :=
  rfl

theorem bipartite_above_swap : s.bipartiteAbove (swap r) b = s.bipartiteBelow r b :=
  rfl

variable {s t a a' b b'}

@[simp]
theorem mem_bipartite_below {a : α} : a ∈ s.bipartiteBelow r b ↔ a ∈ s ∧ r a b :=
  mem_filter

@[simp]
theorem mem_bipartite_above {b : β} : b ∈ t.bipartiteAbove r a ↔ b ∈ t ∧ r a b :=
  mem_filter

theorem sum_card_bipartite_above_eq_sum_card_bipartite_below [∀ a b, Decidable (r a b)] :
    (∑ a in s, (t.bipartiteAbove r a).card) = ∑ b in t, (s.bipartiteBelow r b).card := by
  simp_rw [card_eq_sum_ones, bipartite_above, bipartite_below, sum_filter]
  exact sum_comm

/-- Double counting argument. Considering `r` as a bipartite graph, the LHS is a lower bound on the
number of edges while the RHS is an upper bound. -/
theorem card_mul_le_card_mul [∀ a b, Decidable (r a b)] (hm : ∀, ∀ a ∈ s, ∀, m ≤ (t.bipartiteAbove r a).card)
    (hn : ∀, ∀ b ∈ t, ∀, (s.bipartiteBelow r b).card ≤ n) : s.card * m ≤ t.card * n :=
  calc
    _ ≤ ∑ a in s, (t.bipartiteAbove r a).card := s.card_nsmul_le_sum _ _ hm
    _ = ∑ b in t, (s.bipartiteBelow r b).card := sum_card_bipartite_above_eq_sum_card_bipartite_below _
    _ ≤ _ := t.sum_le_card_nsmul _ _ hn
    

theorem card_mul_le_card_mul' [∀ a b, Decidable (r a b)] (hn : ∀, ∀ b ∈ t, ∀, n ≤ (s.bipartiteBelow r b).card)
    (hm : ∀, ∀ a ∈ s, ∀, (t.bipartiteAbove r a).card ≤ m) : t.card * n ≤ s.card * m :=
  card_mul_le_card_mul (swap r) hn hm

theorem card_mul_eq_card_mul [∀ a b, Decidable (r a b)] (hm : ∀, ∀ a ∈ s, ∀, (t.bipartiteAbove r a).card = m)
    (hn : ∀, ∀ b ∈ t, ∀, (s.bipartiteBelow r b).card = n) : s.card * m = t.card * n :=
  ((card_mul_le_card_mul _ fun a ha => (hm a ha).Ge) fun b hb => (hn b hb).le).antisymm <|
    (card_mul_le_card_mul' _ fun a ha => (hn a ha).Ge) fun b hb => (hm b hb).le

end Bipartite

end Finset

