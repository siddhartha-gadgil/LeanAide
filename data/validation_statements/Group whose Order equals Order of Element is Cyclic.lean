import group_theory.specific_groups.cyclic

universe u

theorem is_cyclic_of_order_eq_card {G : Type u} [group G] [fintype G] (g : G) (hg : order_of g = fintype.card G) : is_cyclic G := sorry