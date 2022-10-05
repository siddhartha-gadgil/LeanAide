import topology.algebra.continuous_monoid_hom
import group_theory.specific_groups.cyclic

universe u

theorem abelian_group_isomorphic_to_pontryagin_dual {G : Type u} [group G] [topological_space G] [fintype G] (h : is_cyclic G) : nonempty (G ≃* pontryagin_dual G) := sorry