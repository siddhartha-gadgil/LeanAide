import analysis.normed_space.basic
import analysis.normed_space.lattice_ordered_group

universes u v

theorem summable_of_summable_norm_ {α : Type u} {E : Type v} [normed_group E] [normed_space ℝ E] [complete_space E] {f : α → E} (hf : summable (λ (a : α), ∥f a∥)) : summable f := sorry