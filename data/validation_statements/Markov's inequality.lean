import measure_theory.function.lp_space
import measure_theory.integral.lebesgue
import probability.integration

theorem markov_inequality {α : Type*} [probability_space α] {β : Type*} {M : measurable_space β} {X : α → β} (a : ℝ) (ha : 0 < a) (e : ennreal) (he : expectation X e) : expectation (⨅b∈(λ x, ⊤), {x : α // X x ∈ {b | b ≥ a}}) ≤ e / ⟨a, ha⟩ := sorry