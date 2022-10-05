import data.real.irrational
import topology.basic
import algebra.order.floor

/-- The fractional parts of the integer multiples of an irrational number form a dense subset of the unit interval. -/
theorem irrational_orbit_dense {α : ℝ} (hα_irrat : irrational α) : closure ((λ m : ℤ, int.fract (α * ↑m)) '' (@set.univ ℤ)) = set.Icc 0 1 := sorry

