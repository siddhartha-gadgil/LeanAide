/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Topology.FiberBundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `complex.re` and `complex.im`.

## Main statements

Each statement about `complex.re` listed below has a counterpart about `complex.im`.

* `complex.is_trivial_topological_fiber_bundle_re`: `complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `complex.is_open_map_re`, `complex.quotient_map_re`: in particular, `complex.re` is an open map
  and is a quotient map;
* `complex.interior_preimage_re`, `complex.closure_preimage_re`, `complex.frontier_preimage_re`:
  formulas for `interior (complex.re ⁻¹' s)` etc;
* `complex.interior_set_of_re_le` etc: particular cases of the above formulas in the cases when `s`
  is one of the infinite intervals `set.Ioi a`, `set.Ici a`, `set.Iio a`, and `set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/


open TopologicalFiberBundle Set

noncomputable section

namespace Complex

/-- `complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem is_trivial_topological_fiber_bundle_re : IsTrivialTopologicalFiberBundle ℝ re :=
  ⟨equivRealProdₗ.toHomeomorph, fun z => rfl⟩

/-- `complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem is_trivial_topological_fiber_bundle_im : IsTrivialTopologicalFiberBundle ℝ im :=
  ⟨equivRealProdₗ.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ), fun z => rfl⟩

theorem is_topological_fiber_bundle_re : IsTopologicalFiberBundle ℝ re :=
  is_trivial_topological_fiber_bundle_re.IsTopologicalFiberBundle

theorem is_topological_fiber_bundle_im : IsTopologicalFiberBundle ℝ im :=
  is_trivial_topological_fiber_bundle_im.IsTopologicalFiberBundle

theorem is_open_map_re : IsOpenMap re :=
  is_topological_fiber_bundle_re.is_open_map_proj

theorem is_open_map_im : IsOpenMap im :=
  is_topological_fiber_bundle_im.is_open_map_proj

theorem quotient_map_re : QuotientMap re :=
  is_topological_fiber_bundle_re.quotient_map_proj

theorem quotient_map_im : QuotientMap im :=
  is_topological_fiber_bundle_im.quotient_map_proj

theorem interior_preimage_re (s : Set ℝ) : Interior (re ⁻¹' s) = re ⁻¹' Interior s :=
  (is_open_map_re.preimage_interior_eq_interior_preimage continuous_re _).symm

theorem interior_preimage_im (s : Set ℝ) : Interior (im ⁻¹' s) = im ⁻¹' Interior s :=
  (is_open_map_im.preimage_interior_eq_interior_preimage continuous_im _).symm

theorem closure_preimage_re (s : Set ℝ) : Closure (re ⁻¹' s) = re ⁻¹' Closure s :=
  (is_open_map_re.preimage_closure_eq_closure_preimage continuous_re _).symm

theorem closure_preimage_im (s : Set ℝ) : Closure (im ⁻¹' s) = im ⁻¹' Closure s :=
  (is_open_map_im.preimage_closure_eq_closure_preimage continuous_im _).symm

theorem frontier_preimage_re (s : Set ℝ) : Frontier (re ⁻¹' s) = re ⁻¹' Frontier s :=
  (is_open_map_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm

theorem frontier_preimage_im (s : Set ℝ) : Frontier (im ⁻¹' s) = im ⁻¹' Frontier s :=
  (is_open_map_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm

@[simp]
theorem interior_set_of_re_le (a : ℝ) : Interior { z : ℂ | z.re ≤ a } = { z | z.re < a } := by
  simpa only [← interior_Iic] using interior_preimage_re (Iic a)

@[simp]
theorem interior_set_of_im_le (a : ℝ) : Interior { z : ℂ | z.im ≤ a } = { z | z.im < a } := by
  simpa only [← interior_Iic] using interior_preimage_im (Iic a)

@[simp]
theorem interior_set_of_le_re (a : ℝ) : Interior { z : ℂ | a ≤ z.re } = { z | a < z.re } := by
  simpa only [← interior_Ici] using interior_preimage_re (Ici a)

@[simp]
theorem interior_set_of_le_im (a : ℝ) : Interior { z : ℂ | a ≤ z.im } = { z | a < z.im } := by
  simpa only [← interior_Ici] using interior_preimage_im (Ici a)

@[simp]
theorem closure_set_of_re_lt (a : ℝ) : Closure { z : ℂ | z.re < a } = { z | z.re ≤ a } := by
  simpa only [← closure_Iio] using closure_preimage_re (Iio a)

@[simp]
theorem closure_set_of_im_lt (a : ℝ) : Closure { z : ℂ | z.im < a } = { z | z.im ≤ a } := by
  simpa only [← closure_Iio] using closure_preimage_im (Iio a)

@[simp]
theorem closure_set_of_lt_re (a : ℝ) : Closure { z : ℂ | a < z.re } = { z | a ≤ z.re } := by
  simpa only [← closure_Ioi] using closure_preimage_re (Ioi a)

@[simp]
theorem closure_set_of_lt_im (a : ℝ) : Closure { z : ℂ | a < z.im } = { z | a ≤ z.im } := by
  simpa only [← closure_Ioi] using closure_preimage_im (Ioi a)

@[simp]
theorem frontier_set_of_re_le (a : ℝ) : Frontier { z : ℂ | z.re ≤ a } = { z | z.re = a } := by
  simpa only [← frontier_Iic] using frontier_preimage_re (Iic a)

@[simp]
theorem frontier_set_of_im_le (a : ℝ) : Frontier { z : ℂ | z.im ≤ a } = { z | z.im = a } := by
  simpa only [← frontier_Iic] using frontier_preimage_im (Iic a)

@[simp]
theorem frontier_set_of_le_re (a : ℝ) : Frontier { z : ℂ | a ≤ z.re } = { z | z.re = a } := by
  simpa only [← frontier_Ici] using frontier_preimage_re (Ici a)

@[simp]
theorem frontier_set_of_le_im (a : ℝ) : Frontier { z : ℂ | a ≤ z.im } = { z | z.im = a } := by
  simpa only [← frontier_Ici] using frontier_preimage_im (Ici a)

@[simp]
theorem frontier_set_of_re_lt (a : ℝ) : Frontier { z : ℂ | z.re < a } = { z | z.re = a } := by
  simpa only [← frontier_Iio] using frontier_preimage_re (Iio a)

@[simp]
theorem frontier_set_of_im_lt (a : ℝ) : Frontier { z : ℂ | z.im < a } = { z | z.im = a } := by
  simpa only [← frontier_Iio] using frontier_preimage_im (Iio a)

@[simp]
theorem frontier_set_of_lt_re (a : ℝ) : Frontier { z : ℂ | a < z.re } = { z | z.re = a } := by
  simpa only [← frontier_Ioi] using frontier_preimage_re (Ioi a)

@[simp]
theorem frontier_set_of_lt_im (a : ℝ) : Frontier { z : ℂ | a < z.im } = { z | z.im = a } := by
  simpa only [← frontier_Ioi] using frontier_preimage_im (Ioi a)

theorem closure_re_prod_im (s t : Set ℝ) : Closure (s ×ℂ t) = Closure s ×ℂ Closure t := by
  simpa only [preimage_eq_preimage equiv_real_prodₗ.symm.to_homeomorph.surjective, ←
    equiv_real_prodₗ.symm.to_homeomorph.preimage_closure] using @closure_prod_eq _ _ _ _ s t

theorem interior_re_prod_im (s t : Set ℝ) : Interior (s ×ℂ t) = Interior s ×ℂ Interior t := by
  rw [re_prod_im, re_prod_im, interior_inter, interior_preimage_re, interior_preimage_im]

theorem frontier_re_prod_im (s t : Set ℝ) : Frontier (s ×ℂ t) = Closure s ×ℂ Frontier t ∪ Frontier s ×ℂ Closure t := by
  simpa only [preimage_eq_preimage equiv_real_prodₗ.symm.to_homeomorph.surjective, ←
    equiv_real_prodₗ.symm.to_homeomorph.preimage_frontier] using frontier_prod_eq s t

theorem frontier_set_of_le_re_and_le_im (a b : ℝ) :
    Frontier { z | a ≤ re z ∧ b ≤ im z } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ b ≤ im z } := by
  simpa only [← closure_Ici, ← frontier_Ici] using frontier_re_prod_im (Ici a) (Ici b)

theorem frontier_set_of_le_re_and_im_le (a b : ℝ) :
    Frontier { z | a ≤ re z ∧ im z ≤ b } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ im z ≤ b } := by
  simpa only [← closure_Ici, ← closure_Iic, ← frontier_Ici, ← frontier_Iic] using frontier_re_prod_im (Ici a) (Iic b)

end Complex

open Complex Metric

variable {s t : Set ℝ}

theorem IsOpen.re_prod_im (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)

theorem IsClosed.re_prod_im (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)

theorem Metric.Bounded.re_prod_im (hs : Bounded s) (ht : Bounded t) : Bounded (s ×ℂ t) :=
  equivRealProdₗ.antilipschitz.bounded_preimage (hs.Prod ht)

