/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Ray
import Mathbin.Topology.LocalExtr

/-!
# (Local) maximums in a normed space

In this file we prove the following lemma, see `is_max_filter.norm_add_same_ray`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `λ x, ∥f x + y∥` has a maximul along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `is_max_filter`:
`is_max_on`, `is_local_max_on`, and `is_local_max`.

## Tags

local maximum, normed space
-/


variable {α X E : Type _} [SemiNormedGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

section

variable {f : α → E} {l : Filter α} {s : Set α} {c : α} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ∥f x + y∥` has a maximul
along `l` at `c`. -/
theorem IsMaxFilter.norm_add_same_ray (h : IsMaxFilter (norm ∘ f) l c) (hy : SameRay ℝ (f c) y) :
    IsMaxFilter (fun x => ∥f x + y∥) l c :=
  h.mono fun x hx =>
    calc
      ∥f x + y∥ ≤ ∥f x∥ + ∥y∥ := norm_add_le _ _
      _ ≤ ∥f c∥ + ∥y∥ := add_le_add_right hx _
      _ = ∥f c + y∥ := hy.norm_add.symm
      

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c`, then the function `λ x, ∥f x + f c∥` has a maximul along `l` at `c`. -/
theorem IsMaxFilter.norm_add_self (h : IsMaxFilter (norm ∘ f) l c) : IsMaxFilter (fun x => ∥f x + f c∥) l c :=
  h.norm_add_same_ray SameRay.rfl

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c` and
`y` is a vector on the same ray as `f c`, then the function `λ x, ∥f x + y∥` has a maximul on `s` at
`c`. -/
theorem IsMaxOn.norm_add_same_ray (h : IsMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsMaxOn (fun x => ∥f x + y∥) s c :=
  h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c`,
then the function `λ x, ∥f x + f c∥` has a maximul on `s` at `c`. -/
theorem IsMaxOn.norm_add_self (h : IsMaxOn (norm ∘ f) s c) : IsMaxOn (fun x => ∥f x + f c∥) s c :=
  h.norm_add_self

end

variable {f : X → E} {s : Set X} {c : X} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ∥f x + y∥` has a local
maximul on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_same_ray (h : IsLocalMaxOn (norm ∘ f) s c) (hy : SameRay ℝ (f c) y) :
    IsLocalMaxOn (fun x => ∥f x + y∥) s c :=
  h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c`, then the function `λ x, ∥f x + f c∥` has a local maximul on `s` at `c`. -/
theorem IsLocalMaxOn.norm_add_self (h : IsLocalMaxOn (norm ∘ f) s c) : IsLocalMaxOn (fun x => ∥f x + f c∥) s c :=
  h.norm_add_self

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c` and `y` is
a vector on the same ray as `f c`, then the function `λ x, ∥f x + y∥` has a local maximul at `c`. -/
theorem IsLocalMax.norm_add_same_ray (h : IsLocalMax (norm ∘ f) c) (hy : SameRay ℝ (f c) y) :
    IsLocalMax (fun x => ∥f x + y∥) c :=
  h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c`, then the
function `λ x, ∥f x + f c∥` has a local maximul at `c`. -/
theorem IsLocalMax.norm_add_self (h : IsLocalMax (norm ∘ f) c) : IsLocalMax (fun x => ∥f x + f c∥) c :=
  h.norm_add_self

