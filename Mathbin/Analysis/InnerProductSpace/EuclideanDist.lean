/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.InnerProductSpace.Calculus
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean distance on a finite dimensional space

When we define a smooth bump function on a normed space, it is useful to have a smooth distance on
the space. Since the default distance is not guaranteed to be smooth, we define `to_euclidean` to be
an equivalence between a finite dimensional normed space and the standard Euclidean space of the
same dimension. Then we define `euclidean.dist x y = dist (to_euclidean x) (to_euclidean y)` and
provide some definitions (`euclidean.ball`, `euclidean.closed_ball`) and simple lemmas about this
distance. This way we hide the usage of `to_euclidean` behind an API.
-/


open TopologicalSpace

open Set

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- If `E` is a finite dimensional space over `ℝ`, then `to_euclidean` is a continuous `ℝ`-linear
equivalence between `E` and the Euclidean space of the same dimension. -/
def toEuclidean : E ≃L[ℝ] EuclideanSpace ℝ (Finₓ <| FiniteDimensional.finrank ℝ E) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclidean_space_fin.symm

namespace Euclidean

/-- If `x` and `y` are two points in a finite dimensional space over `ℝ`, then `euclidean.dist x y`
is the distance between these points in the metric defined by some inner product space structure on
`E`. -/
def dist (x y : E) : ℝ :=
  dist (toEuclidean x) (toEuclidean y)

/-- Closed ball w.r.t. the euclidean distance. -/
def ClosedBall (x : E) (r : ℝ) : Set E :=
  { y | dist y x ≤ r }

/-- Open ball w.r.t. the euclidean distance. -/
def Ball (x : E) (r : ℝ) : Set E :=
  { y | dist y x < r }

theorem ball_eq_preimage (x : E) (r : ℝ) : Ball x r = toEuclidean ⁻¹' Metric.Ball (toEuclidean x) r :=
  rfl

theorem closed_ball_eq_preimage (x : E) (r : ℝ) :
    ClosedBall x r = toEuclidean ⁻¹' Metric.ClosedBall (toEuclidean x) r :=
  rfl

theorem ball_subset_closed_ball {x : E} {r : ℝ} : Ball x r ⊆ ClosedBall x r := fun y (hy : _ < _) => le_of_ltₓ hy

theorem is_open_ball {x : E} {r : ℝ} : IsOpen (Ball x r) :=
  Metric.is_open_ball.Preimage toEuclidean.Continuous

theorem mem_ball_self {x : E} {r : ℝ} (hr : 0 < r) : x ∈ Ball x r :=
  Metric.mem_ball_self hr

theorem closed_ball_eq_image (x : E) (r : ℝ) :
    ClosedBall x r = toEuclidean.symm '' Metric.ClosedBall (toEuclidean x) r := by
  rw [to_euclidean.image_symm_eq_preimage, closed_ball_eq_preimage]

theorem is_compact_closed_ball {x : E} {r : ℝ} : IsCompact (ClosedBall x r) := by
  rw [closed_ball_eq_image]
  exact (is_compact_closed_ball _ _).Image to_euclidean.symm.continuous

theorem is_closed_closed_ball {x : E} {r : ℝ} : IsClosed (ClosedBall x r) :=
  is_compact_closed_ball.IsClosed

theorem closure_ball (x : E) {r : ℝ} (h : r ≠ 0) : Closure (Ball x r) = ClosedBall x r := by
  rw [ball_eq_preimage, ← to_euclidean.preimage_closure, closure_ball (toEuclidean x) h, closed_ball_eq_preimage]

theorem exists_pos_lt_subset_ball {R : ℝ} {s : Set E} {x : E} (hR : 0 < R) (hs : IsClosed s) (h : s ⊆ Ball x R) :
    ∃ r ∈ Ioo 0 R, s ⊆ Ball x r := by
  rw [ball_eq_preimage, ← image_subset_iff] at h
  rcases exists_pos_lt_subset_ball hR (to_euclidean.is_closed_image.2 hs) h with ⟨r, hr, hsr⟩
  exact ⟨r, hr, image_subset_iff.1 hsr⟩

theorem nhds_basis_closed_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (ClosedBall x) := by
  rw [to_euclidean.to_homeomorph.nhds_eq_comap]
  exact metric.nhds_basis_closed_ball.comap _

theorem closed_ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : ClosedBall x r ∈ 𝓝 x :=
  nhds_basis_closed_ball.mem_of_mem hr

theorem nhds_basis_ball {x : E} : (𝓝 x).HasBasis (fun r : ℝ => 0 < r) (Ball x) := by
  rw [to_euclidean.to_homeomorph.nhds_eq_comap]
  exact metric.nhds_basis_ball.comap _

theorem ball_mem_nhds {x : E} {r : ℝ} (hr : 0 < r) : Ball x r ∈ 𝓝 x :=
  nhds_basis_ball.mem_of_mem hr

end Euclidean

variable {F : Type _} [NormedGroup F] [NormedSpace ℝ F] {f g : F → E} {n : WithTop ℕ}

theorem ContDiff.euclidean_dist (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) (h : ∀ x, f x ≠ g x) :
    ContDiff ℝ n fun x => Euclidean.dist (f x) (g x) := by
  simp only [← Euclidean.dist]
  apply @ContDiff.dist ℝ
  exacts[(@toEuclidean E _ _ _).ContDiff.comp hf, (@toEuclidean E _ _ _).ContDiff.comp hg, fun x =>
    to_euclidean.injective.ne (h x)]

