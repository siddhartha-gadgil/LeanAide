/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathbin.Algebra.Module.Ulift
import Mathbin.Order.LiminfLimsup
import Mathbin.Topology.Algebra.UniformGroup
import Mathbin.Topology.MetricSpace.Algebra
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.Sequences

/-!
# Normed (semi)groups

In this file we define four classes:

* `has_norm`, `has_nnnorm`: auxiliary classes endowing a type `α` with a function `norm : α → ℝ`
  (notation: `∥x∥`) and `nnnorm : α → ℝ≥0` (notation: `∥x∥₊`), respectively;
* `semi_normed_group`: a seminormed group is an additive group with a norm and a pseudo metric space
  structures that agree with each other: `∀ x y, dist x y = ∥x - y∥`;
* `normed_group`: a normed group is an additive group with a norm and a metric space structures that
  agree with each other: `∀ x y, dist x y = ∥x - y∥`.

We also prove basic properties of (semi)normed groups and provide some instances.

## Tags

normed group
-/


variable {α ι E F G : Type _}

open Filter Metric

open TopologicalSpace BigOperators Nnreal Ennreal uniformity Pointwise

/-- Auxiliary class, endowing a type `E` with a function `norm : E → ℝ` with notation `∥x∥`. This
class is designed to be extended in more interesting classes specifying the properties of the norm.
-/
class HasNorm (E : Type _) where
  norm : E → ℝ

export HasNorm (norm)

-- mathport name: «expr∥ ∥»
notation "∥" e "∥" => norm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class SemiNormedGroup (E : Type _) extends HasNorm E, AddCommGroupₓ E, PseudoMetricSpace E where
  dist_eq : ∀ x y : E, dist x y = norm (x - y)

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class NormedGroup (E : Type _) extends HasNorm E, AddCommGroupₓ E, MetricSpace E where
  dist_eq : ∀ x y : E, dist x y = norm (x - y)

/-- A normed group is a seminormed group. -/
-- see Note [lower instance priority]
instance (priority := 100) NormedGroup.toSemiNormedGroup [h : NormedGroup E] : SemiNormedGroup E :=
  { h with }

/-- Construct a seminormed group from a translation invariant pseudodistance. -/
def SemiNormedGroup.ofAddDist [HasNorm E] [AddCommGroupₓ E] [PseudoMetricSpace E] (H1 : ∀ x : E, ∥x∥ = dist x 0)
    (H2 : ∀ x y z : E, dist x y ≤ dist (x + z) (y + z)) :
    SemiNormedGroup E where dist_eq := fun x y => by
    rw [H1]
    apply le_antisymmₓ
    · rw [sub_eq_add_neg, ← add_right_negₓ y]
      apply H2
      
    · have := H2 (x - y) 0 y
      rwa [sub_add_cancel, zero_addₓ] at this
      

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def SemiNormedGroup.ofAddDist' [HasNorm E] [AddCommGroupₓ E] [PseudoMetricSpace E] (H1 : ∀ x : E, ∥x∥ = dist x 0)
    (H2 : ∀ x y z : E, dist (x + z) (y + z) ≤ dist x y) :
    SemiNormedGroup E where dist_eq := fun x y => by
    rw [H1]
    apply le_antisymmₓ
    · have := H2 (x - y) 0 y
      rwa [sub_add_cancel, zero_addₓ] at this
      
    · rw [sub_eq_add_neg, ← add_right_negₓ y]
      apply H2
      

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure SemiNormedGroup.Core (E : Type _) [AddCommGroupₓ E] [HasNorm E] : Prop where
  norm_zero : ∥(0 : E)∥ = 0
  triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥
  norm_neg : ∀ x : E, ∥-x∥ = ∥x∥

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. Note that in most
cases this instance creates bad definitional equalities (e.g., it does not take into account
a possibly existing `uniform_space` instance on `E`). -/
def SemiNormedGroup.ofCore (E : Type _) [AddCommGroupₓ E] [HasNorm E] (C : SemiNormedGroup.Core E) :
    SemiNormedGroup E where
  dist := fun x y => ∥x - y∥
  dist_eq := fun x y => by
    rfl
  dist_self := fun x => by
    simp [← C.norm_zero]
  dist_triangle := fun x y z =>
    calc
      ∥x - z∥ = ∥x - y + (y - z)∥ := by
        rw [sub_add_sub_cancel]
      _ ≤ ∥x - y∥ + ∥y - z∥ := C.triangle _ _
      
  dist_comm := fun x y =>
    calc
      ∥x - y∥ = ∥-(y - x)∥ := by
        simp
      _ = ∥y - x∥ := by
        rw [C.norm_neg]
      

instance : NormedGroup PUnit where
  norm := Function.const _ 0
  dist_eq := fun _ _ => rfl

@[simp]
theorem PUnit.norm_eq_zero (r : PUnit) : ∥r∥ = 0 :=
  rfl

noncomputable instance : NormedGroup ℝ where
  norm := fun x => abs x
  dist_eq := fun x y => rfl

@[simp]
theorem Real.norm_eq_abs (r : ℝ) : ∥r∥ = abs r :=
  rfl

section SemiNormedGroup

variable [SemiNormedGroup E] [SemiNormedGroup F] [SemiNormedGroup G]

theorem dist_eq_norm (g h : E) : dist g h = ∥g - h∥ :=
  SemiNormedGroup.dist_eq _ _

theorem dist_eq_norm' (g h : E) : dist g h = ∥h - g∥ := by
  rw [dist_comm, dist_eq_norm]

@[simp]
theorem dist_zero_right (g : E) : dist g 0 = ∥g∥ := by
  rw [dist_eq_norm, sub_zero]

@[simp]
theorem dist_zero_left : dist (0 : E) = norm :=
  funext fun g => by
    rw [dist_comm, dist_zero_right]

theorem Isometry.norm_map_of_map_zero {f : E → F} (hi : Isometry f) (h0 : f 0 = 0) (x : E) : ∥f x∥ = ∥x∥ := by
  rw [← dist_zero_right, ← h0, hi.dist_eq, dist_zero_right]

theorem tendsto_norm_cocompact_at_top [ProperSpace E] : Tendsto norm (cocompact E) atTop := by
  simpa only [← dist_zero_right] using tendsto_dist_right_cocompact_at_top (0 : E)

theorem norm_sub_rev (g h : E) : ∥g - h∥ = ∥h - g∥ := by
  simpa only [← dist_eq_norm] using dist_comm g h

@[simp]
theorem norm_neg (g : E) : ∥-g∥ = ∥g∥ := by
  simpa using norm_sub_rev 0 g

@[simp]
theorem dist_add_left (g h₁ h₂ : E) : dist (g + h₁) (g + h₂) = dist h₁ h₂ := by
  simp [← dist_eq_norm]

@[simp]
theorem dist_add_right (g₁ g₂ h : E) : dist (g₁ + h) (g₂ + h) = dist g₁ g₂ := by
  simp [← dist_eq_norm]

theorem dist_neg (x y : E) : dist (-x) y = dist x (-y) := by
  simp_rw [dist_eq_norm, ← norm_neg (-x - y), neg_sub, sub_neg_eq_add, add_commₓ]

@[simp]
theorem dist_neg_neg (g h : E) : dist (-g) (-h) = dist g h := by
  rw [dist_neg, neg_negₓ]

@[simp]
theorem dist_sub_left (g h₁ h₂ : E) : dist (g - h₁) (g - h₂) = dist h₁ h₂ := by
  simp only [← sub_eq_add_neg, ← dist_add_left, ← dist_neg_neg]

@[simp]
theorem dist_sub_right (g₁ g₂ h : E) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ := by
  simpa only [← sub_eq_add_neg] using dist_add_right _ _ _

@[simp]
theorem dist_self_add_right (g h : E) : dist g (g + h) = ∥h∥ := by
  rw [← dist_zero_left, ← dist_add_left g 0 h, add_zeroₓ]

@[simp]
theorem dist_self_add_left (g h : E) : dist (g + h) g = ∥h∥ := by
  rw [dist_comm, dist_self_add_right]

@[simp]
theorem dist_self_sub_right (g h : E) : dist g (g - h) = ∥h∥ := by
  rw [sub_eq_add_neg, dist_self_add_right, norm_neg]

@[simp]
theorem dist_self_sub_left (g h : E) : dist (g - h) g = ∥h∥ := by
  rw [dist_comm, dist_self_sub_right]

/-- In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. TODO: use
`bornology.cobounded` instead of `filter.comap has_norm.norm filter.at_top`. -/
theorem Filter.tendsto_neg_cobounded : Tendsto (Neg.neg : E → E) (comap norm atTop) (comap norm atTop) := by
  simpa only [← norm_neg, ← tendsto_comap_iff, ← (· ∘ ·)] using tendsto_comap

/-- **Triangle inequality** for the norm. -/
theorem norm_add_le (g h : E) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ := by
  simpa [← dist_eq_norm] using dist_triangle g 0 (-h)

theorem norm_add_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) : ∥g₁ + g₂∥ ≤ n₁ + n₂ :=
  le_transₓ (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

theorem norm_add₃_le (x y z : E) : ∥x + y + z∥ ≤ ∥x∥ + ∥y∥ + ∥z∥ :=
  norm_add_le_of_le (norm_add_le _ _) le_rfl

theorem dist_add_add_le (g₁ g₂ h₁ h₂ : E) : dist (g₁ + g₂) (h₁ + h₂) ≤ dist g₁ h₁ + dist g₂ h₂ := by
  simpa only [← dist_add_left, ← dist_add_right] using dist_triangle (g₁ + g₂) (h₁ + g₂) (h₁ + h₂)

theorem dist_add_add_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
    dist (g₁ + g₂) (h₁ + h₂) ≤ d₁ + d₂ :=
  le_transₓ (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem dist_sub_sub_le (g₁ g₂ h₁ h₂ : E) : dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁ + dist g₂ h₂ := by
  simpa only [← sub_eq_add_neg, ← dist_neg_neg] using dist_add_add_le g₁ (-g₂) h₁ (-h₂)

theorem dist_sub_sub_le_of_le {g₁ g₂ h₁ h₂ : E} {d₁ d₂ : ℝ} (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
    dist (g₁ - g₂) (h₁ - h₂) ≤ d₁ + d₂ :=
  le_transₓ (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

theorem abs_dist_sub_le_dist_add_add (g₁ g₂ h₁ h₂ : E) : abs (dist g₁ h₁ - dist g₂ h₂) ≤ dist (g₁ + g₂) (h₁ + h₂) := by
  simpa only [← dist_add_left, ← dist_add_right, ← dist_comm h₂] using abs_dist_sub_le (g₁ + g₂) (h₁ + h₂) (h₁ + g₂)

@[simp]
theorem norm_nonneg (g : E) : 0 ≤ ∥g∥ := by
  rw [← dist_zero_right]
  exact dist_nonneg

@[simp]
theorem norm_zero : ∥(0 : E)∥ = 0 := by
  rw [← dist_zero_right, dist_self]

theorem ne_zero_of_norm_ne_zero {g : E} : ∥g∥ ≠ 0 → g ≠ 0 :=
  mt <| by
    rintro rfl
    exact norm_zero

@[nontriviality]
theorem norm_of_subsingleton [Subsingleton E] (x : E) : ∥x∥ = 0 := by
  rw [Subsingleton.elimₓ x 0, norm_zero]

theorem norm_sum_le (s : Finset ι) (f : ι → E) : ∥∑ i in s, f i∥ ≤ ∑ i in s, ∥f i∥ :=
  s.le_sum_of_subadditive norm norm_zero norm_add_le f

theorem norm_sum_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ} (h : ∀, ∀ b ∈ s, ∀, ∥f b∥ ≤ n b) :
    ∥∑ b in s, f b∥ ≤ ∑ b in s, n b :=
  le_transₓ (norm_sum_le s f) (Finset.sum_le_sum h)

theorem dist_sum_sum_le_of_le (s : Finset ι) {f g : ι → E} {d : ι → ℝ} (h : ∀, ∀ b ∈ s, ∀, dist (f b) (g b) ≤ d b) :
    dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, d b := by
  simp only [← dist_eq_norm, Finset.sum_sub_distrib] at *
  exact norm_sum_le_of_le s h

theorem dist_sum_sum_le (s : Finset ι) (f g : ι → E) :
    dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, dist (f b) (g b) :=
  dist_sum_sum_le_of_le s fun _ _ => le_rfl

theorem norm_sub_le (g h : E) : ∥g - h∥ ≤ ∥g∥ + ∥h∥ := by
  simpa [← dist_eq_norm] using dist_triangle g 0 h

theorem norm_sub_le_of_le {g₁ g₂ : E} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) : ∥g₁ - g₂∥ ≤ n₁ + n₂ :=
  le_transₓ (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

theorem dist_le_norm_add_norm (g h : E) : dist g h ≤ ∥g∥ + ∥h∥ := by
  rw [dist_eq_norm]
  apply norm_sub_le

theorem abs_norm_sub_norm_le (g h : E) : abs (∥g∥ - ∥h∥) ≤ ∥g - h∥ := by
  simpa [← dist_eq_norm] using abs_dist_sub_le g h 0

theorem norm_sub_norm_le (g h : E) : ∥g∥ - ∥h∥ ≤ ∥g - h∥ :=
  le_transₓ (le_abs_self _) (abs_norm_sub_norm_le g h)

theorem dist_norm_norm_le (g h : E) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
  abs_norm_sub_norm_le g h

/-- The direct path from `0` to `v` is shorter than the path with `u` inserted in between. -/
theorem norm_le_insert (u v : E) : ∥v∥ ≤ ∥u∥ + ∥u - v∥ :=
  calc
    ∥v∥ = ∥u - (u - v)∥ := by
      abel
    _ ≤ ∥u∥ + ∥u - v∥ := norm_sub_le u _
    

theorem norm_le_insert' (u v : E) : ∥u∥ ≤ ∥v∥ + ∥u - v∥ := by
  rw [norm_sub_rev]
  exact norm_le_insert v u

theorem norm_le_add_norm_add (u v : E) : ∥u∥ ≤ ∥u + v∥ + ∥v∥ :=
  calc
    ∥u∥ = ∥u + v - v∥ := by
      rw [add_sub_cancel]
    _ ≤ ∥u + v∥ + ∥v∥ := norm_sub_le _ _
    

theorem ball_eq (y : E) (ε : ℝ) : Metric.Ball y ε = { x | ∥x - y∥ < ε } := by
  ext
  simp [← dist_eq_norm]

theorem ball_zero_eq (ε : ℝ) : Ball (0 : E) ε = { x | ∥x∥ < ε } :=
  Set.ext fun a => by
    simp

theorem mem_ball_iff_norm {g h : E} {r : ℝ} : h ∈ Ball g r ↔ ∥h - g∥ < r := by
  rw [mem_ball, dist_eq_norm]

theorem add_mem_ball_iff_norm {g h : E} {r : ℝ} : g + h ∈ Ball g r ↔ ∥h∥ < r := by
  rw [mem_ball_iff_norm, add_sub_cancel']

theorem mem_ball_iff_norm' {g h : E} {r : ℝ} : h ∈ Ball g r ↔ ∥g - h∥ < r := by
  rw [mem_ball', dist_eq_norm]

@[simp]
theorem mem_ball_zero_iff {ε : ℝ} {x : E} : x ∈ Ball (0 : E) ε ↔ ∥x∥ < ε := by
  rw [mem_ball, dist_zero_right]

theorem mem_closed_ball_iff_norm {g h : E} {r : ℝ} : h ∈ ClosedBall g r ↔ ∥h - g∥ ≤ r := by
  rw [mem_closed_ball, dist_eq_norm]

@[simp]
theorem mem_closed_ball_zero_iff {ε : ℝ} {x : E} : x ∈ ClosedBall (0 : E) ε ↔ ∥x∥ ≤ ε := by
  rw [mem_closed_ball, dist_zero_right]

theorem add_mem_closed_ball_iff_norm {g h : E} {r : ℝ} : g + h ∈ ClosedBall g r ↔ ∥h∥ ≤ r := by
  rw [mem_closed_ball_iff_norm, add_sub_cancel']

theorem mem_closed_ball_iff_norm' {g h : E} {r : ℝ} : h ∈ ClosedBall g r ↔ ∥g - h∥ ≤ r := by
  rw [mem_closed_ball', dist_eq_norm]

theorem norm_le_of_mem_closed_ball {g h : E} {r : ℝ} (H : h ∈ ClosedBall g r) : ∥h∥ ≤ ∥g∥ + r :=
  calc
    ∥h∥ = ∥g + (h - g)∥ := by
      rw [add_sub_cancel'_right]
    _ ≤ ∥g∥ + ∥h - g∥ := norm_add_le _ _
    _ ≤ ∥g∥ + r := by
      apply add_le_add_left
      rw [← dist_eq_norm]
      exact H
    

theorem norm_le_norm_add_const_of_dist_le {a b : E} {c : ℝ} (h : dist a b ≤ c) : ∥a∥ ≤ ∥b∥ + c :=
  norm_le_of_mem_closed_ball h

theorem norm_lt_of_mem_ball {g h : E} {r : ℝ} (H : h ∈ Ball g r) : ∥h∥ < ∥g∥ + r :=
  calc
    ∥h∥ = ∥g + (h - g)∥ := by
      rw [add_sub_cancel'_right]
    _ ≤ ∥g∥ + ∥h - g∥ := norm_add_le _ _
    _ < ∥g∥ + r := by
      apply add_lt_add_left
      rw [← dist_eq_norm]
      exact H
    

theorem norm_lt_norm_add_const_of_dist_lt {a b : E} {c : ℝ} (h : dist a b < c) : ∥a∥ < ∥b∥ + c :=
  norm_lt_of_mem_ball h

theorem bounded_iff_forall_norm_le {s : Set E} : Bounded s ↔ ∃ C, ∀, ∀ x ∈ s, ∀, ∥x∥ ≤ C := by
  simpa only [← Set.subset_def, ← mem_closed_ball_iff_norm, ← sub_zero] using bounded_iff_subset_ball (0 : E)

@[simp]
theorem preimage_add_ball (x y : E) (r : ℝ) : (· + ·) y ⁻¹' Ball x r = Ball (x - y) r := by
  ext z
  simp only [← dist_eq_norm, ← Set.mem_preimage, ← mem_ball]
  abel

@[simp]
theorem preimage_add_closed_ball (x y : E) (r : ℝ) : (· + ·) y ⁻¹' ClosedBall x r = ClosedBall (x - y) r := by
  ext z
  simp only [← dist_eq_norm, ← Set.mem_preimage, ← mem_closed_ball]
  abel

@[simp]
theorem mem_sphere_iff_norm (v w : E) (r : ℝ) : w ∈ Sphere v r ↔ ∥w - v∥ = r := by
  simp [← dist_eq_norm]

@[simp]
theorem mem_sphere_zero_iff_norm {w : E} {r : ℝ} : w ∈ Sphere (0 : E) r ↔ ∥w∥ = r := by
  simp [← dist_eq_norm]

@[simp]
theorem norm_eq_of_mem_sphere {r : ℝ} (x : Sphere (0 : E) r) : ∥(x : E)∥ = r :=
  mem_sphere_zero_iff_norm.mp x.2

theorem preimage_add_sphere (x y : E) (r : ℝ) : (· + ·) y ⁻¹' Sphere x r = Sphere (x - y) r := by
  ext z
  simp only [← Set.mem_preimage, ← mem_sphere_iff_norm]
  abel

theorem ne_zero_of_mem_sphere {r : ℝ} (hr : r ≠ 0) (x : Sphere (0 : E) r) : (x : E) ≠ 0 :=
  ne_zero_of_norm_ne_zero <| by
    rwa [norm_eq_of_mem_sphere x]

theorem ne_zero_of_mem_unit_sphere (x : Sphere (0 : E) 1) : (x : E) ≠ 0 :=
  ne_zero_of_mem_sphere one_ne_zero _

namespace Isometric

/-- Addition `y ↦ y + x` as an `isometry`. -/
-- TODO This material is superseded by similar constructions such as
-- `affine_isometry_equiv.const_vadd`; deduplicate
protected def addRight (x : E) : E ≃ᵢ E :=
  { Equivₓ.addRight x with isometry_to_fun := isometry_emetric_iff_metric.2 fun y z => dist_add_right _ _ _ }

@[simp]
theorem add_right_to_equiv (x : E) : (Isometric.addRight x).toEquiv = Equivₓ.addRight x :=
  rfl

@[simp]
theorem coe_add_right (x : E) : (Isometric.addRight x : E → E) = fun y => y + x :=
  rfl

theorem add_right_apply (x y : E) : (Isometric.addRight x : E → E) y = y + x :=
  rfl

@[simp]
theorem add_right_symm (x : E) : (Isometric.addRight x).symm = Isometric.addRight (-x) :=
  ext fun y => rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def addLeft (x : E) : E ≃ᵢ E where
  isometry_to_fun := isometry_emetric_iff_metric.2 fun y z => dist_add_left _ _ _
  toEquiv := Equivₓ.addLeft x

@[simp]
theorem add_left_to_equiv (x : E) : (Isometric.addLeft x).toEquiv = Equivₓ.addLeft x :=
  rfl

@[simp]
theorem coe_add_left (x : E) : ⇑(Isometric.addLeft x) = (· + ·) x :=
  rfl

@[simp]
theorem add_left_symm (x : E) : (Isometric.addLeft x).symm = Isometric.addLeft (-x) :=
  ext fun y => rfl

variable (E)

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg : E ≃ᵢ E where
  isometry_to_fun := isometry_emetric_iff_metric.2 fun x y => dist_neg_neg _ _
  toEquiv := Equivₓ.neg E

variable {E}

@[simp]
theorem neg_symm : (Isometric.neg E).symm = Isometric.neg E :=
  rfl

@[simp]
theorem neg_to_equiv : (Isometric.neg E).toEquiv = Equivₓ.neg E :=
  rfl

@[simp]
theorem coe_neg : ⇑(Isometric.neg E) = Neg.neg :=
  rfl

end Isometric

theorem NormedGroup.tendsto_nhds_zero {f : α → E} {l : Filter α} :
    Tendsto f l (𝓝 0) ↔ ∀, ∀ ε > 0, ∀, ∀ᶠ x in l, ∥f x∥ < ε :=
  Metric.tendsto_nhds.trans <| by
    simp only [← dist_zero_right]

theorem NormedGroup.tendsto_nhds_nhds {f : E → F} {x : E} {y : F} :
    Tendsto f (𝓝 x) (𝓝 y) ↔ ∀, ∀ ε > 0, ∀, ∃ δ > 0, ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε := by
  simp_rw [Metric.tendsto_nhds_nhds, dist_eq_norm]

theorem NormedGroup.cauchy_seq_iff [Nonempty α] [SemilatticeSup α] {u : α → E} :
    CauchySeq u ↔ ∀, ∀ ε > 0, ∀, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → ∥u m - u n∥ < ε := by
  simp [← Metric.cauchy_seq_iff, ← dist_eq_norm]

theorem NormedGroup.nhds_basis_norm_lt (x : E) : (𝓝 x).HasBasis (fun ε : ℝ => 0 < ε) fun ε : ℝ => { y | ∥y - x∥ < ε } :=
  by
  simp_rw [← ball_eq]
  exact Metric.nhds_basis_ball

theorem NormedGroup.nhds_zero_basis_norm_lt : (𝓝 (0 : E)).HasBasis (fun ε : ℝ => 0 < ε) fun ε : ℝ => { y | ∥y∥ < ε } :=
  by
  convert NormedGroup.nhds_basis_norm_lt (0 : E)
  simp

theorem NormedGroup.uniformity_basis_dist :
    (𝓤 E).HasBasis (fun ε : ℝ => 0 < ε) fun ε => { p : E × E | ∥p.fst - p.snd∥ < ε } := by
  convert Metric.uniformity_basis_dist
  simp [← dist_eq_norm]

open Finset

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
theorem AddMonoidHomClass.lipschitz_of_bound {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) : LipschitzWith (Real.toNnreal C) f :=
  LipschitzWith.of_dist_le' fun x y => by
    simpa only [← dist_eq_norm, ← map_sub] using h (x - y)

theorem lipschitz_on_with_iff_norm_sub_le {f : E → F} {C : ℝ≥0 } {s : Set E} :
    LipschitzOnWith C f s ↔ ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, ∥f x - f y∥ ≤ C * ∥x - y∥ := by
  simp only [← lipschitz_on_with_iff_dist_le_mul, ← dist_eq_norm]

theorem LipschitzOnWith.norm_sub_le {f : E → F} {C : ℝ≥0 } {s : Set E} (h : LipschitzOnWith C f s) {x y : E}
    (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C * ∥x - y∥ :=
  lipschitz_on_with_iff_norm_sub_le.mp h x x_in y y_in

theorem LipschitzOnWith.norm_sub_le_of_le {f : E → F} {C : ℝ≥0 } {s : Set E} (h : LipschitzOnWith C f s) {x y : E}
    (x_in : x ∈ s) (y_in : y ∈ s) {d : ℝ} (hd : ∥x - y∥ ≤ d) : ∥f x - f y∥ ≤ C * d :=
  (h.norm_sub_le x_in y_in).trans <| mul_le_mul_of_nonneg_left hd C.2

theorem lipschitz_with_iff_norm_sub_le {f : E → F} {C : ℝ≥0 } : LipschitzWith C f ↔ ∀ x y, ∥f x - f y∥ ≤ C * ∥x - y∥ :=
  by
  simp only [← lipschitz_with_iff_dist_le_mul, ← dist_eq_norm]

alias lipschitz_with_iff_norm_sub_le ↔ LipschitzWith.norm_sub_le _

theorem LipschitzWith.norm_sub_le_of_le {f : E → F} {C : ℝ≥0 } (h : LipschitzWith C f) {x y : E} {d : ℝ}
    (hd : ∥x - y∥ ≤ d) : ∥f x - f y∥ ≤ C * d :=
  (h.norm_sub_le x y).trans <| mul_le_mul_of_nonneg_left hd C.2

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`.  -/
theorem AddMonoidHomClass.continuous_of_bound {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) : Continuous f :=
  (AddMonoidHomClass.lipschitz_of_bound f C h).Continuous

theorem AddMonoidHomClass.uniform_continuous_of_bound {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ)
    (h : ∀ x, ∥f x∥ ≤ C * ∥x∥) : UniformContinuous f :=
  (AddMonoidHomClass.lipschitz_of_bound f C h).UniformContinuous

theorem IsCompact.exists_bound_of_continuous_on [TopologicalSpace α] {s : Set α} (hs : IsCompact s) {f : α → E}
    (hf : ContinuousOn f s) : ∃ C, ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ C := by
  have : bounded (f '' s) := (hs.image_of_continuous_on hf).Bounded
  rcases bounded_iff_forall_norm_le.1 this with ⟨C, hC⟩
  exact ⟨C, fun x hx => hC _ (Set.mem_image_of_mem _ hx)⟩

theorem AddMonoidHomClass.isometry_iff_norm {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) :
    Isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ := by
  simp only [← isometry_emetric_iff_metric, ← dist_eq_norm, map_sub]
  refine' ⟨fun h x => _, fun h x y => h _⟩
  simpa using h x 0

theorem AddMonoidHomClass.isometry_of_norm {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) (hf : ∀ x, ∥f x∥ = ∥x∥) :
    Isometry f :=
  (AddMonoidHomClass.isometry_iff_norm f).2 hf

theorem controlled_sum_of_mem_closure {s : AddSubgroup E} {g : E} (hg : g ∈ Closure (s : Set E)) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ v : ℕ → E,
      Tendsto (fun n => ∑ i in range (n + 1), v i) atTop (𝓝 g) ∧
        (∀ n, v n ∈ s) ∧ ∥v 0 - g∥ < b 0 ∧ ∀, ∀ n > 0, ∀, ∥v n∥ < b n :=
  by
  obtain ⟨u : ℕ → E, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 g)⟩ := mem_closure_iff_seq_limit.mp hg
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀, ∀ n ≥ n₀, ∀, ∥u n - g∥ < b 0 := by
    have : { x | ∥x - g∥ < b 0 } ∈ 𝓝 g := by
      simp_rw [← dist_eq_norm]
      exact Metric.ball_mem_nhds _ (b_pos _)
    exact filter.tendsto_at_top'.mp lim_u _ this
  set z : ℕ → E := fun n => u (n + n₀)
  have lim_z : tendsto z at_top (𝓝 g) := lim_u.comp (tendsto_add_at_top_nat n₀)
  have mem_𝓤 : ∀ n, { p : E × E | ∥p.1 - p.2∥ < b (n + 1) } ∈ 𝓤 E := fun n => by
    simpa [dist_eq_norm] using Metric.dist_mem_uniformity (b_pos <| n + 1)
  obtain ⟨φ : ℕ → ℕ, φ_extr : StrictMono φ, hφ : ∀ n, ∥z (φ <| n + 1) - z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤
  set w : ℕ → E := z ∘ φ
  have hw : tendsto w at_top (𝓝 g) := lim_z.comp φ_extr.tendsto_at_top
  set v : ℕ → E := fun i => if i = 0 then w 0 else w i - w (i - 1)
  refine' ⟨v, tendsto.congr (Finset.eq_sum_range_sub' w) hw, _, hn₀ _ (n₀.le_add_left _), _⟩
  · rintro ⟨⟩
    · change w 0 ∈ s
      apply u_in
      
    · apply s.sub_mem <;> apply u_in
      
    
  · intro l hl
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1
    exact Nat.exists_eq_succ_of_ne_zero (ne_of_gtₓ hl)
    apply hφ
    

theorem controlled_sum_of_mem_closure_range {j : E →+ F} {h : F} (Hh : h ∈ (Closure <| (j.range : Set F))) {b : ℕ → ℝ}
    (b_pos : ∀ n, 0 < b n) :
    ∃ g : ℕ → E,
      Tendsto (fun n => ∑ i in range (n + 1), j (g i)) atTop (𝓝 h) ∧
        ∥j (g 0) - h∥ < b 0 ∧ ∀, ∀ n > 0, ∀, ∥j (g n)∥ < b n :=
  by
  rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, v_in, hv₀, hv_pos⟩
  choose g hg using v_in
  change ∀ n : ℕ, j (g n) = v n at hg
  refine'
    ⟨g, by
      simpa [hg] using sum_v, by
      simpa [← hg 0] using hv₀, fun n hn => by
      simpa [← hg] using hv_pos n hn⟩

section Nnnorm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0` with notation `∥x∥₊`. -/
class HasNnnorm (E : Type _) where
  nnnorm : E → ℝ≥0

export HasNnnorm (nnnorm)

-- mathport name: «expr∥ ∥₊»
notation "∥" e "∥₊" => nnnorm e

-- see Note [lower instance priority]
instance (priority := 100) SemiNormedGroup.toHasNnnorm : HasNnnorm E :=
  ⟨fun a => ⟨norm a, norm_nonneg a⟩⟩

@[simp, norm_cast]
theorem coe_nnnorm (a : E) : (∥a∥₊ : ℝ) = norm a :=
  rfl

@[simp]
theorem coe_comp_nnnorm : (coe : ℝ≥0 → ℝ) ∘ (nnnorm : E → ℝ≥0 ) = norm :=
  rfl

theorem norm_to_nnreal {a : E} : ∥a∥.toNnreal = ∥a∥₊ :=
  @Real.to_nnreal_coe ∥a∥₊

theorem nndist_eq_nnnorm (a b : E) : nndist a b = ∥a - b∥₊ :=
  Nnreal.eq <| dist_eq_norm _ _

@[simp]
theorem nnnorm_zero : ∥(0 : E)∥₊ = 0 :=
  Nnreal.eq norm_zero

theorem ne_zero_of_nnnorm_ne_zero {g : E} : ∥g∥₊ ≠ 0 → g ≠ 0 :=
  mt <| by
    rintro rfl
    exact nnnorm_zero

theorem nnnorm_add_le (g h : E) : ∥g + h∥₊ ≤ ∥g∥₊ + ∥h∥₊ :=
  Nnreal.coe_le_coe.1 <| norm_add_le g h

@[simp]
theorem nnnorm_neg (g : E) : ∥-g∥₊ = ∥g∥₊ :=
  Nnreal.eq <| norm_neg g

theorem nndist_nnnorm_nnnorm_le (g h : E) : nndist ∥g∥₊ ∥h∥₊ ≤ ∥g - h∥₊ :=
  Nnreal.coe_le_coe.1 <| dist_norm_norm_le g h

/-- The direct path from `0` to `v` is shorter than the path with `u` inserted in between. -/
theorem nnnorm_le_insert (u v : E) : ∥v∥₊ ≤ ∥u∥₊ + ∥u - v∥₊ :=
  norm_le_insert u v

theorem nnnorm_le_insert' (u v : E) : ∥u∥₊ ≤ ∥v∥₊ + ∥u - v∥₊ :=
  norm_le_insert' u v

theorem nnnorm_le_add_nnnorm_add (u v : E) : ∥u∥₊ ≤ ∥u + v∥₊ + ∥v∥₊ :=
  norm_le_add_norm_add u v

theorem of_real_norm_eq_coe_nnnorm (x : E) : Ennreal.ofReal ∥x∥ = (∥x∥₊ : ℝ≥0∞) :=
  Ennreal.of_real_eq_coe_nnreal _

theorem edist_eq_coe_nnnorm_sub (x y : E) : edist x y = (∥x - y∥₊ : ℝ≥0∞) := by
  rw [edist_dist, dist_eq_norm, of_real_norm_eq_coe_nnnorm]

theorem edist_eq_coe_nnnorm (x : E) : edist x 0 = (∥x∥₊ : ℝ≥0∞) := by
  rw [edist_eq_coe_nnnorm_sub, _root_.sub_zero]

theorem mem_emetric_ball_zero_iff {x : E} {r : ℝ≥0∞} : x ∈ Emetric.Ball (0 : E) r ↔ ↑∥x∥₊ < r := by
  rw [Emetric.mem_ball, edist_eq_coe_nnnorm]

theorem nndist_add_add_le (g₁ g₂ h₁ h₂ : E) : nndist (g₁ + g₂) (h₁ + h₂) ≤ nndist g₁ h₁ + nndist g₂ h₂ :=
  Nnreal.coe_le_coe.1 <| dist_add_add_le g₁ g₂ h₁ h₂

theorem edist_add_add_le (g₁ g₂ h₁ h₂ : E) : edist (g₁ + g₂) (h₁ + h₂) ≤ edist g₁ h₁ + edist g₂ h₂ := by
  simp only [← edist_nndist]
  norm_cast
  apply nndist_add_add_le

@[simp]
theorem edist_add_left (g h₁ h₂ : E) : edist (g + h₁) (g + h₂) = edist h₁ h₂ := by
  simp [← edist_dist]

@[simp]
theorem edist_add_right (g₁ g₂ h : E) : edist (g₁ + h) (g₂ + h) = edist g₁ g₂ := by
  simp [← edist_dist]

theorem edist_neg (x y : E) : edist (-x) y = edist x (-y) := by
  simp_rw [edist_dist, dist_neg]

@[simp]
theorem edist_neg_neg (x y : E) : edist (-x) (-y) = edist x y := by
  rw [edist_neg, neg_negₓ]

@[simp]
theorem edist_sub_left (g h₁ h₂ : E) : edist (g - h₁) (g - h₂) = edist h₁ h₂ := by
  simp only [← sub_eq_add_neg, ← edist_add_left, ← edist_neg_neg]

@[simp]
theorem edist_sub_right (g₁ g₂ h : E) : edist (g₁ - h) (g₂ - h) = edist g₁ g₂ := by
  simpa only [← sub_eq_add_neg] using edist_add_right _ _ _

theorem nnnorm_sum_le (s : Finset ι) (f : ι → E) : ∥∑ a in s, f a∥₊ ≤ ∑ a in s, ∥f a∥₊ :=
  s.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le f

theorem nnnorm_sum_le_of_le (s : Finset ι) {f : ι → E} {n : ι → ℝ≥0 } (h : ∀, ∀ b ∈ s, ∀, ∥f b∥₊ ≤ n b) :
    ∥∑ b in s, f b∥₊ ≤ ∑ b in s, n b :=
  (norm_sum_le_of_le s h).trans_eq Nnreal.coe_sum.symm

theorem AddMonoidHomClass.lipschitz_of_bound_nnnorm {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) (C : ℝ≥0 )
    (h : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) : LipschitzWith C f :=
  @Real.to_nnreal_coe C ▸ AddMonoidHomClass.lipschitz_of_bound f C h

theorem AddMonoidHomClass.antilipschitz_of_bound {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0 }
    (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) : AntilipschitzWith K f :=
  AntilipschitzWith.of_le_mul_dist fun x y => by
    simpa only [← dist_eq_norm, ← map_sub] using h (x - y)

theorem AddMonoidHomClass.bound_of_antilipschitz {𝓕 : Type _} [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ≥0 }
    (h : AntilipschitzWith K f) (x) : ∥x∥ ≤ K * ∥f x∥ := by
  simpa only [← dist_zero_right, ← map_zero] using h.le_mul_dist x 0

end Nnnorm

namespace LipschitzWith

variable [PseudoEmetricSpace α] {K Kf Kg : ℝ≥0 } {f g : α → E}

theorem neg (hf : LipschitzWith K f) : LipschitzWith K fun x => -f x := fun x y =>
  (edist_neg_neg _ _).trans_le <| hf x y

theorem add (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) fun x => f x + g x :=
  fun x y =>
  calc
    edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) := edist_add_add_le _ _ _ _
    _ ≤ Kf * edist x y + Kg * edist x y := add_le_add (hf x y) (hg x y)
    _ = (Kf + Kg) * edist x y := (add_mulₓ _ _ _).symm
    

theorem sub (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) : LipschitzWith (Kf + Kg) fun x => f x - g x := by
  simpa only [← sub_eq_add_neg] using hf.add hg.neg

end LipschitzWith

namespace AntilipschitzWith

variable [PseudoEmetricSpace α] {K Kf Kg : ℝ≥0 } {f g : α → E}

theorem add_lipschitz_with (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg g) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ fun x => f x + g x := by
  let this : PseudoMetricSpace α := PseudoEmetricSpace.toPseudoMetricSpace hf.edist_ne_top
  refine' AntilipschitzWith.of_le_mul_dist fun x y => _
  rw [Nnreal.coe_inv, ← div_eq_inv_mul]
  rw [le_div_iff (Nnreal.coe_pos.2 <| tsub_pos_iff_lt.2 hK)]
  rw [mul_comm, Nnreal.coe_sub hK.le, sub_mul]
  calc ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :=
      sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)_ ≤ _ :=
      le_transₓ (le_abs_self _) (abs_dist_sub_le_dist_add_add _ _ _ _)

theorem add_sub_lipschitz_with (hf : AntilipschitzWith Kf f) (hg : LipschitzWith Kg (g - f)) (hK : Kg < Kf⁻¹) :
    AntilipschitzWith (Kf⁻¹ - Kg)⁻¹ g := by
  simpa only [← Pi.sub_apply, ← add_sub_cancel'_right] using hf.add_lipschitz_with hg hK

theorem le_mul_norm_sub {f : E → F} (hf : AntilipschitzWith K f) (x y : E) : ∥x - y∥ ≤ K * ∥f x - f y∥ := by
  simp [dist_eq_norm, ← hf.le_mul_dist x y]

end AntilipschitzWith

/-- A group homomorphism from an `add_comm_group` to a `semi_normed_group` induces a
`semi_normed_group` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def SemiNormedGroup.induced {E} [AddCommGroupₓ E] (f : E →+ F) : SemiNormedGroup E :=
  { PseudoMetricSpace.induced f SemiNormedGroup.toPseudoMetricSpace with norm := fun x => ∥f x∥,
    dist_eq := fun x y => by
      simpa only [← AddMonoidHom.map_sub, dist_eq_norm] }

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
instance AddSubgroup.semiNormedGroup (s : AddSubgroup E) : SemiNormedGroup s :=
  SemiNormedGroup.induced s.Subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp]
theorem AddSubgroup.coe_norm {E : Type _} [SemiNormedGroup E] {s : AddSubgroup E} (x : s) : ∥(x : s)∥ = ∥(x : E)∥ :=
  rfl

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `add_subgroup.coe_norm` for use by `norm_cast`.
-/
@[norm_cast]
theorem AddSubgroup.norm_coe {E : Type _} [SemiNormedGroup E] {s : AddSubgroup E} (x : s) : ∥(x : E)∥ = ∥(x : s)∥ :=
  rfl

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Submodule.semiNormedGroup {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
    (s : Submodule 𝕜 E) : SemiNormedGroup s where
  norm := fun x => norm (x : E)
  dist_eq := fun x y => dist_eq_norm (x : E) (y : E)

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `s` is equal to its
norm in `E`.

See note [implicit instance arguments]. -/
@[simp]
theorem Submodule.coe_norm {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
    {s : Submodule 𝕜 E} (x : s) : ∥(x : s)∥ = ∥(x : E)∥ :=
  rfl

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

This is a reversed version of the `simp` lemma `submodule.coe_norm` for use by `norm_cast`.

See note [implicit instance arguments]. -/
@[norm_cast]
theorem Submodule.norm_coe {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [SemiNormedGroup E] {_ : Module 𝕜 E}
    {s : Submodule 𝕜 E} (x : s) : ∥(x : E)∥ = ∥(x : s)∥ :=
  rfl

instance ULift.semiNormedGroup : SemiNormedGroup (ULift E) :=
  SemiNormedGroup.induced ⟨ULift.down, rfl, fun _ _ => rfl⟩

theorem ULift.norm_def (x : ULift E) : ∥x∥ = ∥x.down∥ :=
  rfl

theorem ULift.nnnorm_def (x : ULift E) : ∥x∥₊ = ∥x.down∥₊ :=
  rfl

@[simp]
theorem ULift.norm_up (x : E) : ∥ULift.up x∥ = ∥x∥ :=
  rfl

@[simp]
theorem ULift.nnnorm_up (x : E) : ∥ULift.up x∥₊ = ∥x∥₊ :=
  rfl

/-- seminormed group instance on the product of two seminormed groups, using the sup norm. -/
noncomputable instance Prod.semiNormedGroup : SemiNormedGroup (E × F) where
  norm := fun x => max ∥x.1∥ ∥x.2∥
  dist_eq := fun x y : E × F =>
    show max (dist x.1 y.1) (dist x.2 y.2) = max ∥(x - y).1∥ ∥(x - y).2∥ by
      simp [← dist_eq_norm]

theorem Prod.norm_def (x : E × F) : ∥x∥ = max ∥x.1∥ ∥x.2∥ :=
  rfl

theorem Prod.nnnorm_def (x : E × F) : ∥x∥₊ = max ∥x.1∥₊ ∥x.2∥₊ := by
  have := x.norm_def
  simp only [coe_nnnorm] at this
  exact_mod_cast this

theorem norm_fst_le (x : E × F) : ∥x.1∥ ≤ ∥x∥ :=
  le_max_leftₓ _ _

theorem norm_snd_le (x : E × F) : ∥x.2∥ ≤ ∥x∥ :=
  le_max_rightₓ _ _

theorem norm_prod_le_iff {x : E × F} {r : ℝ} : ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
  max_le_iff

/-- seminormed group instance on the product of finitely many seminormed groups,
using the sup norm. -/
noncomputable instance Pi.semiNormedGroup {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] :
    SemiNormedGroup (∀ i, π i) where
  norm := fun f => ↑(Finset.univ.sup fun b => ∥f b∥₊)
  dist_eq := fun x y =>
    congr_arg (coe : ℝ≥0 → ℝ) <|
      congr_arg (Finset.sup Finset.univ) <|
        funext fun a => show nndist (x a) (y a) = ∥x a - y a∥₊ from nndist_eq_nnnorm _ _

theorem Pi.norm_def {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (f : ∀ i, π i) :
    ∥f∥ = ↑(Finset.univ.sup fun b => ∥f b∥₊) :=
  rfl

theorem Pi.nnnorm_def {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (f : ∀ i, π i) :
    ∥f∥₊ = Finset.univ.sup fun b => ∥f b∥₊ :=
  Subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
theorem pi_norm_le_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ} (hr : 0 ≤ r) {x : ∀ i, π i} :
    ∥x∥ ≤ r ↔ ∀ i, ∥x i∥ ≤ r := by
  simp only [dist_zero_right, ← dist_pi_le_iff hr, ← Pi.zero_apply]

theorem pi_nnnorm_le_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ≥0 } {x : ∀ i, π i} :
    ∥x∥₊ ≤ r ↔ ∀ i, ∥x i∥₊ ≤ r :=
  pi_norm_le_iff r.coe_nonneg

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
theorem pi_norm_lt_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ} (hr : 0 < r) {x : ∀ i, π i} :
    ∥x∥ < r ↔ ∀ i, ∥x i∥ < r := by
  simp only [dist_zero_right, ← dist_pi_lt_iff hr, ← Pi.zero_apply]

theorem pi_nnnorm_lt_iff {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] {r : ℝ≥0 } (hr : 0 < r)
    {x : ∀ i, π i} : ∥x∥₊ < r ↔ ∀ i, ∥x i∥₊ < r :=
  pi_norm_lt_iff hr

theorem norm_le_pi_norm {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (x : ∀ i, π i) (i : ι) :
    ∥x i∥ ≤ ∥x∥ :=
  (pi_norm_le_iff (norm_nonneg x)).1 le_rfl i

theorem nnnorm_le_pi_nnnorm {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (x : ∀ i, π i) (i : ι) :
    ∥x i∥₊ ≤ ∥x∥₊ :=
  norm_le_pi_norm x i

@[simp]
theorem pi_norm_const [Nonempty ι] [Fintype ι] (a : E) : ∥fun i : ι => a∥ = ∥a∥ := by
  simpa only [dist_zero_right] using dist_pi_const a 0

@[simp]
theorem pi_nnnorm_const [Nonempty ι] [Fintype ι] (a : E) : ∥fun i : ι => a∥₊ = ∥a∥₊ :=
  Nnreal.eq <| pi_norm_const a

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
theorem Pi.sum_norm_apply_le_norm {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (x : ∀ i, π i) :
    (∑ i, ∥x i∥) ≤ Fintype.card ι • ∥x∥ :=
  calc
    (∑ i, ∥x i∥) ≤ ∑ i : ι, ∥x∥ := Finset.sum_le_sum fun i hi => norm_le_pi_norm x i
    _ = Fintype.card ι • ∥x∥ := Finset.sum_const _
    

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
theorem Pi.sum_nnnorm_apply_le_nnnorm {π : ι → Type _} [Fintype ι] [∀ i, SemiNormedGroup (π i)] (x : ∀ i, π i) :
    (∑ i, ∥x i∥₊) ≤ Fintype.card ι • ∥x∥₊ :=
  Nnreal.coe_sum.trans_le <| Pi.sum_norm_apply_le_norm x

theorem tendsto_iff_norm_tendsto_zero {f : α → E} {a : Filter α} {b : E} :
    Tendsto f a (𝓝 b) ↔ Tendsto (fun e => ∥f e - b∥) a (𝓝 0) := by
  convert tendsto_iff_dist_tendsto_zero
  simp [← dist_eq_norm]

theorem tendsto_zero_iff_norm_tendsto_zero {f : α → E} {a : Filter α} :
    Tendsto f a (𝓝 0) ↔ Tendsto (fun e => ∥f e∥) a (𝓝 0) := by
  rw [tendsto_iff_norm_tendsto_zero]
  simp only [← sub_zero]

theorem comap_norm_nhds_zero : comap norm (𝓝 0) = 𝓝 (0 : E) := by
  simpa only [← dist_zero_right] using nhds_comap_dist (0 : E)

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.order`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
theorem squeeze_zero_norm' {f : α → E} {g : α → ℝ} {t₀ : Filter α} (h : ∀ᶠ n in t₀, ∥f n∥ ≤ g n)
    (h' : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (eventually_of_forall fun n => norm_nonneg _) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
theorem squeeze_zero_norm {f : α → E} {g : α → ℝ} {t₀ : Filter α} (h : ∀ n, ∥f n∥ ≤ g n) (h' : Tendsto g t₀ (𝓝 0)) :
    Tendsto f t₀ (𝓝 0) :=
  squeeze_zero_norm' (eventually_of_forall h) h'

theorem tendsto_norm_sub_self (x : E) : Tendsto (fun g : E => ∥g - x∥) (𝓝 x) (𝓝 0) := by
  simpa [← dist_eq_norm] using tendsto_id.dist (tendsto_const_nhds : tendsto (fun g => (x : E)) (𝓝 x) _)

theorem tendsto_norm {x : E} : Tendsto (fun g : E => ∥g∥) (𝓝 x) (𝓝 ∥x∥) := by
  simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (fun g => (0 : E)) _ _)

theorem tendsto_norm_zero : Tendsto (fun g : E => ∥g∥) (𝓝 0) (𝓝 0) := by
  simpa using tendsto_norm_sub_self (0 : E)

@[continuity]
theorem continuous_norm : Continuous fun g : E => ∥g∥ := by
  simpa using continuous_id.dist (continuous_const : Continuous fun g => (0 : E))

@[continuity]
theorem continuous_nnnorm : Continuous fun a : E => ∥a∥₊ :=
  continuous_subtype_mk _ continuous_norm

theorem lipschitz_with_one_norm : LipschitzWith 1 (norm : E → ℝ) := by
  simpa only [← dist_zero_left] using LipschitzWith.dist_right (0 : E)

theorem lipschitz_with_one_nnnorm : LipschitzWith 1 (HasNnnorm.nnnorm : E → ℝ≥0 ) :=
  lipschitz_with_one_norm

theorem uniform_continuous_norm : UniformContinuous (norm : E → ℝ) :=
  lipschitz_with_one_norm.UniformContinuous

theorem uniform_continuous_nnnorm : UniformContinuous fun a : E => ∥a∥₊ :=
  uniform_continuous_subtype_mk uniform_continuous_norm _

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to zero
and a bounded function tends to zero. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ A * ∥x∥ * ∥y∥` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
theorem Filter.Tendsto.op_zero_is_bounded_under_le' {f : α → E} {g : α → F} {l : Filter α} (hf : Tendsto f l (𝓝 0))
    (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G) (h_op : ∃ A, ∀ x y, ∥op x y∥ ≤ A * ∥x∥ * ∥y∥) :
    Tendsto (fun x => op (f x) (g x)) l (𝓝 0) := by
  cases' h_op with A h_op
  rcases hg with ⟨C, hC⟩
  rw [eventually_map] at hC
  rw [NormedGroup.tendsto_nhds_zero] at hf⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine' (h_op _ _).trans_lt _
  cases' le_totalₓ A 0 with hA hA
  · exact
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA (norm_nonneg _)) (norm_nonneg _)).trans_lt ε₀
    
  calc A * ∥f i∥ * ∥g i∥ ≤ A * δ * C :=
      mul_le_mul (mul_le_mul_of_nonneg_left hf.le hA) hg (norm_nonneg _) (mul_nonneg hA δ₀.le)_ = A * C * δ :=
      mul_right_commₓ _ _ _ _ < ε := hδ

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to zero
and a bounded function tends to zero. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `∥op x y∥ ≤ ∥x∥ * ∥y∥` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
theorem Filter.Tendsto.op_zero_is_bounded_under_le {f : α → E} {g : α → F} {l : Filter α} (hf : Tendsto f l (𝓝 0))
    (hg : IsBoundedUnder (· ≤ ·) l (norm ∘ g)) (op : E → F → G) (h_op : ∀ x y, ∥op x y∥ ≤ ∥x∥ * ∥y∥) :
    Tendsto (fun x => op (f x) (g x)) l (𝓝 0) :=
  hf.op_zero_is_bounded_under_le' hg op ⟨1, fun x y => (one_mulₓ ∥x∥).symm ▸ h_op x y⟩

section

variable {l : Filter α} {f : α → E} {a : E}

theorem Filter.Tendsto.norm (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ∥f x∥) l (𝓝 ∥a∥) :=
  tendsto_norm.comp h

theorem Filter.Tendsto.nnnorm (h : Tendsto f l (𝓝 a)) : Tendsto (fun x => ∥f x∥₊) l (𝓝 ∥a∥₊) :=
  Tendsto.comp continuous_nnnorm.ContinuousAt h

end

section

variable [TopologicalSpace α] {f : α → E} {s : Set α} {a : α} {b : E}

theorem Continuous.norm (h : Continuous f) : Continuous fun x => ∥f x∥ :=
  continuous_norm.comp h

theorem Continuous.nnnorm (h : Continuous f) : Continuous fun x => ∥f x∥₊ :=
  continuous_nnnorm.comp h

theorem ContinuousAt.norm (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥) a :=
  h.norm

theorem ContinuousAt.nnnorm (h : ContinuousAt f a) : ContinuousAt (fun x => ∥f x∥₊) a :=
  h.nnnorm

theorem ContinuousWithinAt.norm (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ∥f x∥) s a :=
  h.norm

theorem ContinuousWithinAt.nnnorm (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => ∥f x∥₊) s a :=
  h.nnnorm

theorem ContinuousOn.norm (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥) s := fun x hx => (h x hx).norm

theorem ContinuousOn.nnnorm (h : ContinuousOn f s) : ContinuousOn (fun x => ∥f x∥₊) s := fun x hx => (h x hx).nnnorm

end

/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
theorem eventually_ne_of_tendsto_norm_at_top {l : Filter α} {f : α → E} (h : Tendsto (fun y => ∥f y∥) l atTop) (x : E) :
    ∀ᶠ y in l, f y ≠ x :=
  (h.eventually_ne_at_top _).mono fun x => ne_of_apply_ne norm

-- see Note [lower instance priority]
instance (priority := 100) SemiNormedGroup.has_lipschitz_add :
    HasLipschitzAdd E where lipschitz_add := ⟨2, LipschitzWith.prod_fst.add LipschitzWith.prod_snd⟩

/-- A seminormed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
-- see Note [lower instance priority]
instance (priority := 100) normed_uniform_group : UniformAddGroup E :=
  ⟨(LipschitzWith.prod_fst.sub LipschitzWith.prod_snd).UniformContinuous⟩

-- see Note [lower instance priority]
instance (priority := 100) normed_top_group : TopologicalAddGroup E := by
  infer_instance

-- short-circuit type class inference
theorem SemiNormedGroup.mem_closure_iff {s : Set E} {x : E} : x ∈ Closure s ↔ ∀, ∀ ε > 0, ∀, ∃ y ∈ s, ∥x - y∥ < ε := by
  simp [← Metric.mem_closure_iff, ← dist_eq_norm]

theorem norm_le_zero_iff' [T0Space E] {g : E} : ∥g∥ ≤ 0 ↔ g = 0 := by
  let this : NormedGroup E := { ‹SemiNormedGroup E› with toMetricSpace := Metric.ofT0PseudoMetricSpace E }
  rw [← dist_zero_right]
  exact dist_le_zero

theorem norm_eq_zero_iff' [T0Space E] {g : E} : ∥g∥ = 0 ↔ g = 0 :=
  (norm_nonneg g).le_iff_eq.symm.trans norm_le_zero_iff'

theorem norm_pos_iff' [T0Space E] {g : E} : 0 < ∥g∥ ↔ g ≠ 0 := by
  rw [← not_leₓ, norm_le_zero_iff']

theorem cauchy_seq_sum_of_eventually_eq {u v : ℕ → E} {N : ℕ} (huv : ∀, ∀ n ≥ N, ∀, u n = v n)
    (hv : CauchySeq fun n => ∑ k in range (n + 1), v k) : CauchySeq fun n => ∑ k in range (n + 1), u k := by
  let d : ℕ → E := fun n => ∑ k in range (n + 1), u k - v k
  rw
    [show (fun n => ∑ k in range (n + 1), u k) = d + fun n => ∑ k in range (n + 1), v k by
      ext n
      simp [← d]]
  have : ∀, ∀ n ≥ N, ∀, d n = d N := by
    intro n hn
    dsimp' [← d]
    rw [eventually_constant_sum _ hn]
    intro m hm
    simp [← huv m hm]
  exact (tendsto_at_top_of_eventually_const this).CauchySeq.add hv

end SemiNormedGroup

section NormedGroup

/-- Construct a normed group from a translation invariant distance -/
def NormedGroup.ofAddDist [HasNorm E] [AddCommGroupₓ E] [MetricSpace E] (H1 : ∀ x : E, ∥x∥ = dist x 0)
    (H2 : ∀ x y z : E, dist x y ≤ dist (x + z) (y + z)) :
    NormedGroup E where dist_eq := fun x y => by
    rw [H1]
    apply le_antisymmₓ
    · rw [sub_eq_add_neg, ← add_right_negₓ y]
      apply H2
      
    · have := H2 (x - y) 0 y
      rwa [sub_add_cancel, zero_addₓ] at this
      

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure NormedGroup.Core (E : Type _) [AddCommGroupₓ E] [HasNorm E] : Prop where
  norm_eq_zero_iff : ∀ x : E, ∥x∥ = 0 ↔ x = 0
  triangle : ∀ x y : E, ∥x + y∥ ≤ ∥x∥ + ∥y∥
  norm_neg : ∀ x : E, ∥-x∥ = ∥x∥

/-- The `semi_normed_group.core` induced by a `normed_group.core`. -/
theorem NormedGroup.Core.ToSemiNormedGroup.core {E : Type _} [AddCommGroupₓ E] [HasNorm E] (C : NormedGroup.Core E) :
    SemiNormedGroup.Core E :=
  { norm_zero := (C.norm_eq_zero_iff 0).2 rfl, triangle := C.triangle, norm_neg := C.norm_neg }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
def NormedGroup.ofCore (E : Type _) [AddCommGroupₓ E] [HasNorm E] (C : NormedGroup.Core E) : NormedGroup E :=
  { SemiNormedGroup.ofCore E (NormedGroup.Core.ToSemiNormedGroup.core C) with
    eq_of_dist_eq_zero := fun x y h => by
      rw [dist_eq_norm] at h
      exact sub_eq_zero.mp ((C.norm_eq_zero_iff _).1 h) }

variable [NormedGroup E] [NormedGroup F] {x y : E}

@[simp]
theorem norm_eq_zero {g : E} : ∥g∥ = 0 ↔ g = 0 :=
  norm_eq_zero_iff'

theorem norm_ne_zero_iff {g : E} : ∥g∥ ≠ 0 ↔ g ≠ 0 :=
  not_congr norm_eq_zero

@[simp]
theorem norm_pos_iff {g : E} : 0 < ∥g∥ ↔ g ≠ 0 :=
  norm_pos_iff'

@[simp]
theorem norm_le_zero_iff {g : E} : ∥g∥ ≤ 0 ↔ g = 0 :=
  norm_le_zero_iff'

theorem norm_sub_eq_zero_iff {u v : E} : ∥u - v∥ = 0 ↔ u = v := by
  rw [norm_eq_zero, sub_eq_zero]

theorem norm_sub_pos_iff : 0 < ∥x - y∥ ↔ x ≠ y := by
  rw [(norm_nonneg _).lt_iff_ne, ne_comm]
  exact norm_sub_eq_zero_iff.not

theorem eq_of_norm_sub_le_zero {g h : E} (a : ∥g - h∥ ≤ 0) : g = h := by
  rwa [← sub_eq_zero, ← norm_le_zero_iff]

theorem eq_of_norm_sub_eq_zero {u v : E} (h : ∥u - v∥ = 0) : u = v :=
  norm_sub_eq_zero_iff.1 h

@[simp]
theorem nnnorm_eq_zero {a : E} : ∥a∥₊ = 0 ↔ a = 0 := by
  rw [← Nnreal.coe_eq_zero, coe_nnnorm, norm_eq_zero]

theorem nnnorm_ne_zero_iff {g : E} : ∥g∥₊ ≠ 0 ↔ g ≠ 0 :=
  not_congr nnnorm_eq_zero

/-- An injective group homomorphism from an `add_comm_group` to a `normed_group` induces a
`normed_group` structure on the domain.

See note [reducible non-instances]. -/
@[reducible]
def NormedGroup.induced {E} [AddCommGroupₓ E] (f : E →+ F) (h : Function.Injective f) : NormedGroup E :=
  { SemiNormedGroup.induced f, MetricSpace.induced f h NormedGroup.toMetricSpace with }

/-- A subgroup of a normed group is also a normed group, with the restriction of the norm. -/
instance AddSubgroup.normedGroup (s : AddSubgroup E) : NormedGroup s :=
  NormedGroup.induced s.Subtype Subtype.coe_injective

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance Submodule.normedGroup {𝕜 : Type _} {_ : Ringₓ 𝕜} {E : Type _} [NormedGroup E] {_ : Module 𝕜 E}
    (s : Submodule 𝕜 E) : NormedGroup s :=
  { Submodule.semiNormedGroup s with }

instance ULift.normedGroup : NormedGroup (ULift E) :=
  { ULift.semiNormedGroup with }

/-- normed group instance on the product of two normed groups, using the sup norm. -/
noncomputable instance Prod.normedGroup : NormedGroup (E × F) :=
  { Prod.semiNormedGroup with }

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
noncomputable instance Pi.normedGroup {π : ι → Type _} [Fintype ι] [∀ i, NormedGroup (π i)] : NormedGroup (∀ i, π i) :=
  { Pi.semiNormedGroup with }

theorem tendsto_norm_sub_self_punctured_nhds (a : E) : Tendsto (fun x => ∥x - a∥) (𝓝[≠] a) (𝓝[>] 0) :=
  (tendsto_norm_sub_self a).inf <| tendsto_principal_principal.2 fun x hx => norm_pos_iff.2 <| sub_ne_zero.2 hx

theorem tendsto_norm_nhds_within_zero : Tendsto (norm : E → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf <| tendsto_principal_principal.2 fun x => norm_pos_iff.2

/-! Some relations with `has_compact_support` -/


theorem has_compact_support_norm_iff [TopologicalSpace α] {f : α → E} :
    (HasCompactSupport fun x => ∥f x∥) ↔ HasCompactSupport f :=
  has_compact_support_comp_left fun x => norm_eq_zero

alias has_compact_support_norm_iff ↔ _ HasCompactSupport.norm

theorem Continuous.bounded_above_of_compact_support [TopologicalSpace α] {f : α → E} (hf : Continuous f)
    (hsupp : HasCompactSupport f) : ∃ C, ∀ x, ∥f x∥ ≤ C := by
  simpa [← bdd_above_def] using hf.norm.bdd_above_range_of_has_compact_support hsupp.norm

end NormedGroup

