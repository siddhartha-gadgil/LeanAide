/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/


open Filter Set

open TopologicalSpace

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class NormedLinearOrderedGroup (α : Type _) extends LinearOrderedAddCommGroup α, HasNorm α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)

instance (priority := 100) NormedLinearOrderedGroup.toNormedGroup (α : Type _) [NormedLinearOrderedGroup α] :
    NormedGroup α :=
  ⟨NormedLinearOrderedGroup.dist_eq⟩

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class NormedLinearOrderedField (α : Type _) extends LinearOrderedField α, HasNorm α, MetricSpace α where
  dist_eq : ∀ x y, dist x y = norm (x - y)
  norm_mul' : ∀ a b, norm (a * b) = norm a * norm b

instance (priority := 100) NormedLinearOrderedField.toNormedField (α : Type _) [NormedLinearOrderedField α] :
    NormedField α where
  dist_eq := NormedLinearOrderedField.dist_eq
  norm_mul' := NormedLinearOrderedField.norm_mul'

instance (priority := 100) NormedLinearOrderedField.toNormedLinearOrderedGroup (α : Type _)
    [NormedLinearOrderedField α] : NormedLinearOrderedGroup α :=
  ⟨NormedLinearOrderedField.dist_eq⟩

noncomputable instance : NormedLinearOrderedField ℚ :=
  ⟨dist_eq_norm, norm_mul⟩

noncomputable instance : NormedLinearOrderedField ℝ :=
  ⟨dist_eq_norm, norm_mul⟩

