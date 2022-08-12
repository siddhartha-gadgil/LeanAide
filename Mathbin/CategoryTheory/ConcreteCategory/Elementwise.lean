/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w kernel.lift_ι cokernel.π_desc kernel.condition cokernel.condition

