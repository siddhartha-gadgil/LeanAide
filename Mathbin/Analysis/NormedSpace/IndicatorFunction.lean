/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.IndicatorFunction

/-!
# Indicator function and norm

This file contains a few simple lemmas about `set.indicator` and `norm`.

## Tags
indicator, norm
-/


variable {α E : Type _} [SemiNormedGroup E] {s t : Set α} (f : α → E) (a : α)

open Set

theorem norm_indicator_eq_indicator_norm : ∥indicatorₓ s f a∥ = indicatorₓ s (fun a => ∥f a∥) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm

theorem nnnorm_indicator_eq_indicator_nnnorm : ∥indicatorₓ s f a∥₊ = indicatorₓ s (fun a => ∥f a∥₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) : ∥indicatorₓ s f a∥ ≤ ∥indicatorₓ t f a∥ := by
  simp only [← norm_indicator_eq_indicator_norm]
  exact indicator_le_indicator_of_subset ‹_› (fun _ => norm_nonneg _) _

theorem indicator_norm_le_norm_self : indicatorₓ s (fun a => ∥f a∥) a ≤ ∥f a∥ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a

theorem norm_indicator_le_norm_self : ∥indicatorₓ s f a∥ ≤ ∥f a∥ := by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

