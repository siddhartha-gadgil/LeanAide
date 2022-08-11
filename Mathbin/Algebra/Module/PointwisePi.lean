/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathbin.Data.Set.Pointwise
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Pointwise actions on sets in Pi types

This file contains lemmas about pointwise actions on sets in Pi types.

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication, pi

-/


open Pointwise

open Set

variable {K ι : Type _} {R : ι → Type _}

@[to_additive]
theorem smul_pi_subset [∀ i, HasSmul K (R i)] (r : K) (s : Set ι) (t : ∀ i, Set (R i)) : r • Pi s t ⊆ Pi s (r • t) := by
  rintro x ⟨y, h, rfl⟩ i hi
  exact smul_mem_smul_set (h i hi)

@[to_additive]
theorem smul_univ_pi [∀ i, HasSmul K (R i)] (r : K) (t : ∀ i, Set (R i)) :
    r • Pi (Univ : Set ι) t = Pi (Univ : Set ι) (r • t) :=
  (Subset.antisymm (smul_pi_subset _ _ _)) fun x h => by
    refine' ⟨fun i => Classical.some (h i <| Set.mem_univ _), fun i hi => _, funext fun i => _⟩
    · exact (Classical.some_spec (h i _)).left
      
    · exact (Classical.some_spec (h i _)).right
      

@[to_additive]
theorem smul_pi [Groupₓ K] [∀ i, MulAction K (R i)] (r : K) (S : Set ι) (t : ∀ i, Set (R i)) :
    r • S.pi t = S.pi (r • t) :=
  (Subset.antisymm (smul_pi_subset _ _ _)) fun x h =>
    ⟨r⁻¹ • x, fun i hiS => mem_smul_set_iff_inv_smul_mem.mp (h i hiS), smul_inv_smul _ _⟩

theorem smul_pi₀ [GroupWithZeroₓ K] [∀ i, MulAction K (R i)] {r : K} (S : Set ι) (t : ∀ i, Set (R i)) (hr : r ≠ 0) :
    r • S.pi t = S.pi (r • t) :=
  smul_pi (Units.mk0 r hr) S t

