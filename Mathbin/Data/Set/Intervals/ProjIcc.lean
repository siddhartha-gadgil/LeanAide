/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot
-/
import Mathbin.Data.Set.Intervals.Basic

/-!
# Projection of a line onto a closed interval

Given a linearly ordered type `α`, in this file we define

* `set.proj_Icc (a b : α) (h : a ≤ b)` to be the map `α → [a, b]` sending `(-∞, a]` to `a`, `[b, ∞)`
  to `b`, and each point `x ∈ [a, b]` to itself;
* `set.Icc_extend {a b : α} (h : a ≤ b) (f : Icc a b → β)` to be the extension of `f` to `α` defined
  as `f ∘ proj_Icc a b h`.

We also prove some trivial properties of these maps.
-/


variable {α β : Type _} [LinearOrderₓ α]

open Function

namespace Set

/-- Projection of `α` to the closed interval `[a, b]`. -/
def projIcc (a b : α) (h : a ≤ b) (x : α) : Icc a b :=
  ⟨max a (min b x), le_max_leftₓ _ _, max_leₓ h (min_le_leftₓ _ _)⟩

variable {a b : α} (h : a ≤ b) {x : α}

theorem proj_Icc_of_le_left (hx : x ≤ a) : projIcc a b h x = ⟨a, left_mem_Icc.2 h⟩ := by
  simp [← proj_Icc, ← hx, ← hx.trans h]

@[simp]
theorem proj_Icc_left : projIcc a b h a = ⟨a, left_mem_Icc.2 h⟩ :=
  proj_Icc_of_le_left h le_rfl

theorem proj_Icc_of_right_le (hx : b ≤ x) : projIcc a b h x = ⟨b, right_mem_Icc.2 h⟩ := by
  simp [← proj_Icc, ← hx, ← h]

@[simp]
theorem proj_Icc_right : projIcc a b h b = ⟨b, right_mem_Icc.2 h⟩ :=
  proj_Icc_of_right_le h le_rfl

theorem proj_Icc_eq_left (h : a < b) : projIcc a b h.le x = ⟨a, left_mem_Icc.mpr h.le⟩ ↔ x ≤ a := by
  refine' ⟨fun h' => _, proj_Icc_of_le_left _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc, max_eq_left_iff, min_le_iff, h.not_le, false_orₓ] at h'
  exact h'

theorem proj_Icc_eq_right (h : a < b) : projIcc a b h.le x = ⟨b, right_mem_Icc.mpr h.le⟩ ↔ b ≤ x := by
  refine' ⟨fun h' => _, proj_Icc_of_right_le _⟩
  simp_rw [Subtype.ext_iff_val, proj_Icc] at h'
  have :=
    ((max_choice _ _).resolve_left
            (by
              simp [← h.ne', ← h'])).symm.trans
      h'
  exact min_eq_left_iff.mp this

theorem proj_Icc_of_mem (hx : x ∈ Icc a b) : projIcc a b h x = ⟨x, hx⟩ := by
  simp [← proj_Icc, ← hx.1, ← hx.2]

@[simp]
theorem proj_Icc_coe (x : Icc a b) : projIcc a b h x = x := by
  cases x
  apply proj_Icc_of_mem

theorem proj_Icc_surj_on : SurjOn (projIcc a b h) (Icc a b) Univ := fun x _ => ⟨x, x.2, proj_Icc_coe h x⟩

theorem proj_Icc_surjective : Surjective (projIcc a b h) := fun x => ⟨x, proj_Icc_coe h x⟩

@[simp]
theorem range_proj_Icc : Range (projIcc a b h) = univ :=
  (proj_Icc_surjective h).range_eq

theorem monotone_proj_Icc : Monotone (projIcc a b h) := fun x y hxy => max_le_max le_rfl <| min_le_min le_rfl hxy

theorem strict_mono_on_proj_Icc : StrictMonoOn (projIcc a b h) (Icc a b) := fun x hx y hy hxy => by
  simpa only [← proj_Icc_of_mem, ← hx, ← hy]

/-- Extend a function `[a, b] → β` to a map `α → β`. -/
def iccExtend {a b : α} (h : a ≤ b) (f : Icc a b → β) : α → β :=
  f ∘ projIcc a b h

@[simp]
theorem Icc_extend_range (f : Icc a b → β) : Range (iccExtend h f) = Range f := by
  simp only [← Icc_extend, ← range_comp f, ← range_proj_Icc, ← range_id']

theorem Icc_extend_of_le_left (f : Icc a b → β) (hx : x ≤ a) : iccExtend h f x = f ⟨a, left_mem_Icc.2 h⟩ :=
  congr_arg f <| proj_Icc_of_le_left h hx

@[simp]
theorem Icc_extend_left (f : Icc a b → β) : iccExtend h f a = f ⟨a, left_mem_Icc.2 h⟩ :=
  Icc_extend_of_le_left h f le_rfl

theorem Icc_extend_of_right_le (f : Icc a b → β) (hx : b ≤ x) : iccExtend h f x = f ⟨b, right_mem_Icc.2 h⟩ :=
  congr_arg f <| proj_Icc_of_right_le h hx

@[simp]
theorem Icc_extend_right (f : Icc a b → β) : iccExtend h f b = f ⟨b, right_mem_Icc.2 h⟩ :=
  Icc_extend_of_right_le h f le_rfl

theorem Icc_extend_of_mem (f : Icc a b → β) (hx : x ∈ Icc a b) : iccExtend h f x = f ⟨x, hx⟩ :=
  congr_arg f <| proj_Icc_of_mem h hx

@[simp]
theorem Icc_extend_coe (f : Icc a b → β) (x : Icc a b) : iccExtend h f x = f x :=
  congr_arg f <| proj_Icc_coe h x

end Set

open Set

variable [Preorderₓ β] {a b : α} (h : a ≤ b) {f : Icc a b → β}

theorem Monotone.Icc_extend (hf : Monotone f) : Monotone (iccExtend h f) :=
  hf.comp <| monotone_proj_Icc h

theorem StrictMono.strict_mono_on_Icc_extend (hf : StrictMono f) : StrictMonoOn (iccExtend h f) (Icc a b) :=
  hf.comp_strict_mono_on (strict_mono_on_proj_Icc h)

