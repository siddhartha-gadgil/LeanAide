/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `int.floor`, `int.ceil`, `int.fract`, `nat.floor`, and `nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/


open Set

section FloorRing

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedRing R] [FloorRing R] [TopologicalSpace R] [OrderTopology R]
  [MeasurableSpace R]

theorem Int.measurable_floor [OpensMeasurableSpace R] : Measurable (Int.floor : R → ℤ) :=
  measurable_to_encodable fun x => by
    simpa only [← Int.preimage_floor_singleton] using measurable_set_Ico

@[measurability]
theorem Measurable.floor [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => ⌊f x⌋ :=
  Int.measurable_floor.comp hf

theorem Int.measurable_ceil [OpensMeasurableSpace R] : Measurable (Int.ceil : R → ℤ) :=
  measurable_to_encodable fun x => by
    simpa only [← Int.preimage_ceil_singleton] using measurable_set_Ioc

@[measurability]
theorem Measurable.ceil [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => ⌈f x⌉ :=
  Int.measurable_ceil.comp hf

theorem measurable_fract [BorelSpace R] : Measurable (Int.fract : R → R) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.Union fun z => measurable_id.sub_const _ (hs.inter measurable_set_Ico)

@[measurability]
theorem Measurable.fract [BorelSpace R] {f : α → R} (hf : Measurable f) : Measurable fun x => Int.fract (f x) :=
  measurable_fract.comp hf

theorem MeasurableSet.image_fract [BorelSpace R] {s : Set R} (hs : MeasurableSet s) : MeasurableSet (Int.fract '' s) :=
  by
  simp only [← Int.image_fract, ← sub_eq_add_neg, ← image_add_right']
  exact MeasurableSet.Union fun m => (measurable_add_const _ hs).inter measurable_set_Ico

end FloorRing

section FloorSemiring

variable {α R : Type _} [MeasurableSpace α] [LinearOrderedSemiring R] [FloorSemiring R] [TopologicalSpace R]
  [OrderTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] {f : α → R}

theorem Nat.measurable_floor : Measurable (Nat.floor : R → ℕ) :=
  measurable_to_encodable fun n => by
    cases eq_or_ne ⌊n⌋₊ 0 <;> simp [*, ← Nat.preimage_floor_of_ne_zero]

@[measurability]
theorem Measurable.nat_floor (hf : Measurable f) : Measurable fun x => ⌊f x⌋₊ :=
  Nat.measurable_floor.comp hf

theorem Nat.measurable_ceil : Measurable (Nat.ceil : R → ℕ) :=
  measurable_to_encodable fun n => by
    cases eq_or_ne ⌈n⌉₊ 0 <;> simp [*, ← Nat.preimage_ceil_of_ne_zero]

@[measurability]
theorem Measurable.nat_ceil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊ :=
  Nat.measurable_ceil.comp hf

end FloorSemiring

