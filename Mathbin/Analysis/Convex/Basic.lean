/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov, Yaël Dillies
-/
import Mathbin.Algebra.Order.Invertible
import Mathbin.Algebra.Order.Module
import Mathbin.LinearAlgebra.AffineSpace.Midpoint
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace
import Mathbin.LinearAlgebra.Ray

/-!
# Convex sets and functions in vector spaces

In a 𝕜-vector space, we define the following objects and properties.
* `segment 𝕜 x y`: Closed segment joining `x` and `y`.
* `open_segment 𝕜 x y`: Open segment joining `x` and `y`.
* `convex 𝕜 s`: A set `s` is convex if for any two points `x y ∈ s` it includes `segment 𝕜 x y`.
* `std_simplex 𝕜 ι`: The standard simplex in `ι → 𝕜` (currently requires `fintype ι`). It is the
  intersection of the positive quadrant with the hyperplane `s.sum = 1`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex.

## Notations

We provide the following notation:
* `[x -[𝕜] y] = segment 𝕜 x y` in locale `convex`

## TODO

Generalize all this file to affine spaces.

Should we rename `segment` and `open_segment` to `convex.Icc` and `convex.Ioo`? Should we also
define `clopen_segment`/`convex.Ico`/`convex.Ioc`?
-/


variable {𝕜 E F β : Type _}

open LinearMap Set

open BigOperators Classical Pointwise

/-! ### Segment -/


section OrderedSemiring

variable [OrderedSemiring 𝕜] [AddCommMonoidₓ E]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E]

/-- Segments in a vector space. -/
def Segment (x y : E) : Set E :=
  { z : E | ∃ (a b : 𝕜)(ha : 0 ≤ a)(hb : 0 ≤ b)(hab : a + b = 1), a • x + b • y = z }

/-- Open segment in a vector space. Note that `open_segment 𝕜 x x = {x}` instead of being `∅` when
the base semiring has some element between `0` and `1`. -/
def OpenSegment (x y : E) : Set E :=
  { z : E | ∃ (a b : 𝕜)(ha : 0 < a)(hb : 0 < b)(hab : a + b = 1), a • x + b • y = z }

-- mathport name: «expr[ -[ ] ]»
localized [Convex] notation "[" x " -[" 𝕜 "] " y "]" => Segment 𝕜 x y

theorem segment_eq_image₂ (x y : E) :
    [x -[𝕜] y] = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [← Segment, ← image, ← Prod.exists, ← mem_set_of_eq, ← exists_prop, ← and_assoc]

theorem open_segment_eq_image₂ (x y : E) :
    OpenSegment 𝕜 x y = (fun p : 𝕜 × 𝕜 => p.1 • x + p.2 • y) '' { p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1 } := by
  simp only [← OpenSegment, ← image, ← Prod.exists, ← mem_set_of_eq, ← exists_prop, ← and_assoc]

theorem segment_symm (x y : E) : [x -[𝕜] y] = [y -[𝕜] x] :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩⟩

theorem open_segment_symm (x y : E) : OpenSegment 𝕜 x y = OpenSegment 𝕜 y x :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩,
      fun ⟨a, b, ha, hb, hab, H⟩ => ⟨b, a, hb, ha, (add_commₓ _ _).trans hab, (add_commₓ _ _).trans H⟩⟩

theorem open_segment_subset_segment (x y : E) : OpenSegment 𝕜 x y ⊆ [x -[𝕜] y] := fun z ⟨a, b, ha, hb, hab, hz⟩ =>
  ⟨a, b, ha.le, hb.le, hab, hz⟩

theorem segment_subset_iff {x y : E} {s : Set E} :
    [x -[𝕜] y] ⊆ s ↔ ∀ a b : 𝕜, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H z ⟨a, b, ha, hb, hab, hz⟩ => hz ▸ H a b ha hb hab⟩

theorem open_segment_subset_iff {x y : E} {s : Set E} :
    OpenSegment 𝕜 x y ⊆ s ↔ ∀ a b : 𝕜, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  ⟨fun H a b ha hb hab => H ⟨a, b, ha, hb, hab, rfl⟩, fun H z ⟨a, b, ha, hb, hab, hz⟩ => hz ▸ H a b ha hb hab⟩

end HasSmul

open Convex

section MulActionWithZero

variable (𝕜) [MulActionWithZero 𝕜 E]

theorem left_mem_segment (x y : E) : x ∈ [x -[𝕜] y] :=
  ⟨1, 0, zero_le_one, le_reflₓ 0, add_zeroₓ 1, by
    rw [zero_smul, one_smul, add_zeroₓ]⟩

theorem right_mem_segment (x y : E) : y ∈ [x -[𝕜] y] :=
  segment_symm 𝕜 y x ▸ left_mem_segment 𝕜 y x

end MulActionWithZero

section Module

variable (𝕜) [Module 𝕜 E] {x y z : E} {s : Set E}

@[simp]
theorem segment_same (x : E) : [x -[𝕜] x] = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ => by
      simpa only [← (add_smul _ _ _).symm, ← mem_singleton_iff, ← hab, ← one_smul, ← eq_comm] using hz, fun h =>
      mem_singleton_iff.1 h ▸ left_mem_segment 𝕜 z z⟩

theorem insert_endpoints_open_segment (x y : E) : insert x (insert y (OpenSegment 𝕜 x y)) = [x -[𝕜] y] := by
  simp only [← subset_antisymm_iff, ← insert_subset, ← left_mem_segment, ← right_mem_segment, ←
    open_segment_subset_segment, ← true_andₓ]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  refine' hb.eq_or_gt.imp _ fun hb' => ha.eq_or_gt.imp _ _
  · rintro rfl
    rw [add_zeroₓ] at hab
    rw [hab, one_smul, zero_smul, add_zeroₓ]
    
  · rintro rfl
    rw [zero_addₓ] at hab
    rw [hab, one_smul, zero_smul, zero_addₓ]
    
  · exact fun ha' => ⟨a, b, ha', hb', hab, rfl⟩
    

variable {𝕜}

theorem mem_open_segment_of_ne_left_right (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x -[𝕜] y]) : z ∈ OpenSegment 𝕜 x y := by
  rw [← insert_endpoints_open_segment] at hz
  exact (hz.resolve_left hx.symm).resolve_left hy.symm

theorem open_segment_subset_iff_segment_subset (hx : x ∈ s) (hy : y ∈ s) : OpenSegment 𝕜 x y ⊆ s ↔ [x -[𝕜] y] ⊆ s := by
  simp only [insert_endpoints_open_segment, ← insert_subset, *, ← true_andₓ]

end Module

end OrderedSemiring

open Convex

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroupₓ

variable (𝕜) [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

section DenselyOrdered

variable [Nontrivial 𝕜] [DenselyOrdered 𝕜]

@[simp]
theorem open_segment_same (x : E) : OpenSegment 𝕜 x x = {x} :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ => by
      simpa only [add_smul, ← mem_singleton_iff, ← hab, ← one_smul, ← eq_comm] using hz, fun h : z = x => by
      obtain ⟨a, ha₀, ha₁⟩ := DenselyOrdered.dense (0 : 𝕜) 1 zero_lt_one
      refine' ⟨a, 1 - a, ha₀, sub_pos_of_lt ha₁, add_sub_cancel'_right _ _, _⟩
      rw [← add_smul, add_sub_cancel'_right, one_smul, h]⟩

end DenselyOrdered

theorem segment_eq_image (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Icc (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩,
        hab ▸
          hz ▸ by
            simp only [← add_sub_cancel]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

theorem open_segment_eq_image (x y : E) : OpenSegment 𝕜 x y = (fun θ : 𝕜 => (1 - θ) • x + θ • y) '' Ioo (0 : 𝕜) 1 :=
  Set.ext fun z =>
    ⟨fun ⟨a, b, ha, hb, hab, hz⟩ =>
      ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩,
        hab ▸
          hz ▸ by
            simp only [← add_sub_cancel]⟩,
      fun ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩ => ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

theorem segment_eq_image' (x y : E) : [x -[𝕜] y] = (fun θ : 𝕜 => x + θ • (y - x)) '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  ext θ
  simp only [← smul_sub, ← sub_smul, ← one_smul]
  abel

theorem open_segment_eq_image' (x y : E) : OpenSegment 𝕜 x y = (fun θ : 𝕜 => x + θ • (y - x)) '' Ioo (0 : 𝕜) 1 := by
  convert open_segment_eq_image 𝕜 x y
  ext θ
  simp only [← smul_sub, ← sub_smul, ← one_smul]
  abel

theorem segment_eq_image_line_map (x y : E) : [x -[𝕜] y] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1 := by
  convert segment_eq_image 𝕜 x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem open_segment_eq_image_line_map (x y : E) : OpenSegment 𝕜 x y = AffineMap.lineMap x y '' Ioo (0 : 𝕜) 1 := by
  convert open_segment_eq_image 𝕜 x y
  ext
  exact AffineMap.line_map_apply_module _ _ _

theorem segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' [a -[𝕜] b] = [f a -[𝕜] f b] :=
  Set.ext fun x => by
    simp_rw [segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

@[simp]
theorem open_segment_image (f : E →ₗ[𝕜] F) (a b : E) : f '' OpenSegment 𝕜 a b = OpenSegment 𝕜 (f a) (f b) :=
  Set.ext fun x => by
    simp_rw [open_segment_eq_image, mem_image, exists_exists_and_eq_and, map_add, map_smul]

theorem mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b -[𝕜] a + c] ↔ x ∈ [b -[𝕜] c] := by
  rw [segment_eq_image', segment_eq_image']
  refine' exists_congr fun θ => and_congr Iff.rfl _
  simp only [← add_sub_add_left_eq_sub, ← add_assocₓ, ← add_right_injₓ]

@[simp]
theorem mem_open_segment_translate (a : E) {x b c : E} :
    a + x ∈ OpenSegment 𝕜 (a + b) (a + c) ↔ x ∈ OpenSegment 𝕜 b c := by
  rw [open_segment_eq_image', open_segment_eq_image']
  refine' exists_congr fun θ => and_congr Iff.rfl _
  simp only [← add_sub_add_left_eq_sub, ← add_assocₓ, ← add_right_injₓ]

theorem segment_translate_preimage (a b c : E) : (fun x => a + x) ⁻¹' [a + b -[𝕜] a + c] = [b -[𝕜] c] :=
  Set.ext fun x => mem_segment_translate 𝕜 a

theorem open_segment_translate_preimage (a b c : E) :
    (fun x => a + x) ⁻¹' OpenSegment 𝕜 (a + b) (a + c) = OpenSegment 𝕜 b c :=
  Set.ext fun x => mem_open_segment_translate 𝕜 a

theorem segment_translate_image (a b c : E) : (fun x => a + x) '' [b -[𝕜] c] = [a + b -[𝕜] a + c] :=
  segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a

theorem open_segment_translate_image (a b c : E) :
    (fun x => a + x) '' OpenSegment 𝕜 b c = OpenSegment 𝕜 (a + b) (a + c) :=
  open_segment_translate_preimage 𝕜 a b c ▸ image_preimage_eq _ <| add_left_surjective a

end AddCommGroupₓ

end OrderedRing

theorem same_ray_of_mem_segment [OrderedCommRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {x y z : E} (h : x ∈ [y -[𝕜] z]) :
    SameRay 𝕜 (x - y) (z - x) := by
  rw [segment_eq_image'] at h
  rcases h with ⟨θ, ⟨hθ₀, hθ₁⟩, rfl⟩
  simpa only [← add_sub_cancel', sub_sub, ← sub_smul, ← one_smul] using
    (same_ray_nonneg_smul_left (z - y) hθ₀).nonneg_smul_right (sub_nonneg.2 hθ₁)

section LinearOrderedRing

variable [LinearOrderedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

theorem midpoint_mem_segment [Invertible (2 : 𝕜)] (x y : E) : midpoint 𝕜 x y ∈ [x -[𝕜] y] := by
  rw [segment_eq_image_line_map]
  exact ⟨⅟ 2, ⟨inv_of_nonneg.mpr zero_le_two, inv_of_le_one one_le_two⟩, rfl⟩

theorem mem_segment_sub_add [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x - y -[𝕜] x + y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _
  rw [midpoint_sub_add]

theorem mem_segment_add_sub [Invertible (2 : 𝕜)] (x y : E) : x ∈ [x + y -[𝕜] x - y] := by
  convert @midpoint_mem_segment 𝕜 _ _ _ _ _ _ _
  rw [midpoint_add_sub]

@[simp]
theorem left_mem_open_segment_iff [DenselyOrdered 𝕜] [NoZeroSmulDivisors 𝕜 E] {x y : E} :
    x ∈ OpenSegment 𝕜 x y ↔ x = y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, hx⟩
    refine' smul_right_injective _ hb.ne' ((add_right_injₓ (a • x)).1 _)
    rw [hx, ← add_smul, hab, one_smul]
    
  · rintro rfl
    rw [open_segment_same]
    exact mem_singleton _
    

@[simp]
theorem right_mem_open_segment_iff [DenselyOrdered 𝕜] [NoZeroSmulDivisors 𝕜 E] {x y : E} :
    y ∈ OpenSegment 𝕜 x y ↔ x = y := by
  rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

end AddCommGroupₓ

end LinearOrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {x y z : E}

theorem mem_segment_iff_same_ray : x ∈ [y -[𝕜] z] ↔ SameRay 𝕜 (x - y) (z - x) := by
  refine' ⟨same_ray_of_mem_segment, fun h => _⟩
  rcases h.exists_eq_smul_add with ⟨a, b, ha, hb, hab, hxy, hzx⟩
  rw [add_commₓ, sub_add_sub_cancel] at hxy hzx
  rw [← mem_segment_translate _ (-x), neg_add_selfₓ]
  refine' ⟨b, a, hb, ha, add_commₓ a b ▸ hab, _⟩
  rw [← sub_eq_neg_add, ← neg_sub, hxy, ← sub_eq_neg_add, hzx, smul_neg, smul_comm, neg_add_selfₓ]

theorem mem_segment_iff_div :
    x ∈ [y -[𝕜] z] ↔ ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ 0 < a + b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    simp [*]
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine' ⟨a / (a + b), b / (a + b), div_nonneg ha hab.le, div_nonneg hb hab.le, _, rfl⟩
    rw [← add_div, div_self hab.ne']
    

theorem mem_open_segment_iff_div :
    x ∈ OpenSegment 𝕜 y z ↔ ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ (a / (a + b)) • y + (b / (a + b)) • z = x := by
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    use a, b, ha, hb
    rw [hab, div_one, div_one]
    
  · rintro ⟨a, b, ha, hb, rfl⟩
    have hab : 0 < a + b := add_pos ha hb
    refine' ⟨a / (a + b), b / (a + b), div_pos ha hab, div_pos hb hab, _, rfl⟩
    rw [← add_div, div_self hab.ne']
    

end AddCommGroupₓ

end LinearOrderedField

/-!
#### Segments in an ordered space
Relates `segment`, `open_segment` and `set.Icc`, `set.Ico`, `set.Ioc`, `set.Ioo`
-/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]

theorem segment_subset_Icc {x y : E} (h : x ≤ y) : [x -[𝕜] y] ⊆ Icc x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  calc x = a • x + b • x := (Convex.combo_self hab _).symm _ ≤ a • x + b • y :=
      add_le_add_left (smul_le_smul_of_nonneg h hb) _
  calc a • x + b • y ≤ a • y + b • y := add_le_add_right (smul_le_smul_of_nonneg h ha) _ _ = y :=
      Convex.combo_self hab _

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]

theorem open_segment_subset_Ioo {x y : E} (h : x < y) : OpenSegment 𝕜 x y ⊆ Ioo x y := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  constructor
  calc x = a • x + b • x := (Convex.combo_self hab _).symm _ < a • x + b • y :=
      add_lt_add_left (smul_lt_smul_of_pos h hb) _
  calc a • x + b • y < a • y + b • y := add_lt_add_right (smul_lt_smul_of_pos h ha) _ _ = y := Convex.combo_self hab _

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E] {𝕜}

theorem segment_subset_interval (x y : E) : [x -[𝕜] y] ⊆ Interval x y := by
  cases le_totalₓ x y
  · rw [interval_of_le h]
    exact segment_subset_Icc h
    
  · rw [interval_of_ge h, segment_symm]
    exact segment_subset_Icc h
    

theorem Convex.min_le_combo (x y : E) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : min x y ≤ a • x + b • y :=
  (segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).1

theorem Convex.combo_le_max (x y : E) {a b : 𝕜} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • x + b • y ≤ max x y :=
  (segment_subset_interval x y ⟨_, _, ha, hb, hab, rfl⟩).2

end LinearOrderedAddCommMonoid

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜]

theorem Icc_subset_segment {x y : 𝕜} : Icc x y ⊆ [x -[𝕜] y] := by
  rintro z ⟨hxz, hyz⟩
  obtain rfl | h := (hxz.trans hyz).eq_or_lt
  · rw [segment_same]
    exact hyz.antisymm hxz
    
  rw [← sub_nonneg] at hxz hyz
  rw [← sub_pos] at h
  refine' ⟨(y - z) / (y - x), (z - x) / (y - x), div_nonneg hyz h.le, div_nonneg hxz h.le, _, _⟩
  · rw [← add_div, sub_add_sub_cancel, div_self h.ne']
    
  · rw [smul_eq_mul, smul_eq_mul, ← mul_div_right_comm, ← mul_div_right_comm, ← add_div, div_eq_iff h.ne', add_commₓ,
      sub_mul, sub_mul, mul_comm x, sub_add_sub_cancel, mul_sub]
    

@[simp]
theorem segment_eq_Icc {x y : 𝕜} (h : x ≤ y) : [x -[𝕜] y] = Icc x y :=
  (segment_subset_Icc h).antisymm Icc_subset_segment

theorem Ioo_subset_open_segment {x y : 𝕜} : Ioo x y ⊆ OpenSegment 𝕜 x y := fun z hz =>
  mem_open_segment_of_ne_left_right hz.1.Ne hz.2.ne' (Icc_subset_segment <| Ioo_subset_Icc_self hz)

@[simp]
theorem open_segment_eq_Ioo {x y : 𝕜} (h : x < y) : OpenSegment 𝕜 x y = Ioo x y :=
  (open_segment_subset_Ioo h).antisymm Ioo_subset_open_segment

theorem segment_eq_Icc' (x y : 𝕜) : [x -[𝕜] y] = Icc (min x y) (max x y) := by
  cases le_totalₓ x y
  · rw [segment_eq_Icc h, max_eq_rightₓ h, min_eq_leftₓ h]
    
  · rw [segment_symm, segment_eq_Icc h, max_eq_leftₓ h, min_eq_rightₓ h]
    

theorem open_segment_eq_Ioo' {x y : 𝕜} (hxy : x ≠ y) : OpenSegment 𝕜 x y = Ioo (min x y) (max x y) := by
  cases hxy.lt_or_lt
  · rw [open_segment_eq_Ioo h, max_eq_rightₓ h.le, min_eq_leftₓ h.le]
    
  · rw [open_segment_symm, open_segment_eq_Ioo h, max_eq_leftₓ h.le, min_eq_rightₓ h.le]
    

theorem segment_eq_interval (x y : 𝕜) : [x -[𝕜] y] = Interval x y :=
  segment_eq_Icc' _ _

/-- A point is in an `Icc` iff it can be expressed as a convex combination of the endpoints. -/
theorem Convex.mem_Icc {x y : 𝕜} (h : x ≤ y) {z : 𝕜} :
    z ∈ Icc x y ↔ ∃ a b : 𝕜, 0 ≤ a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← segment_eq_Icc h]
  simp_rw [← exists_prop]
  rfl

/-- A point is in an `Ioo` iff it can be expressed as a strict convex combination of the endpoints.
-/
theorem Convex.mem_Ioo {x y : 𝕜} (h : x < y) {z : 𝕜} :
    z ∈ Ioo x y ↔ ∃ a b : 𝕜, 0 < a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  rw [← open_segment_eq_Ioo h]
  simp_rw [← exists_prop]
  rfl

/-- A point is in an `Ioc` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ioc {x y : 𝕜} (h : x < y) {z : 𝕜} :
    z ∈ Ioc x y ↔ ∃ a b : 𝕜, 0 ≤ a ∧ 0 < b ∧ a + b = 1 ∧ a * x + b * y = z := by
  constructor
  · rintro hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ioc_subset_Icc_self hz)
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zeroₓ] at hab
      rw [hab, one_mulₓ, zero_mul, add_zeroₓ] at hz
      exact (hz.1.Ne rfl).elim
      
    · exact ⟨a, b, ha, hb', hab, rfl⟩
      
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_addₓ] at hab
      rwa [hab, one_mulₓ, zero_mul, zero_addₓ, right_mem_Ioc]
      
    · exact Ioo_subset_Ioc_self ((Convex.mem_Ioo h).2 ⟨a, b, ha', hb, hab, rfl⟩)
      
    

/-- A point is in an `Ico` iff it can be expressed as a semistrict convex combination of the
endpoints. -/
theorem Convex.mem_Ico {x y : 𝕜} (h : x < y) {z : 𝕜} :
    z ∈ Ico x y ↔ ∃ a b : 𝕜, 0 < a ∧ 0 ≤ b ∧ a + b = 1 ∧ a * x + b * y = z := by
  constructor
  · rintro hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := (Convex.mem_Icc h.le).1 (Ico_subset_Icc_self hz)
    obtain rfl | ha' := ha.eq_or_lt
    · rw [zero_addₓ] at hab
      rw [hab, one_mulₓ, zero_mul, zero_addₓ] at hz
      exact (hz.2.Ne rfl).elim
      
    · exact ⟨a, b, ha', hb, hab, rfl⟩
      
    
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    obtain rfl | hb' := hb.eq_or_lt
    · rw [add_zeroₓ] at hab
      rwa [hab, one_mulₓ, zero_mul, add_zeroₓ, left_mem_Ico]
      
    · exact Ioo_subset_Ico_self ((Convex.mem_Ioo h).2 ⟨a, b, ha, hb', hab, rfl⟩)
      
    

end LinearOrderedField

/-! ### Convexity of sets -/


section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] [HasSmul 𝕜 F] (s : Set E)

/-- Convexity of sets. -/
def Convex : Prop :=
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • x + b • y ∈ s

variable {𝕜 s}

theorem convex_iff_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → [x -[𝕜] y] ⊆ s :=
  forall₄_congrₓ fun x y hx hy => (segment_subset_iff _).symm

theorem Convex.segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : [x -[𝕜] y] ⊆ s :=
  convex_iff_segment_subset.1 h hx hy

theorem Convex.open_segment_subset (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : OpenSegment 𝕜 x y ⊆ s :=
  (open_segment_subset_segment 𝕜 x y).trans (h.segment_subset hx hy)

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
theorem convex_iff_pointwise_add_subset : Convex 𝕜 s ↔ ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
  Iff.intro
    (by
      rintro hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩
      exact hA hu hv ha hb hab)
    fun h x y hx hy a b ha hb hab => (h ha hb hab) (Set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩)

alias convex_iff_pointwise_add_subset ↔ Convex.set_combo_subset _

theorem convex_empty : Convex 𝕜 (∅ : Set E) := fun x y => False.elim

theorem convex_univ : Convex 𝕜 (Set.Univ : Set E) := fun _ _ _ _ _ _ _ _ _ => trivialₓ

theorem Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ∩ t) :=
  fun x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) =>
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

theorem convex_sInter {S : Set (Set E)} (h : ∀, ∀ s ∈ S, ∀, Convex 𝕜 s) : Convex 𝕜 (⋂₀ S) :=
  fun x y hx hy a b ha hb hab s hs => h s hs (hx s hs) (hy s hs) ha hb hab

theorem convex_Inter {ι : Sort _} {s : ι → Set E} (h : ∀ i, Convex 𝕜 (s i)) : Convex 𝕜 (⋂ i, s i) :=
  sInter_range s ▸ convex_sInter <| forall_range_iff.2 h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem convex_Inter₂ {ι : Sort _} {κ : ι → Sort _} {s : ∀ i, κ i → Set E} (h : ∀ i j, Convex 𝕜 (s i j)) :
    Convex 𝕜 (⋂ (i) (j), s i j) :=
  convex_Inter fun i => convex_Inter <| h i

theorem Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t) := by
  intro x y hx hy a b ha hb hab
  apply mem_prod.2
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab, ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩

theorem convex_pi {ι : Type _} {E : ι → Type _} [∀ i, AddCommMonoidₓ (E i)] [∀ i, HasSmul 𝕜 (E i)] {s : Set ι}
    {t : ∀ i, Set (E i)} (ht : ∀ i, Convex 𝕜 (t i)) : Convex 𝕜 (s.pi t) := fun x y hx hy a b ha hb hab i hi =>
  ht i (hx i hi) (hy i hi) ha hb hab

theorem Directed.convex_Union {ι : Sort _} {s : ι → Set E} (hdir : Directed (· ⊆ ·) s)
    (hc : ∀ ⦃i : ι⦄, Convex 𝕜 (s i)) : Convex 𝕜 (⋃ i, s i) := by
  rintro x y hx hy a b ha hb hab
  rw [mem_Union] at hx hy⊢
  obtain ⟨i, hx⟩ := hx
  obtain ⟨j, hy⟩ := hy
  obtain ⟨k, hik, hjk⟩ := hdir i j
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩

theorem DirectedOn.convex_sUnion {c : Set (Set E)} (hdir : DirectedOn (· ⊆ ·) c)
    (hc : ∀ ⦃A : Set E⦄, A ∈ c → Convex 𝕜 A) : Convex 𝕜 (⋃₀c) := by
  rw [sUnion_eq_Union]
  exact (directed_on_iff_directed.1 hdir).convex_Union fun A => hc A.2

end HasSmul

section Module

variable [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

theorem convex_iff_open_segment_subset : Convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → OpenSegment 𝕜 x y ⊆ s :=
  convex_iff_segment_subset.trans <| forall₄_congrₓ fun x y hx hy => (open_segment_subset_iff_segment_subset hx hy).symm

theorem convex_iff_forall_pos :
    Convex 𝕜 s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
  convex_iff_open_segment_subset.trans <| forall₄_congrₓ fun x y hx hy => open_segment_subset_iff 𝕜

theorem convex_iff_pairwise_pos :
    Convex 𝕜 s ↔ s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s := by
  refine' convex_iff_forall_pos.trans ⟨fun h x hx y hy _ => h hx hy, _⟩
  intro h x y hx hy a b ha hb hab
  obtain rfl | hxy := eq_or_ne x y
  · rwa [Convex.combo_self hab]
    
  · exact h hx hy hxy ha hb hab
    

protected theorem Set.Subsingleton.convex {s : Set E} (h : s.Subsingleton) : Convex 𝕜 s :=
  convex_iff_pairwise_pos.mpr (h.Pairwise _)

theorem convex_singleton (c : E) : Convex 𝕜 ({c} : Set E) :=
  subsingleton_singleton.Convex

theorem convex_segment (x y : E) : Convex 𝕜 [x -[𝕜] y] := by
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ a b ha hb hab
  refine'
    ⟨a * ap + b * aq, a * bp + b * bq, add_nonneg (mul_nonneg ha hap) (mul_nonneg hb haq),
      add_nonneg (mul_nonneg ha hbp) (mul_nonneg hb hbq), _, _⟩
  · rw [add_add_add_commₓ, ← mul_addₓ, ← mul_addₓ, habp, habq, mul_oneₓ, mul_oneₓ, hab]
    
  · simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commₓ _ _ _ _
    

theorem convex_open_segment (a b : E) : Convex 𝕜 (OpenSegment 𝕜 a b) := by
  rw [convex_iff_open_segment_subset]
  rintro p q ⟨ap, bp, hap, hbp, habp, rfl⟩ ⟨aq, bq, haq, hbq, habq, rfl⟩ z ⟨a, b, ha, hb, hab, rfl⟩
  refine'
    ⟨a * ap + b * aq, a * bp + b * bq, add_pos (mul_pos ha hap) (mul_pos hb haq),
      add_pos (mul_pos ha hbp) (mul_pos hb hbq), _, _⟩
  · rw [add_add_add_commₓ, ← mul_addₓ, ← mul_addₓ, habp, habq, mul_oneₓ, mul_oneₓ, hab]
    
  · simp_rw [add_smul, mul_smul, smul_add]
    exact add_add_add_commₓ _ _ _ _
    

theorem Convex.linear_image (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f '' s) := by
  intro x y hx hy a b ha hb hab
  obtain ⟨x', hx', rfl⟩ := mem_image_iff_bex.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_image_iff_bex.1 hy
  exact
    ⟨a • x' + b • y', hs hx' hy' ha hb hab, by
      rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem Convex.is_linear_image (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f '' s) :=
  hs.linear_image <| hf.mk' f

theorem Convex.linear_preimage {s : Set F} (hs : Convex 𝕜 s) (f : E →ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s) := by
  intro x y hx hy a b ha hb hab
  rw [mem_preimage, f.map_add, f.map_smul, f.map_smul]
  exact hs hx hy ha hb hab

theorem Convex.is_linear_preimage {s : Set F} (hs : Convex 𝕜 s) {f : E → F} (hf : IsLinearMap 𝕜 f) :
    Convex 𝕜 (f ⁻¹' s) :=
  hs.linear_preimage <| hf.mk' f

theorem Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s + t) := by
  rw [← add_image_prod]
  exact (hs.prod ht).is_linear_image IsLinearMap.is_linear_map_add

theorem Convex.vadd (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 (z +ᵥ s) := by
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  exact (convex_singleton _).add hs

theorem Convex.translate (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) '' s) :=
  hs.vadd _

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_right (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => z + x) ⁻¹' s) := by
  intro x y hx hy a b ha hb hab
  have h := hs hx hy ha hb hab
  rwa [smul_add, smul_add, add_add_add_commₓ, ← add_smul, hab, one_smul] at h

/-- The translation of a convex set is also convex. -/
theorem Convex.translate_preimage_left (hs : Convex 𝕜 s) (z : E) : Convex 𝕜 ((fun x => x + z) ⁻¹' s) := by
  simpa only [← add_commₓ] using hs.translate_preimage_right z

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_Iic (r : β) : Convex 𝕜 (Iic r) := fun x y hx hy a b ha hb hab =>
  calc
    a • x + b • y ≤ a • r + b • r := add_le_add (smul_le_smul_of_nonneg hx ha) (smul_le_smul_of_nonneg hy hb)
    _ = r := Convex.combo_self hab _
    

theorem convex_Ici (r : β) : Convex 𝕜 (Ici r) :=
  @convex_Iic 𝕜 βᵒᵈ _ _ _ _ r

theorem convex_Icc (r s : β) : Convex 𝕜 (Icc r s) :=
  Ici_inter_Iic.subst ((convex_Ici r).inter <| convex_Iic s)

theorem convex_halfspace_le {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w ≤ r } :=
  (convex_Iic r).is_linear_preimage h

theorem convex_halfspace_ge {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r ≤ f w } :=
  (convex_Ici r).is_linear_preimage h

theorem convex_hyperplane {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w = r } := by
  simp_rw [le_antisymm_iffₓ]
  exact (convex_halfspace_le h r).inter (convex_halfspace_ge h r)

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_Iio (r : β) : Convex 𝕜 (Iio r) := by
  intro x y hx hy a b ha hb hab
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_addₓ] at hab
    rwa [zero_smul, zero_addₓ, hab, one_smul]
    
  rw [mem_Iio] at hx hy
  calc a • x + b • y < a • r + b • r :=
      add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx ha') (smul_le_smul_of_nonneg hy.le hb)_ = r :=
      Convex.combo_self hab _

theorem convex_Ioi (r : β) : Convex 𝕜 (Ioi r) :=
  @convex_Iio 𝕜 βᵒᵈ _ _ _ _ r

theorem convex_Ioo (r s : β) : Convex 𝕜 (Ioo r s) :=
  Ioi_inter_Iio.subst ((convex_Ioi r).inter <| convex_Iio s)

theorem convex_Ico (r s : β) : Convex 𝕜 (Ico r s) :=
  Ici_inter_Iio.subst ((convex_Ici r).inter <| convex_Iio s)

theorem convex_Ioc (r s : β) : Convex 𝕜 (Ioc r s) :=
  Ioi_inter_Iic.subst ((convex_Ioi r).inter <| convex_Iic s)

theorem convex_halfspace_lt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | f w < r } :=
  (convex_Iio r).is_linear_preimage h

theorem convex_halfspace_gt {f : E → β} (h : IsLinearMap 𝕜 f) (r : β) : Convex 𝕜 { w | r < f w } :=
  (convex_Ioi r).is_linear_preimage h

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β]

theorem convex_interval (r s : β) : Convex 𝕜 (Interval r s) :=
  convex_Icc _ _

end LinearOrderedAddCommMonoid

end Module

end AddCommMonoidₓ

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [OrderedSmul 𝕜 E] {s : Set E} {f : E → β}

theorem MonotoneOn.convex_le (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x y hx hy a b ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans
      (max_rec' _ hx.2 hy.2)⟩

theorem MonotoneOn.convex_lt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  fun x y hx hy a b ha hb hab =>
  ⟨hs hx.1 hy.1 ha hb hab,
    (hf (hs hx.1 hy.1 ha hb hab) (max_rec' s hx.1 hy.1) (Convex.combo_le_max x y ha hb hab)).trans_lt
      (max_rec' _ hx.2 hy.2)⟩

theorem MonotoneOn.convex_ge (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

theorem MonotoneOn.convex_gt (hf : MonotoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 Eᵒᵈ βᵒᵈ _ _ _ _ _ _ _ hf.dual hs r

theorem AntitoneOn.convex_le (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  @MonotoneOn.convex_ge 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_lt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  @MonotoneOn.convex_gt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_ge (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  @MonotoneOn.convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem AntitoneOn.convex_gt (hf : AntitoneOn f s) (hs : Convex 𝕜 s) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  @MonotoneOn.convex_lt 𝕜 E βᵒᵈ _ _ _ _ _ _ _ hf hs r

theorem Monotone.convex_le (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_lt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Monotone.convex_ge (hf : Monotone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_ge convex_univ r)

theorem Monotone.convex_gt (hf : Monotone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.MonotoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_le (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x ≤ r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_le convex_univ r)

theorem Antitone.convex_lt (hf : Antitone f) (r : β) : Convex 𝕜 { x | f x < r } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_lt convex_univ r)

theorem Antitone.convex_ge (hf : Antitone f) (r : β) : Convex 𝕜 { x | r ≤ f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_ge convex_univ r)

theorem Antitone.convex_gt (hf : Antitone f) (r : β) : Convex 𝕜 { x | r < f x } :=
  Set.sep_univ.subst ((hf.AntitoneOn Univ).convex_gt convex_univ r)

end LinearOrderedAddCommMonoid

section AddCommGroupₓ

variable [AddCommGroupₓ E] [Module 𝕜 E] {s t : Set E}

theorem Convex.combo_eq_vadd {a b : 𝕜} {x y : E} (h : a + b = 1) : a • x + b • y = b • (y - x) + x :=
  calc
    a • x + b • y = b • y - b • x + (a • x + b • x) := by
      abel
    _ = b • (y - x) + x := by
      rw [smul_sub, Convex.combo_self h]
    

end AddCommGroupₓ

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

theorem Convex.smul (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 (c • s) :=
  hs.linear_image (LinearMap.lsmul _ _ c)

theorem Convex.smul_preimage (hs : Convex 𝕜 s) (c : 𝕜) : Convex 𝕜 ((fun z => c • z) ⁻¹' s) :=
  hs.linear_preimage (LinearMap.lsmul _ _ c)

theorem Convex.affinity (hs : Convex 𝕜 s) (z : E) (c : 𝕜) : Convex 𝕜 ((fun x => z + c • x) '' s) := by
  simpa only [image_smul, image_vadd, ← image_image] using (hs.smul c).vadd z

end AddCommMonoidₓ

end OrderedCommSemiring

section OrderedRing

variable [OrderedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s t : Set E}

theorem Convex.add_smul_mem (hs : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    x + t • y ∈ s := by
  have h : x + t • y = (1 - t) • x + t • (x + y) := by
    rw [smul_add, ← add_assocₓ, ← add_smul, sub_add_cancel, one_smul]
  rw [h]
  exact hs hx hy (sub_nonneg_of_le ht.2) ht.1 (sub_add_cancel _ _)

theorem Convex.smul_mem_of_zero_mem (hs : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) {t : 𝕜}
    (ht : t ∈ Icc (0 : 𝕜) 1) : t • x ∈ s := by
  simpa using
    hs.add_smul_mem zero_mem
      (by
        simpa using hx)
      ht

theorem Convex.add_smul_sub_mem (h : Convex 𝕜 s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {t : 𝕜} (ht : t ∈ Icc (0 : 𝕜) 1) :
    x + t • (y - x) ∈ s := by
  apply h.segment_subset hx hy
  rw [segment_eq_image']
  exact mem_image_of_mem _ ht

/-- Affine subspaces are convex. -/
theorem AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : Convex 𝕜 (Q : Set E) := by
  intro x y hx hy a b ha hb hab
  rw [eq_sub_of_add_eq hab, ← AffineMap.line_map_apply_module]
  exact AffineMap.line_map_mem b hx hy

/-- Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
theorem Convex.combo_affine_apply {a b : 𝕜} {x y : E} {f : E →ᵃ[𝕜] F} (h : a + b = 1) :
    f (a • x + b • y) = a • f x + b • f y := by
  simp only [← Convex.combo_eq_vadd h, vsub_eq_sub]
  exact f.apply_line_map _ _ _

/-- The preimage of a convex set under an affine map is convex. -/
theorem Convex.affine_preimage (f : E →ᵃ[𝕜] F) {s : Set F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s) := by
  intro x y xs ys a b ha hb hab
  rw [mem_preimage, Convex.combo_affine_apply hab]
  exact hs xs ys ha hb hab

/-- The image of a convex set under an affine map is convex. -/
theorem Convex.affine_image (f : E →ᵃ[𝕜] F) (hs : Convex 𝕜 s) : Convex 𝕜 (f '' s) := by
  rintro x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab
  refine' ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩
  rw [Convex.combo_affine_apply hab, hx'f, hy'f]

theorem Convex.neg (hs : Convex 𝕜 s) : Convex 𝕜 (-s) :=
  hs.is_linear_preimage IsLinearMap.is_linear_map_neg

theorem Convex.sub (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) : Convex 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end AddCommGroupₓ

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F] {s : Set E}

/-- Alternative definition of set convexity, using division. -/
theorem convex_iff_div :
    Convex 𝕜 s ↔
      ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → 0 < a + b → (a / (a + b)) • x + (b / (a + b)) • y ∈ s :=
  by
  simp only [← convex_iff_segment_subset, ← subset_def, ← mem_segment_iff_div]
  refine' forall₄_congrₓ fun x y hx hy => ⟨fun H a b ha hb hab => H _ ⟨a, b, ha, hb, hab, rfl⟩, _⟩
  rintro H _ ⟨a, b, ha, hb, hab, rfl⟩
  exact H ha hb hab

theorem Convex.mem_smul_of_zero_mem (h : Convex 𝕜 s) {x : E} (zero_mem : (0 : E) ∈ s) (hx : x ∈ s) {t : 𝕜}
    (ht : 1 ≤ t) : x ∈ t • s := by
  rw [mem_smul_set_iff_inv_smul_mem₀ (zero_lt_one.trans_le ht).ne']
  exact h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩

theorem Convex.add_smul (h_conv : Convex 𝕜 s) {p q : 𝕜} (hp : 0 ≤ p) (hq : 0 ≤ q) : (p + q) • s = p • s + q • s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp_rw [smul_set_empty, add_empty]
    
  obtain rfl | hp' := hp.eq_or_lt
  · rw [zero_addₓ, zero_smul_set hs, zero_addₓ]
    
  obtain rfl | hq' := hq.eq_or_lt
  · rw [add_zeroₓ, zero_smul_set hs, add_zeroₓ]
    
  ext
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨p • v, q • v, smul_mem_smul_set hv, smul_mem_smul_set hv, (add_smul _ _ _).symm⟩
    
  · rintro ⟨v₁, v₂, ⟨v₁₁, h₁₂, rfl⟩, ⟨v₂₁, h₂₂, rfl⟩, rfl⟩
    have hpq := add_pos hp' hq'
    exact
      mem_smul_set.2
        ⟨_,
          h_conv h₁₂ h₂₂ (div_pos hp' hpq).le (div_pos hq' hpq).le
            (by
              rw [← div_self hpq.ne', add_div] : p / (p + q) + q / (p + q) = 1),
          by
          simp only [mul_smul, ← smul_add, ← mul_div_cancel' _ hpq.ne']⟩
    

end AddCommGroupₓ

end LinearOrderedField

/-!
#### Convex sets in an ordered space
Relates `convex` and `ord_connected`.
-/


section

theorem Set.OrdConnected.convex_of_chain [OrderedSemiring 𝕜] [OrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]
    {s : Set E} (hs : s.OrdConnected) (h : IsChain (· ≤ ·) s) : Convex 𝕜 s := by
  refine' convex_iff_segment_subset.mpr fun x y hx hy => _
  obtain hxy | hyx := h.total hx hy
  · exact (segment_subset_Icc hxy).trans (hs.out hx hy)
    
  · rw [segment_symm]
    exact (segment_subset_Icc hyx).trans (hs.out hy hx)
    

theorem Set.OrdConnected.convex [OrderedSemiring 𝕜] [LinearOrderedAddCommMonoid E] [Module 𝕜 E] [OrderedSmul 𝕜 E]
    {s : Set E} (hs : s.OrdConnected) : Convex 𝕜 s :=
  hs.convex_of_chain <| is_chain_of_trichotomous s

theorem convex_iff_ord_connected [LinearOrderedField 𝕜] {s : Set 𝕜} : Convex 𝕜 s ↔ s.OrdConnected := by
  simp_rw [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset]
  exact forall_congrₓ fun x => forall_swap

alias convex_iff_ord_connected ↔ Convex.ord_connected _

end

/-! #### Convexity of submodules/subspaces -/


section Submodule

open Submodule

theorem Submodule.convex [OrderedSemiring 𝕜] [AddCommMonoidₓ E] [Module 𝕜 E] (K : Submodule 𝕜 E) :
    Convex 𝕜 (↑K : Set E) := by
  repeat'
    intro
  refine' add_mem (smul_mem _ _ _) (smul_mem _ _ _) <;> assumption

theorem Subspace.convex [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (K : Subspace 𝕜 E) :
    Convex 𝕜 (↑K : Set E) :=
  K.Convex

end Submodule

/-! ### Simplex -/


section Simplex

variable (𝕜) (ι : Type _) [OrderedSemiring 𝕜] [Fintype ι]

/-- The standard simplex in the space of functions `ι → 𝕜` is the set of vectors with non-negative
coordinates with total sum `1`. This is the free object in the category of convex spaces. -/
def StdSimplex : Set (ι → 𝕜) :=
  { f | (∀ x, 0 ≤ f x) ∧ (∑ x, f x) = 1 }

theorem std_simplex_eq_inter : StdSimplex 𝕜 ι = (⋂ x, { f | 0 ≤ f x }) ∩ { f | (∑ x, f x) = 1 } := by
  ext f
  simp only [← StdSimplex, ← Set.mem_inter_eq, ← Set.mem_Inter, ← Set.mem_set_of_eq]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:63:9: parse error
theorem convex_std_simplex : Convex 𝕜 (StdSimplex 𝕜 ι) := by
  refine' fun f g hf hg a b ha hb hab => ⟨fun x => _, _⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
    
  · erw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul, smul_eq_mul, mul_oneₓ,
      mul_oneₓ]
    exact hab
    

variable {ι}

theorem ite_eq_mem_std_simplex (i : ι) : (fun j => ite (i = j) (1 : 𝕜) 0) ∈ StdSimplex 𝕜 ι :=
  ⟨fun j => by
    simp only <;> split_ifs <;> norm_num, by
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]⟩

end Simplex

