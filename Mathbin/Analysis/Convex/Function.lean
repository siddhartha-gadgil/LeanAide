/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, François Dupuis
-/
import Mathbin.Analysis.Convex.Basic
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.Ring

/-!
# Convex and concave functions

This file defines convex and concave functions in vector spaces and proves the finite Jensen
inequality. The integral version can be found in `analysis.convex.integral`.

A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
points `x y ∈ s`, the segment joining `(x, f x)` to `(y, f y)` is above the graph of `f`.
Equivalently, `convex_on 𝕜 f s` means that the epigraph `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is
a convex set.

## Main declarations

* `convex_on 𝕜 s f`: The function `f` is convex on `s` with scalars `𝕜`.
* `concave_on 𝕜 s f`: The function `f` is concave on `s` with scalars `𝕜`.
* `strict_convex_on 𝕜 s f`: The function `f` is strictly convex on `s` with scalars `𝕜`.
* `strict_concave_on 𝕜 s f`: The function `f` is strictly concave on `s` with scalars `𝕜`.
-/


open Finset LinearMap Set

open BigOperators Classical Convex Pointwise

variable {𝕜 E F β ι : Type _}

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β]

section HasSmul

variable (𝕜) [HasSmul 𝕜 E] [HasSmul 𝕜 β] (s : Set E) (f : E → β)

/-- Convexity of functions -/
def ConvexOn : Prop :=
  Convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def ConcaveOn : Prop :=
  Convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y)

/-- Strict convexity of functions -/
def StrictConvexOn : Prop :=
  Convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) < a • f x + b • f y

/-- Strict concavity of functions -/
def StrictConcaveOn : Prop :=
  Convex 𝕜 s ∧
    ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y < f (a • x + b • y)

variable {𝕜 s f}

open OrderDual (toDual ofDual)

theorem ConvexOn.dual (hf : ConvexOn 𝕜 s f) : ConcaveOn 𝕜 s (to_dual ∘ f) :=
  hf

theorem ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to_dual ∘ f) :=
  hf

theorem StrictConvexOn.dual (hf : StrictConvexOn 𝕜 s f) : StrictConcaveOn 𝕜 s (to_dual ∘ f) :=
  hf

theorem StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) : StrictConvexOn 𝕜 s (to_dual ∘ f) :=
  hf

theorem convex_on_id {s : Set β} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s id :=
  ⟨hs, by
    intros
    rfl⟩

theorem concave_on_id {s : Set β} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s id :=
  ⟨hs, by
    intros
    rfl⟩

theorem ConvexOn.subset {t : Set E} (hf : ConvexOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)⟩

theorem ConcaveOn.subset {t : Set E} (hf : ConcaveOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConvexOn.subset {t : Set E} (hf : StrictConvexOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    StrictConvexOn 𝕜 s f :=
  ⟨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)⟩

theorem StrictConcaveOn.subset {t : Set E} (hf : StrictConcaveOn 𝕜 t f) (hst : s ⊆ t) (hs : Convex 𝕜 s) :
    StrictConcaveOn 𝕜 s f :=
  ⟨hs, fun x y hx hy => hf.2 (hst hx) (hst hy)⟩

end HasSmul

section DistribMulAction

variable [HasSmul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.add (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x y hx hy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) ≤ a • f x + b • f y + (a • g x + b • g y) :=
        add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commₓ]
      ⟩

theorem ConcaveOn.add (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [HasSmul 𝕜 E] [Module 𝕜 β] {s : Set E} {f : E → β}

theorem convex_on_const (c : β) (hs : Convex 𝕜 s) : ConvexOn 𝕜 s fun x : E => c :=
  ⟨hs, fun x y _ _ a b _ _ hab => (Convex.combo_self hab c).Ge⟩

theorem concave_on_const (c : β) (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s fun x : E => c :=
  @convex_on_const _ _ βᵒᵈ _ _ _ _ _ _ c hs

theorem convex_on_of_convex_epigraph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 }) : ConvexOn 𝕜 s f :=
  ⟨fun x y hx hy a b ha hb hab => (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).1,
    fun x y hx hy a b ha hb hab => (@h (x, f x) (y, f y) ⟨hx, le_rfl⟩ ⟨hy, le_rfl⟩ a b ha hb hab).2⟩

theorem concave_on_of_convex_hypograph (h : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 }) : ConcaveOn 𝕜 s f :=
  @convex_on_of_convex_epigraph 𝕜 E βᵒᵈ _ _ _ _ _ _ _ h

end Module

section OrderedSmul

variable [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_le (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x ≤ r }) :=
  fun x y hx hy a b ha hb hab =>
  ⟨hf.1 hx.1 hy.1 ha hb hab,
    calc
      f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha hb hab
      _ ≤ a • r + b • r := add_le_add (smul_le_smul_of_nonneg hx.2 ha) (smul_le_smul_of_nonneg hy.2 hb)
      _ = r := Convex.combo_self hab r
      ⟩

theorem ConcaveOn.convex_ge (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r ≤ f x }) :=
  hf.dual.convex_le r

theorem ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := by
  rintro ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab
  refine' ⟨hf.1 hx hy ha hb hab, _⟩
  calc f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab _ ≤ a • r + b • t :=
      add_le_add (smul_le_smul_of_nonneg hr ha) (smul_le_smul_of_nonneg ht hb)

theorem ConcaveOn.convex_hypograph (hf : ConcaveOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  hf.dual.convex_epigraph

theorem convex_on_iff_convex_epigraph : ConvexOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } :=
  ⟨ConvexOn.convex_epigraph, convex_on_of_convex_epigraph⟩

theorem concave_on_iff_convex_hypograph : ConcaveOn 𝕜 s f ↔ Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 ≤ f p.1 } :=
  @convex_on_iff_convex_epigraph 𝕜 E βᵒᵈ _ _ _ _ _ _ _ f

end OrderedSmul

section Module

variable [Module 𝕜 E] [HasSmul 𝕜 β] {s : Set E} {f : E → β}

/-- Right translation preserves convexity. -/
theorem ConvexOn.translate_right (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x y hx hy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_commₓ, Convex.combo_self hab]
      _ ≤ a • f (c + x) + b • f (c + y) := hf.2 hx hy ha hb hab
      ⟩

/-- Right translation preserves concavity. -/
theorem ConcaveOn.translate_right (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves convexity. -/
theorem ConvexOn.translate_left (hf : ConvexOn 𝕜 s f) (c : E) :
    ConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [← add_commₓ] using hf.translate_right _

/-- Left translation preserves concavity. -/
theorem ConcaveOn.translate_left (hf : ConcaveOn 𝕜 s f) (c : E) :
    ConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) :=
  hf.dual.translate_left _

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 β]

theorem convex_on_iff_forall_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y :=
  by
  refine'
    and_congr_right' ⟨fun h x y hx hy a b ha hb hab => h hx hy ha.le hb.le hab, fun h x y hx hy a b ha hb hab => _⟩
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_addₓ] at hab
    subst b
    simp_rw [zero_smul, zero_addₓ, one_smul]
    
  obtain rfl | hb' := hb.eq_or_lt
  · rw [add_zeroₓ] at hab
    subst a
    simp_rw [zero_smul, add_zeroₓ, one_smul]
    
  exact h hx hy ha' hb' hab

theorem concave_on_iff_forall_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) :=
  @convex_on_iff_forall_pos 𝕜 E βᵒᵈ _ _ _ _ _ _ _

theorem convex_on_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y :=
  by
  rw [convex_on_iff_forall_pos]
  refine' and_congr_right' ⟨fun h x hx y hy _ a b ha hb hab => h hx hy ha hb hab, fun h x y hx hy a b ha hb hab => _⟩
  obtain rfl | hxy := eq_or_ne x y
  · rw [Convex.combo_self hab, Convex.combo_self hab]
    
  exact h hx hy hxy ha hb hab

theorem concave_on_iff_pairwise_pos {s : Set E} {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        s.Pairwise fun x y => ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y) :=
  @convex_on_iff_pairwise_pos 𝕜 E βᵒᵈ _ _ _ _ _ _ _

/-- A linear map is convex. -/
theorem LinearMap.convex_on (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConvexOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by
    rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- A linear map is concave. -/
theorem LinearMap.concave_on (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) : ConcaveOn 𝕜 s f :=
  ⟨hs, fun _ _ _ _ _ _ _ _ _ => by
    rw [f.map_add, f.map_smul, f.map_smul]⟩

theorem StrictConvexOn.convex_on {s : Set E} {f : E → β} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f :=
  convex_on_iff_pairwise_pos.mpr ⟨hf.1, fun x hx y hy hxy a b ha hb hab => (hf.2 hx hy hxy ha hb hab).le⟩

theorem StrictConcaveOn.concave_on {s : Set E} {f : E → β} (hf : StrictConcaveOn 𝕜 s f) : ConcaveOn 𝕜 s f :=
  hf.dual.ConvexOn

section OrderedSmul

variable [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem StrictConvexOn.convex_lt (hf : StrictConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_pairwise_pos.2 fun x hx y hy hxy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx.1 hy.1 hxy ha hb hab
        _ ≤ a • r + b • r := add_le_add (smul_lt_smul_of_pos hx.2 ha).le (smul_lt_smul_of_pos hy.2 hb).le
        _ = r := Convex.combo_self hab r
        ⟩

theorem StrictConcaveOn.convex_gt (hf : StrictConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end OrderedSmul

section LinearOrderₓ

variable [LinearOrderₓ E] {s : Set E} {f : E → β}

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is convex, it suffices to
verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y` and positive `a`,
`b`. The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order.
-/
theorem LinearOrderₓ.convex_on_of_lt (hs : Convex 𝕜 s)
    (hf :
      ∀ ⦃x y : E⦄,
        x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y) :
    ConvexOn 𝕜 s f := by
  refine' convex_on_iff_pairwise_pos.2 ⟨hs, fun x hx y hy hxy a b ha hb hab => _⟩
  wlog h : x ≤ y using x y a b, y x b a
  · exact le_totalₓ _ _
    
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is concave it suffices to
verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` for `x < y` and positive `a`, `b`. The
main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with lexicographic order. -/
theorem LinearOrderₓ.concave_on_of_lt (hs : Convex 𝕜 s)
    (hf :
      ∀ ⦃x y : E⦄,
        x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y ≤ f (a • x + b • y)) :
    ConcaveOn 𝕜 s f :=
  @LinearOrderₓ.convex_on_of_lt _ _ βᵒᵈ _ _ _ _ _ _ s f hs hf

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly convex, it suffices
to verify the inequality `f (a • x + b • y) < a • f x + b • f y` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
theorem LinearOrderₓ.strict_convex_on_of_lt (hs : Convex 𝕜 s)
    (hf :
      ∀ ⦃x y : E⦄,
        x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → f (a • x + b • y) < a • f x + b • f y) :
    StrictConvexOn 𝕜 s f := by
  refine' ⟨hs, fun x y hx hy hxy a b ha hb hab => _⟩
  wlog h : x ≤ y using x y a b, y x b a
  · exact le_totalₓ _ _
    
  exact hf hx hy (h.lt_of_ne hxy) ha hb hab

/-- For a function on a convex set in a linearly ordered space (where the order and the algebraic
structures aren't necessarily compatible), in order to prove that it is strictly concave it suffices
to verify the inequality `a • f x + b • f y < f (a • x + b • y)` for `x < y` and positive `a`, `b`.
The main use case is `E = 𝕜` however one can apply it, e.g., to `𝕜^n` with lexicographic order. -/
theorem LinearOrderₓ.strict_concave_on_of_lt (hs : Convex 𝕜 s)
    (hf :
      ∀ ⦃x y : E⦄,
        x ∈ s → y ∈ s → x < y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1 → a • f x + b • f y < f (a • x + b • y)) :
    StrictConcaveOn 𝕜 s f :=
  @LinearOrderₓ.strict_convex_on_of_lt _ _ βᵒᵈ _ _ _ _ _ _ _ _ hs hf

end LinearOrderₓ

end Module

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [HasSmul 𝕜 β]

/-- If `g` is convex on `s`, so is `(f ∘ g)` on `f ⁻¹' s` for a linear `f`. -/
theorem ConvexOn.comp_linear_map {f : F → β} {s : Set F} (hf : ConvexOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.linear_preimage _, fun x y hx hy a b ha hb hab =>
    calc
      f (g (a • x + b • y)) = f (a • g x + b • g y) := by
        rw [g.map_add, g.map_smul, g.map_smul]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab
      ⟩

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
theorem ConcaveOn.comp_linear_map {f : F → β} {s : Set F} (hf : ConcaveOn 𝕜 s f) (g : E →ₗ[𝕜] F) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_linear_map g

end Module

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid β]

section DistribMulAction

variable [HasSmul 𝕜 E] [DistribMulAction 𝕜 β] {s : Set E} {f g : E → β}

theorem StrictConvexOn.add_convex_on (hf : StrictConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add_of_lt_of_le (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy ha.le hb.le hab)
      _ = a • (f x + g x) + b • (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commₓ]
      ⟩

theorem ConvexOn.add_strict_convex_on (hf : ConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g) :=
  add_commₓ g f ▸ hg.add_convex_on hf

theorem StrictConvexOn.add (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f + g) :=
  ⟨hf.1, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (a • x + b • y) + g (a • x + b • y) < a • f x + b • f y + (a • g x + b • g y) :=
        add_lt_add (hf.2 hx hy hxy ha hb hab) (hg.2 hx hy hxy ha hb hab)
      _ = a • (f x + g x) + b • (f y + g y) := by
        rw [smul_add, smul_add, add_add_add_commₓ]
      ⟩

theorem StrictConcaveOn.add_concave_on (hf : StrictConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_convex_on hg.dual

theorem ConcaveOn.add_strict_concave_on (hf : ConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add_strict_convex_on hg.dual

theorem StrictConcaveOn.add (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f + g) :=
  hf.dual.add hg

end DistribMulAction

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.convex_lt (hf : ConvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) :=
  convex_iff_forall_pos.2 fun x y hx hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha.le hb.le hab,
      calc
        f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx.1 hy.1 ha.le hb.le hab
        _ < a • r + b • r := add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hx.2 ha) (smul_le_smul_of_nonneg hy.2.le hb.le)
        _ = r := Convex.combo_self hab _
        ⟩

theorem ConcaveOn.convex_gt (hf : ConcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

theorem ConvexOn.open_segment_subset_strict_epigraph (hf : ConvexOn 𝕜 s f) (p q : E × β) (hp : p.1 ∈ s ∧ f p.1 < p.2)
    (hq : q.1 ∈ s ∧ f q.1 ≤ q.2) : OpenSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } := by
  rintro _ ⟨a, b, ha, hb, hab, rfl⟩
  refine' ⟨hf.1 hp.1 hq.1 ha.le hb.le hab, _⟩
  calc f (a • p.1 + b • q.1) ≤ a • f p.1 + b • f q.1 := hf.2 hp.1 hq.1 ha.le hb.le hab _ < a • p.2 + b • q.2 :=
      add_lt_add_of_lt_of_le (smul_lt_smul_of_pos hp.2 ha) (smul_le_smul_of_nonneg hq.2 hb.le)

theorem ConcaveOn.open_segment_subset_strict_hypograph (hf : ConcaveOn 𝕜 s f) (p q : E × β) (hp : p.1 ∈ s ∧ p.2 < f p.1)
    (hq : q.1 ∈ s ∧ q.2 ≤ f q.1) : OpenSegment 𝕜 p q ⊆ { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.open_segment_subset_strict_epigraph p q hp hq

theorem ConvexOn.convex_strict_epigraph (hf : ConvexOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ f p.1 < p.2 } :=
  convex_iff_open_segment_subset.mpr fun p q hp hq => hf.open_segment_subset_strict_epigraph p q hp ⟨hq.1, hq.2.le⟩

theorem ConcaveOn.convex_strict_hypograph (hf : ConcaveOn 𝕜 s f) : Convex 𝕜 { p : E × β | p.1 ∈ s ∧ p.2 < f p.1 } :=
  hf.dual.convex_strict_epigraph

end Module

end OrderedCancelAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β] [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f g : E → β}

/-- The pointwise maximum of convex functions is convex. -/
theorem ConvexOn.sup (hf : ConvexOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConvexOn 𝕜 s (f⊔g) := by
  refine' ⟨hf.left, fun x y hx hy a b ha hb hab => sup_le _ _⟩
  · calc f (a • x + b • y) ≤ a • f x + b • f y := hf.right hx hy ha hb hab _ ≤ a • (f x⊔g x) + b • (f y⊔g y) :=
        add_le_add (smul_le_smul_of_nonneg le_sup_left ha) (smul_le_smul_of_nonneg le_sup_left hb)
    
  · calc g (a • x + b • y) ≤ a • g x + b • g y := hg.right hx hy ha hb hab _ ≤ a • (f x⊔g x) + b • (f y⊔g y) :=
        add_le_add (smul_le_smul_of_nonneg le_sup_right ha) (smul_le_smul_of_nonneg le_sup_right hb)
    

/-- The pointwise minimum of concave functions is concave. -/
theorem ConcaveOn.inf (hf : ConcaveOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConcaveOn 𝕜 s (f⊓g) :=
  hf.dual.sup hg

/-- The pointwise maximum of strictly convex functions is strictly convex. -/
theorem StrictConvexOn.sup (hf : StrictConvexOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConvexOn 𝕜 s (f⊔g) :=
  ⟨hf.left, fun x y hx hy hxy a b ha hb hab =>
    max_ltₓ
      (calc
        f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
        _ ≤ a • (f x⊔g x) + b • (f y⊔g y) :=
          add_le_add (smul_le_smul_of_nonneg le_sup_left ha.le) (smul_le_smul_of_nonneg le_sup_left hb.le)
        )
      (calc
        g (a • x + b • y) < a • g x + b • g y := hg.2 hx hy hxy ha hb hab
        _ ≤ a • (f x⊔g x) + b • (f y⊔g y) :=
          add_le_add (smul_le_smul_of_nonneg le_sup_right ha.le) (smul_le_smul_of_nonneg le_sup_right hb.le)
        )⟩

/-- The pointwise minimum of strictly concave functions is strictly concave. -/
theorem StrictConcaveOn.inf (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f⊓g) :=
  hf.dual.sup hg

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ max (f x) (f y) :=
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) :=
      add_le_add (smul_le_smul_of_nonneg (le_max_leftₓ _ _) ha) (smul_le_smul_of_nonneg (le_max_rightₓ _ _) hb)
    _ = max (f x) (f y) := Convex.combo_self hab _
    

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hab : a + b = 1) : min (f x) (f y) ≤ f (a • x + b • y) :=
  hf.dual.le_on_segment' hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
theorem ConvexOn.le_on_segment (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[𝕜] y]) :
    f z ≤ max (f x) (f y) :=
  let ⟨a, b, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
theorem ConcaveOn.ge_on_segment (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x -[𝕜] y]) :
    min (f x) (f y) ≤ f z :=
  hf.dual.le_on_segment hx hy hz

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_open_segment' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y)
    {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : f (a • x + b • y) < max (f x) (f y) :=
  calc
    f (a • x + b • y) < a • f x + b • f y := hf.2 hx hy hxy ha hb hab
    _ ≤ a • max (f x) (f y) + b • max (f x) (f y) :=
      add_le_add (smul_le_smul_of_nonneg (le_max_leftₓ _ _) ha.le) (smul_le_smul_of_nonneg (le_max_rightₓ _ _) hb.le)
    _ = max (f x) (f y) := Convex.combo_self hab _
    

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_open_segment' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) {a b : 𝕜} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : min (f x) (f y) < f (a • x + b • y) :=
  hf.dual.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly convex function on an open segment is strictly upper-bounded by the max of its
endpoints. -/
theorem StrictConvexOn.lt_on_open_segment (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hz : z ∈ OpenSegment 𝕜 x y) : f z < max (f x) (f y) :=
  let ⟨a, b, ha, hb, hab, hz⟩ := hz
  hz ▸ hf.lt_on_open_segment' hx hy hxy ha hb hab

/-- A strictly concave function on an open segment is strictly lower-bounded by the min of its
endpoints. -/
theorem StrictConcaveOn.lt_on_open_segment (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hz : z ∈ OpenSegment 𝕜 x y) : min (f x) (f y) < f z :=
  hf.dual.lt_on_open_segment hx hy hxy hz

end LinearOrderedAddCommMonoid

section LinearOrderedCancelAddCommMonoid

variable [LinearOrderedCancelAddCommMonoid β]

section OrderedSmul

variable [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f g : E → β}

theorem ConvexOn.le_left_of_right_le' (hf : ConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a)
    (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f y ≤ f (a • x + b • y)) : f (a • x + b • y) ≤ f x :=
  le_of_not_ltₓ fun h =>
    lt_irreflₓ (f (a • x + b • y)) <|
      calc
        f (a • x + b • y) ≤ a • f x + b • f y := hf.2 hx hy ha.le hb hab
        _ < a • f (a • x + b • y) + b • f (a • x + b • y) :=
          add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hfy hb)
        _ = f (a • x + b • y) := Convex.combo_self hab _
        

theorem ConcaveOn.left_le_of_le_right' (hf : ConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜} (ha : 0 < a)
    (hb : 0 ≤ b) (hab : a + b = 1) (hfy : f (a • x + b • y) ≤ f y) : f x ≤ f (a • x + b • y) :=
  hf.dual.le_left_of_right_le' hx hy ha hb hab hfy

theorem ConvexOn.le_right_of_left_le' (hf : ConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a)
    (hb : 0 < b) (hab : a + b = 1) (hfx : f x ≤ f (a • x + b • y)) : f (a • x + b • y) ≤ f y := by
  rw [add_commₓ] at hab hfx⊢
  exact hf.le_left_of_right_le' hy hx hb ha hab hfx

theorem ConcaveOn.right_le_of_le_left' (hf : ConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a)
    (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) ≤ f x) : f y ≤ f (a • x + b • y) :=
  hf.dual.le_right_of_left_le' hx hy ha hb hab hfx

theorem ConvexOn.le_left_of_right_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hyz : f y ≤ f z) : f z ≤ f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz

theorem ConcaveOn.left_le_of_le_right (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hyz : f z ≤ f y) : f x ≤ f z :=
  hf.dual.le_left_of_right_le hx hy hz hyz

theorem ConvexOn.le_right_of_left_le (hf : ConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hxz : f x ≤ f z) : f z ≤ f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz

theorem ConcaveOn.right_le_of_le_left (hf : ConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hxz : f z ≤ f x) : f y ≤ f z :=
  hf.dual.le_right_of_left_le hx hy hz hxz

end OrderedSmul

section Module

variable [Module 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f g : E → β}

/- The following lemmas don't require `module 𝕜 E` if you add the hypothesis `x ≠ y`. At the time of
the writing, we decided the resulting lemmas wouldn't be useful. Feel free to reintroduce them. -/
theorem StrictConvexOn.lt_left_of_right_lt' (hf : StrictConvexOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f y < f (a • x + b • y)) : f (a • x + b • y) < f x :=
  not_leₓ.1 fun h =>
    lt_irreflₓ (f (a • x + b • y)) <|
      calc
        f (a • x + b • y) < a • f x + b • f y :=
          hf.2 hx hy
            (by
              rintro rfl
              rw [Convex.combo_self hab] at hfy
              exact lt_irreflₓ _ hfy)
            ha hb hab
        _ < a • f (a • x + b • y) + b • f (a • x + b • y) :=
          add_lt_add_of_le_of_lt (smul_le_smul_of_nonneg h ha.le) (smul_lt_smul_of_pos hfy hb)
        _ = f (a • x + b • y) := Convex.combo_self hab _
        

theorem StrictConcaveOn.left_lt_of_lt_right' (hf : StrictConcaveOn 𝕜 s f) {x y : E} (hx : x ∈ s) (hy : y ∈ s) {a b : 𝕜}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfy : f (a • x + b • y) < f y) : f x < f (a • x + b • y) :=
  hf.dual.lt_left_of_right_lt' hx hy ha hb hab hfy

theorem StrictConvexOn.lt_right_of_left_lt' (hf : StrictConvexOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s) (hy : y ∈ s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f x < f (a • x + b • y)) : f (a • x + b • y) < f y := by
  rw [add_commₓ] at hab hfx⊢
  exact hf.lt_left_of_right_lt' hy hx hb ha hab hfx

theorem StrictConcaveOn.lt_right_of_left_lt' (hf : StrictConcaveOn 𝕜 s f) {x y : E} {a b : 𝕜} (hx : x ∈ s) (hy : y ∈ s)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hfx : f (a • x + b • y) < f x) : f y < f (a • x + b • y) :=
  hf.dual.lt_right_of_left_lt' hx hy ha hb hab hfx

theorem StrictConvexOn.lt_left_of_right_lt (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hyz : f y < f z) : f z < f x := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_left_of_right_lt' hx hy ha hb hab hyz

theorem StrictConcaveOn.left_lt_of_lt_right (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hyz : f z < f y) : f x < f z :=
  hf.dual.lt_left_of_right_lt hx hy hz hyz

theorem StrictConvexOn.lt_right_of_left_lt (hf : StrictConvexOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hxz : f x < f z) : f z < f y := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact hf.lt_right_of_left_lt' hx hy ha hb hab hxz

theorem StrictConcaveOn.lt_right_of_left_lt (hf : StrictConcaveOn 𝕜 s f) {x y z : E} (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ OpenSegment 𝕜 x y) (hxz : f z < f x) : f y < f z :=
  hf.dual.lt_right_of_left_lt hx hy hz hxz

end Module

end LinearOrderedCancelAddCommMonoid

section OrderedAddCommGroup

variable [OrderedAddCommGroup β] [HasSmul 𝕜 E] [Module 𝕜 β] {s : Set E} {f g : E → β}

/-- A function `-f` is convex iff `f` is concave. -/
@[simp]
theorem neg_convex_on_iff : ConvexOn 𝕜 s (-f) ↔ ConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine' ⟨hconv, fun x y hx hy a b ha hb hab => _⟩
    simp [← neg_apply, ← neg_le, ← add_commₓ] at h
    exact h hx hy ha hb hab
    
  · rintro ⟨hconv, h⟩
    refine' ⟨hconv, fun x y hx hy a b ha hb hab => _⟩
    rw [← neg_le_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_negₓ]
    exact h hx hy ha hb hab
    

/-- A function `-f` is concave iff `f` is convex. -/
@[simp]
theorem neg_concave_on_iff : ConcaveOn 𝕜 s (-f) ↔ ConvexOn 𝕜 s f := by
  rw [← neg_convex_on_iff, neg_negₓ f]

/-- A function `-f` is strictly convex iff `f` is strictly concave. -/
@[simp]
theorem neg_strict_convex_on_iff : StrictConvexOn 𝕜 s (-f) ↔ StrictConcaveOn 𝕜 s f := by
  constructor
  · rintro ⟨hconv, h⟩
    refine' ⟨hconv, fun x y hx hy hxy a b ha hb hab => _⟩
    simp [← neg_apply, ← neg_lt, ← add_commₓ] at h
    exact h hx hy hxy ha hb hab
    
  · rintro ⟨hconv, h⟩
    refine' ⟨hconv, fun x y hx hy hxy a b ha hb hab => _⟩
    rw [← neg_lt_neg_iff]
    simp_rw [neg_add, Pi.neg_apply, smul_neg, neg_negₓ]
    exact h hx hy hxy ha hb hab
    

/-- A function `-f` is strictly concave iff `f` is strictly convex. -/
@[simp]
theorem neg_strict_concave_on_iff : StrictConcaveOn 𝕜 s (-f) ↔ StrictConvexOn 𝕜 s f := by
  rw [← neg_strict_convex_on_iff, neg_negₓ f]

alias neg_convex_on_iff ↔ _ ConcaveOn.neg

alias neg_concave_on_iff ↔ _ ConvexOn.neg

alias neg_strict_convex_on_iff ↔ _ StrictConcaveOn.neg

alias neg_strict_concave_on_iff ↔ _ StrictConvexOn.neg

theorem ConvexOn.sub (hf : ConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : ConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem ConcaveOn.sub (hf : ConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) : ConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem StrictConvexOn.sub (hf : StrictConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) : StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem StrictConcaveOn.sub (hf : StrictConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) : StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add hg.neg

theorem ConvexOn.sub_strict_concave_on (hf : ConvexOn 𝕜 s f) (hg : StrictConcaveOn 𝕜 s g) :
    StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strict_convex_on hg.neg

theorem ConcaveOn.sub_strict_convex_on (hf : ConcaveOn 𝕜 s f) (hg : StrictConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_strict_concave_on hg.neg

theorem StrictConvexOn.sub_concave_on (hf : StrictConvexOn 𝕜 s f) (hg : ConcaveOn 𝕜 s g) : StrictConvexOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_convex_on hg.neg

theorem StrictConcaveOn.sub_convex_on (hf : StrictConcaveOn 𝕜 s f) (hg : ConvexOn 𝕜 s g) :
    StrictConcaveOn 𝕜 s (f - g) :=
  (sub_eq_add_neg f g).symm ▸ hf.add_concave_on hg.neg

end OrderedAddCommGroup

end AddCommMonoidₓ

section AddCancelCommMonoid

variable [AddCancelCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [HasSmul 𝕜 β] {s : Set E} {f : E → β}

/-- Right translation preserves strict convexity. -/
theorem StrictConvexOn.translate_right (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  ⟨hf.1.translate_preimage_right _, fun x y hx hy hxy a b ha hb hab =>
    calc
      f (c + (a • x + b • y)) = f (a • (c + x) + b • (c + y)) := by
        rw [smul_add, smul_add, add_add_add_commₓ, Convex.combo_self hab]
      _ < a • f (c + x) + b • f (c + y) := hf.2 hx hy ((add_right_injective c).Ne hxy) ha hb hab
      ⟩

/-- Right translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_right (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => c + z) :=
  hf.dual.translate_right _

/-- Left translation preserves strict convexity. -/
theorem StrictConvexOn.translate_left (hf : StrictConvexOn 𝕜 s f) (c : E) :
    StrictConvexOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [← add_commₓ] using hf.translate_right _

/-- Left translation preserves strict concavity. -/
theorem StrictConcaveOn.translate_left (hf : StrictConcaveOn 𝕜 s f) (c : E) :
    StrictConcaveOn 𝕜 ((fun z => c + z) ⁻¹' s) (f ∘ fun z => z + c) := by
  simpa only [← add_commₓ] using hf.translate_right _

end AddCancelCommMonoid

end OrderedSemiring

section OrderedCommSemiring

variable [OrderedCommSemiring 𝕜] [AddCommMonoidₓ E]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β]

section Module

variable [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConvexOn 𝕜 s f) : ConvexOn 𝕜 s fun x => c • f x :=
  ⟨hf.1, fun x y hx hy a b ha hb hab =>
    calc
      c • f (a • x + b • y) ≤ c • (a • f x + b • f y) := smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
      _ = a • c • f x + b • c • f y := by
        rw [smul_add, smul_comm c, smul_comm c] <;> infer_instance
      ⟩

theorem ConcaveOn.smul {c : 𝕜} (hc : 0 ≤ c) (hf : ConcaveOn 𝕜 s f) : ConcaveOn 𝕜 s fun x => c • f x :=
  hf.dual.smul hc

end Module

end OrderedAddCommMonoid

end OrderedCommSemiring

section OrderedRing

variable [LinearOrderedField 𝕜] [AddCommGroupₓ E] [AddCommGroupₓ F]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β]

section Module

variable [Module 𝕜 E] [Module 𝕜 F] [HasSmul 𝕜 β]

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
theorem ConvexOn.comp_affine_map {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConvexOn 𝕜 s f) :
    ConvexOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  ⟨hf.1.affine_preimage _, fun x y hx hy a b ha hb hab =>
    calc
      (f ∘ g) (a • x + b • y) = f (g (a • x + b • y)) := rfl
      _ = f (a • g x + b • g y) := by
        rw [Convex.combo_affine_apply hab]
      _ ≤ a • f (g x) + b • f (g y) := hf.2 hx hy ha hb hab
      ⟩

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
theorem ConcaveOn.comp_affine_map {f : F → β} (g : E →ᵃ[𝕜] F) {s : Set F} (hf : ConcaveOn 𝕜 s f) :
    ConcaveOn 𝕜 (g ⁻¹' s) (f ∘ g) :=
  hf.dual.comp_affine_map g

end Module

end OrderedAddCommMonoid

end OrderedRing

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommMonoidₓ E]

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β]

section HasSmul

variable [HasSmul 𝕜 E] [HasSmul 𝕜 β] {s : Set E}

theorem convex_on_iff_div {f : E → β} :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄,
          x ∈ s →
            y ∈ s →
              ∀ ⦃a b : 𝕜⦄,
                0 ≤ a →
                  0 ≤ b →
                    0 < a + b → f ((a / (a + b)) • x + (b / (a + b)) • y) ≤ (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl
    ⟨by
      intro h x y hx hy a b ha hb hab
      apply h hx hy (div_nonneg ha hab.le) (div_nonneg hb hab.le)
      rw [← add_div, div_self hab.ne'], by
      intro h x y hx hy a b ha hb hab
      simpa [← hab, ← zero_lt_one] using h hx hy ha hb⟩

theorem concave_on_iff_div {f : E → β} :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄,
          x ∈ s →
            y ∈ s →
              ∀ ⦃a b : 𝕜⦄,
                0 ≤ a →
                  0 ≤ b →
                    0 < a + b → (a / (a + b)) • f x + (b / (a + b)) • f y ≤ f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  @convex_on_iff_div _ _ βᵒᵈ _ _ _ _ _ _ _

theorem strict_convex_on_iff_div {f : E → β} :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄,
          x ∈ s →
            y ∈ s →
              x ≠ y →
                ∀ ⦃a b : 𝕜⦄,
                  0 < a →
                    0 < b → f ((a / (a + b)) • x + (b / (a + b)) • y) < (a / (a + b)) • f x + (b / (a + b)) • f y :=
  and_congr Iff.rfl
    ⟨by
      intro h x y hx hy hxy a b ha hb
      have hab := add_pos ha hb
      apply h hx hy hxy (div_pos ha hab) (div_pos hb hab)
      rw [← add_div, div_self hab.ne'], by
      intro h x y hx hy hxy a b ha hb hab
      simpa [← hab, ← zero_lt_one] using h hx hy hxy ha hb⟩

theorem strict_concave_on_iff_div {f : E → β} :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄,
          x ∈ s →
            y ∈ s →
              x ≠ y →
                ∀ ⦃a b : 𝕜⦄,
                  0 < a →
                    0 < b → (a / (a + b)) • f x + (b / (a + b)) • f y < f ((a / (a + b)) • x + (b / (a + b)) • y) :=
  @strict_convex_on_iff_div _ _ βᵒᵈ _ _ _ _ _ _ _

end HasSmul

end OrderedAddCommMonoid

end LinearOrderedField

section

variable [LinearOrderedField 𝕜] [LinearOrderedCancelAddCommMonoid β] [Module 𝕜 β] [OrderedSmul 𝕜 β] {x y z : 𝕜}
  {s : Set 𝕜} {f : 𝕜 → β}

theorem ConvexOn.le_right_of_left_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y ≤ z)
    (h : f x ≤ f y) : f y ≤ f z :=
  hyz.eq_or_lt.elim (fun hyz => (congr_arg f hyz).le) fun hyz =>
    hf.le_right_of_left_le hx hz (Ioo_subset_open_segment ⟨hxy, hyz⟩) h

theorem ConvexOn.le_left_of_right_le'' (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y) (hyz : y < z)
    (h : f z ≤ f y) : f y ≤ f x :=
  hxy.eq_or_lt.elim (fun hxy => (congr_arg f hxy).Ge) fun hxy =>
    hf.le_left_of_right_le hx hz (Ioo_subset_open_segment ⟨hxy, hyz⟩) h

theorem ConcaveOn.right_le_of_le_left'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y ≤ z)
    (h : f y ≤ f x) : f z ≤ f y :=
  hf.dual.le_right_of_left_le'' hx hz hxy hyz h

theorem ConcaveOn.left_le_of_le_right'' (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y) (hyz : y < z)
    (h : f y ≤ f z) : f x ≤ f y :=
  hf.dual.le_left_of_right_le'' hx hz hxy hyz h

end

