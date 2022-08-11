/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Analysis.Convex.Function

/-!
# Quasiconvex and quasiconcave functions

This file defines quasiconvexity, quasiconcavity and quasilinearity of functions, which are
generalizations of unimodality and monotonicity. Convexity implies quasiconvexity, concavity implies
quasiconcavity, and monotonicity implies quasilinearity.

## Main declarations

* `quasiconvex_on 𝕜 s f`: Quasiconvexity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex.
* `quasiconcave_on 𝕜 s f`: Quasiconcavity of the function `f` on the set `s` with scalars `𝕜`. This
  means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex.
* `quasilinear_on 𝕜 s f`: Quasilinearity of the function `f` on the set `s` with scalars `𝕜`. This
  means that `f` is both quasiconvex and quasiconcave.

## TODO

Prove that a quasilinear function between two linear orders is either monotone or antitone. This is
not hard but quite a pain to go about as there are many cases to consider.

## References

* https://en.wikipedia.org/wiki/Quasiconvex_function
-/


open Function OrderDual Set

variable {𝕜 E F β : Type _}

section OrderedSemiring

variable [OrderedSemiring 𝕜]

section AddCommMonoidₓ

variable [AddCommMonoidₓ E] [AddCommMonoidₓ F]

section OrderedAddCommMonoid

variable (𝕜) [OrderedAddCommMonoid β] [HasSmul 𝕜 E] (s : Set E) (f : E → β)

/-- A function is quasiconvex if all its sublevels are convex.
This means that, for all `r`, `{x ∈ s | f x ≤ r}` is `𝕜`-convex. -/
def QuasiconvexOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | f x ≤ r })

/-- A function is quasiconcave if all its superlevels are convex.
This means that, for all `r`, `{x ∈ s | r ≤ f x}` is `𝕜`-convex. -/
def QuasiconcaveOn : Prop :=
  ∀ r, Convex 𝕜 ({ x ∈ s | r ≤ f x })

/-- A function is quasilinear if it is both quasiconvex and quasiconcave.
This means that, for all `r`,
the sets `{x ∈ s | f x ≤ r}` and `{x ∈ s | r ≤ f x}` are `𝕜`-convex. -/
def QuasilinearOn : Prop :=
  QuasiconvexOn 𝕜 s f ∧ QuasiconcaveOn 𝕜 s f

variable {𝕜 s f}

theorem QuasiconvexOn.dual : QuasiconvexOn 𝕜 s f → QuasiconcaveOn 𝕜 s (to_dual ∘ f) :=
  id

theorem QuasiconcaveOn.dual : QuasiconcaveOn 𝕜 s f → QuasiconvexOn 𝕜 s (to_dual ∘ f) :=
  id

theorem QuasilinearOn.dual : QuasilinearOn 𝕜 s f → QuasilinearOn 𝕜 s (to_dual ∘ f) :=
  And.swap

theorem Convex.quasiconvex_on_of_convex_le (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | f x ≤ r }) :
    QuasiconvexOn 𝕜 s f := fun r => hs.inter (h r)

theorem Convex.quasiconcave_on_of_convex_ge (hs : Convex 𝕜 s) (h : ∀ r, Convex 𝕜 { x | r ≤ f x }) :
    QuasiconcaveOn 𝕜 s f :=
  @Convex.quasiconvex_on_of_convex_le 𝕜 E βᵒᵈ _ _ _ _ _ _ hs h

theorem QuasiconvexOn.convex [IsDirected β (· ≤ ·)] (hf : QuasiconvexOn 𝕜 s f) : Convex 𝕜 s :=
  fun x y hx hy a b ha hb hab =>
  let ⟨z, hxz, hyz⟩ := exists_ge_ge (f x) (f y)
  (hf _ ⟨hx, hxz⟩ ⟨hy, hyz⟩ ha hb hab).1

theorem QuasiconcaveOn.convex [IsDirected β (· ≥ ·)] (hf : QuasiconcaveOn 𝕜 s f) : Convex 𝕜 s :=
  hf.dual.Convex

end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid β]

section HasSmul

variable [HasSmul 𝕜 E] {s : Set E} {f g : E → β}

theorem QuasiconvexOn.sup (hf : QuasiconvexOn 𝕜 s f) (hg : QuasiconvexOn 𝕜 s g) : QuasiconvexOn 𝕜 s (f⊔g) := by
  intro r
  simp_rw [Pi.sup_def, sup_le_iff, ← Set.sep_inter_sep]
  exact (hf r).inter (hg r)

theorem QuasiconcaveOn.inf (hf : QuasiconcaveOn 𝕜 s f) (hg : QuasiconcaveOn 𝕜 s g) : QuasiconcaveOn 𝕜 s (f⊓g) :=
  hf.dual.sup hg

theorem quasiconvex_on_iff_le_max :
    QuasiconvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ max (f x) (f y) :=
  ⟨fun hf =>
    ⟨hf.Convex, fun x y hx hy a b ha hb hab => (hf _ ⟨hx, le_max_leftₓ _ _⟩ ⟨hy, le_max_rightₓ _ _⟩ ha hb hab).2⟩,
    fun hf r x y hx hy a b ha hb hab =>
    ⟨hf.1 hx.1 hy.1 ha hb hab, (hf.2 hx.1 hy.1 ha hb hab).trans <| max_leₓ hx.2 hy.2⟩⟩

theorem quasiconcave_on_iff_min_le :
    QuasiconcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → min (f x) (f y) ≤ f (a • x + b • y) :=
  @quasiconvex_on_iff_le_max 𝕜 E βᵒᵈ _ _ _ _ _ _

theorem quasilinear_on_iff_mem_interval :
    QuasilinearOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y : E⦄,
          x ∈ s → y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ∈ Interval (f x) (f y) :=
  by
  rw [QuasilinearOn, quasiconvex_on_iff_le_max, quasiconcave_on_iff_min_le, and_and_and_comm, and_selfₓ]
  apply and_congr_right'
  simp_rw [← forall_and_distrib, interval, mem_Icc, and_comm]

theorem QuasiconvexOn.convex_lt (hf : QuasiconvexOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | f x < r }) := by
  refine' fun x y hx hy a b ha hb hab => _
  have h := hf _ ⟨hx.1, le_max_leftₓ _ _⟩ ⟨hy.1, le_max_rightₓ _ _⟩ ha hb hab
  exact ⟨h.1, h.2.trans_lt <| max_ltₓ hx.2 hy.2⟩

theorem QuasiconcaveOn.convex_gt (hf : QuasiconcaveOn 𝕜 s f) (r : β) : Convex 𝕜 ({ x ∈ s | r < f x }) :=
  hf.dual.convex_lt r

end HasSmul

section OrderedSmul

variable [HasSmul 𝕜 E] [Module 𝕜 β] [OrderedSmul 𝕜 β] {s : Set E} {f : E → β}

theorem ConvexOn.quasiconvex_on (hf : ConvexOn 𝕜 s f) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le

theorem ConcaveOn.quasiconcave_on (hf : ConcaveOn 𝕜 s f) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge

end OrderedSmul

end LinearOrderedAddCommMonoid

end AddCommMonoidₓ

section LinearOrderedAddCommMonoid

variable [LinearOrderedAddCommMonoid E] [OrderedAddCommMonoid β] [Module 𝕜 E] [OrderedSmul 𝕜 E] {s : Set E} {f : E → β}

theorem MonotoneOn.quasiconvex_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

theorem MonotoneOn.quasiconcave_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

theorem MonotoneOn.quasilinear_on (hf : MonotoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.QuasiconvexOn hs, hf.QuasiconcaveOn hs⟩

theorem AntitoneOn.quasiconvex_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconvexOn 𝕜 s f :=
  hf.convex_le hs

theorem AntitoneOn.quasiconcave_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasiconcaveOn 𝕜 s f :=
  hf.convex_ge hs

theorem AntitoneOn.quasilinear_on (hf : AntitoneOn f s) (hs : Convex 𝕜 s) : QuasilinearOn 𝕜 s f :=
  ⟨hf.QuasiconvexOn hs, hf.QuasiconcaveOn hs⟩

theorem Monotone.quasiconvex_on (hf : Monotone f) : QuasiconvexOn 𝕜 Univ f :=
  (hf.MonotoneOn _).QuasiconvexOn convex_univ

theorem Monotone.quasiconcave_on (hf : Monotone f) : QuasiconcaveOn 𝕜 Univ f :=
  (hf.MonotoneOn _).QuasiconcaveOn convex_univ

theorem Monotone.quasilinear_on (hf : Monotone f) : QuasilinearOn 𝕜 Univ f :=
  ⟨hf.QuasiconvexOn, hf.QuasiconcaveOn⟩

theorem Antitone.quasiconvex_on (hf : Antitone f) : QuasiconvexOn 𝕜 Univ f :=
  (hf.AntitoneOn _).QuasiconvexOn convex_univ

theorem Antitone.quasiconcave_on (hf : Antitone f) : QuasiconcaveOn 𝕜 Univ f :=
  (hf.AntitoneOn _).QuasiconcaveOn convex_univ

theorem Antitone.quasilinear_on (hf : Antitone f) : QuasilinearOn 𝕜 Univ f :=
  ⟨hf.QuasiconvexOn, hf.QuasiconcaveOn⟩

end LinearOrderedAddCommMonoid

end OrderedSemiring

