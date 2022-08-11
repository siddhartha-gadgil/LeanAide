/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Scott Morrison
-/
import Mathbin.CategoryTheory.Preadditive.Injective
import Mathbin.Algebra.Homology.Single

/-!
# Injective resolutions

A injective resolution `I : InjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed cochain complex `I.cocomplex` of injective objects,
along with a cochain map `I.ι` from cochain complex consisting just of `Z` in degree zero to `C`,
so that the augmented cochain complex is exact.
```
Z ----> 0 ----> ... ----> 0 ----> ...
|       |                 |
|       |                 |
v       v                 v
I⁰ ---> I¹ ---> ... ----> Iⁿ ---> ...
```
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open Injective

variable [HasZeroObject C] [HasZeroMorphisms C] [HasEqualizers C] [HasImages C]

/-- An `InjectiveResolution Z` consists of a bundled `ℕ`-indexed cochain complex of injective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

Except in situations where you want to provide a particular injective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `injective_resolution Z`: the `ℕ`-indexed cochain complex
  (equipped with `injective` and `exact` instances)
* `injective_resolution.ι Z`: the cochain map from  `(single C _ 0).obj Z` to
  `injective_resolution Z` (all the components are equipped with `mono` instances,
  and when the category is `abelian` we will show `ι` is a quasi-iso).
-/
@[nolint has_inhabited_instance]
structure InjectiveResolution (Z : C) where
  cocomplex : CochainComplex C ℕ
  ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex
  Injective : ∀ n, Injective (cocomplex.x n) := by
    run_tac
      tactic.apply_instance
  exact₀ : Exact (ι.f 0) (cocomplex.d 0 1) := by
    run_tac
      tactic.apply_instance
  exact : ∀ n, Exact (cocomplex.d n (n + 1)) (cocomplex.d (n + 1) (n + 2)) := by
    run_tac
      tactic.apply_instance
  mono : Mono (ι.f 0) := by
    run_tac
      tactic.apply_instance

attribute [instance] InjectiveResolution.injective InjectiveResolution.mono

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`out] []
/-- An object admits a injective resolution. -/
class HasInjectiveResolution (Z : C) : Prop where
  out : Nonempty (InjectiveResolution Z)

section

variable (C)

/-- You will rarely use this typeclass directly: it is implied by the combination
`[enough_injectives C]` and `[abelian C]`. -/
class HasInjectiveResolutions : Prop where
  out : ∀ Z : C, HasInjectiveResolution Z

attribute [instance] has_injective_resolutions.out

end

namespace InjectiveResolution

@[simp]
theorem ι_f_succ {Z : C} (I : InjectiveResolution Z) (n : ℕ) : I.ι.f (n + 1) = 0 := by
  apply zero_of_source_iso_zero
  dsimp'
  rfl

@[simp]
theorem ι_f_zero_comp_complex_d {Z : C} (I : InjectiveResolution Z) : I.ι.f 0 ≫ I.cocomplex.d 0 1 = 0 :=
  I.exact₀.w

@[simp]
theorem complex_d_comp {Z : C} (I : InjectiveResolution Z) (n : ℕ) :
    I.cocomplex.d n (n + 1) ≫ I.cocomplex.d (n + 1) (n + 2) = 0 :=
  (I.exact _).w

instance {Z : C} (I : InjectiveResolution Z) (n : ℕ) : CategoryTheory.Mono (I.ι.f n) := by
  cases n <;> infer_instance

/-- An injective object admits a trivial injective resolution: itself in degree 0. -/
def self (Z : C) [CategoryTheory.Injective Z] : InjectiveResolution Z where
  cocomplex := (CochainComplex.single₀ C).obj Z
  ι := 𝟙 ((CochainComplex.single₀ C).obj Z)
  Injective := fun n => by
    cases n <;>
      · dsimp'
        infer_instance
        
  exact₀ := by
    dsimp'
    exact exact_epi_zero _
  exact := fun n => by
    dsimp'
    exact exact_of_zero _ _
  mono := by
    dsimp'
    infer_instance

end InjectiveResolution

end CategoryTheory

