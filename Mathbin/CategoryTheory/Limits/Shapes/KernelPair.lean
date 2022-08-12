/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Shapes.RegularMono

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f`
then it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `is_limit (pullback_cone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/


universe v u u₂

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/-- `is_kernel_pair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is essentially just a convenience wrapper over `is_limit (pullback_cone.mk _ _ _)`.
-/
structure IsKernelPair where
  comm : a ≫ f = b ≫ f
  IsLimit : IsLimit (PullbackCone.mk _ _ comm)

attribute [reassoc] is_kernel_pair.comm

namespace IsKernelPair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
instance : Subsingleton (IsKernelPair f a b) :=
  ⟨fun P Q => by
    cases P
    cases Q
    congr⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)`  is a kernel pair for `f`. -/
def idOfMono [Mono f] : IsKernelPair f (𝟙 _) (𝟙 _) :=
  ⟨rfl, PullbackCone.isLimitMkIdId _⟩

instance [Mono f] : Inhabited (IsKernelPair f (𝟙 _) (𝟙 _)) :=
  ⟨idOfMono f⟩

variable {f a b}

/-- Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
def lift' {S : C} (k : IsKernelPair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) : { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
  PullbackCone.IsLimit.lift' k.IsLimit _ _ w

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
def cancelRight {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : IsKernelPair (f₁ ≫ f₂) a b) :
    IsKernelPair f₁ a b :=
  { comm,
    IsLimit :=
      (PullbackCone.isLimitAux' _) fun s => by
        let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) := pullback_cone.mk s.fst s.snd (s.condition_assoc _)
        refine'
          ⟨big_k.is_limit.lift s', big_k.is_limit.fac _ walking_cospan.left, big_k.is_limit.fac _ walking_cospan.right,
            fun m m₁ m₂ => _⟩
        apply big_k.is_limit.hom_ext
        refine' (pullback_cone.mk a b _ : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _
        apply m₁.trans (big_k.is_limit.fac s' walking_cospan.left).symm
        apply m₂.trans (big_k.is_limit.fac s' walking_cospan.right).symm }

/-- If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
def cancelRightOfMono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (big_k : IsKernelPair (f₁ ≫ f₂) a b) : IsKernelPair f₁ a b :=
  cancelRight
    (by
      rw [← cancel_mono f₂, assoc, assoc, big_k.comm])
    big_k

/-- If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
def compOfMono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [Mono f₂] (small_k : IsKernelPair f₁ a b) : IsKernelPair (f₁ ≫ f₂) a b where
  comm := by
    rw [small_k.comm_assoc]
  IsLimit :=
    (PullbackCone.isLimitAux' _) fun s => by
      refine' ⟨_, _, _, _⟩
      apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).1
      rw [← cancel_mono f₂, assoc, s.condition, assoc]
      apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1
      apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2
      intro m m₁ m₂
      apply small_k.is_limit.hom_ext
      refine' (pullback_cone.mk a b _ : pullback_cone f₁ _).equalizer_ext _ _
      rwa [(pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1]
      rwa [(pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2]

/-- If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def toCoequalizer (k : IsKernelPair f a b) [r : RegularEpi f] : IsColimit (Cofork.ofπ f k.comm) := by
  let t := k.is_limit.lift (pullback_cone.mk _ _ r.w)
  have ht : t ≫ a = r.left := k.is_limit.fac _ walking_cospan.left
  have kt : t ≫ b = r.right := k.is_limit.fac _ walking_cospan.right
  apply cofork.is_colimit.mk _ _ _ _
  · intro s
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).1
    rw [← ht, assoc, s.condition, reassoc_of kt]
    
  · intro s
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).2
    
  · intro s m w
    apply r.is_colimit.hom_ext
    rintro ⟨⟩
    change (r.left ≫ f) ≫ m = (r.left ≫ f) ≫ _
    rw [assoc, assoc]
    congr 1
    erw [(cofork.is_colimit.desc' r.is_colimit s.π _).2]
    apply w
    erw [(cofork.is_colimit.desc' r.is_colimit s.π _).2]
    apply w
    

end IsKernelPair

end CategoryTheory

