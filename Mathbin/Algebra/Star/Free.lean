/-
Copyright (c) 2020 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Weiser
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.FreeAlgebra

/-!
# A *-algebra structure on the free algebra.

Reversing words gives a *-structure on the free monoid or on the free algebra on a type.

## Implementation note
We have this in a separate file, rather than in `algebra.free_monoid` and `algebra.free_algebra`,
to avoid importing `algebra.star.basic` into the entire hierarchy.
-/


namespace FreeMonoid

variable {α : Type _}

instance : StarSemigroup (FreeMonoid α) where
  star := List.reverse
  star_involutive := List.reverse_reverse
  star_mul := List.reverse_append

@[simp]
theorem star_of (x : α) : star (of x) = of x :=
  rfl

/-- Note that `star_one` is already a global simp lemma, but this one works with dsimp too -/
@[simp]
theorem star_one : star (1 : FreeMonoid α) = 1 :=
  rfl

end FreeMonoid

namespace FreeAlgebra

variable {R : Type _} [CommSemiringₓ R] {X : Type _}

/-- The star ring formed by reversing the elements of products -/
instance : StarRing (FreeAlgebra R X) where
  star := MulOpposite.unop ∘ lift R (MulOpposite.op ∘ ι R)
  star_involutive := fun x => by
    unfold HasStar.star
    simp only [← Function.comp_applyₓ]
    refine' FreeAlgebra.induction R X _ _ _ _ x <;> intros <;> simp [*]
  star_mul := fun a b => by
    simp
  star_add := fun a b => by
    simp

@[simp]
theorem star_ι (x : X) : star (ι R x) = ι R x := by
  simp [← star, ← HasStar.star]

@[simp]
theorem star_algebra_map (r : R) : star (algebraMap R (FreeAlgebra R X) r) = algebraMap R _ r := by
  simp [← star, ← HasStar.star]

/-- `star` as an `alg_equiv` -/
def starHom : FreeAlgebra R X ≃ₐ[R] (FreeAlgebra R X)ᵐᵒᵖ :=
  { starRingEquiv with
    commutes' := fun r => by
      simp [← star_algebra_map] }

end FreeAlgebra

