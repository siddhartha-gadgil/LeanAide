/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Pi
import Mathbin.Algebra.Module.Pi

/-!
# `star` on pi types

We put a `has_star` structure on pi types that operates elementwise, such that it describes the
complex conjugation of vectors.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
namespace Pi

instance [∀ i, HasStar (f i)] : HasStar (∀ i, f i) where star := fun x i => star (x i)

@[simp]
theorem star_apply [∀ i, HasStar (f i)] (x : ∀ i, f i) (i : I) : star x i = star (x i) :=
  rfl

theorem star_def [∀ i, HasStar (f i)] (x : ∀ i, f i) : star x = fun i => star (x i) :=
  rfl

instance [∀ i, HasInvolutiveStar (f i)] :
    HasInvolutiveStar (∀ i, f i) where star_involutive := fun _ => funext fun _ => star_star _

instance [∀ i, Semigroupₓ (f i)] [∀ i, StarSemigroup (f i)] :
    StarSemigroup (∀ i, f i) where star_mul := fun _ _ => funext fun _ => star_mul _ _

instance [∀ i, AddMonoidₓ (f i)] [∀ i, StarAddMonoid (f i)] :
    StarAddMonoid (∀ i, f i) where star_add := fun _ _ => funext fun _ => star_add _ _

instance [∀ i, NonUnitalSemiringₓ (f i)] [∀ i, StarRing (f i)] : StarRing (∀ i, f i) :=
  { Pi.starAddMonoid, (Pi.starSemigroup : StarSemigroup (∀ i, f i)) with }

instance {R : Type w} [∀ i, HasSmul R (f i)] [HasStar R] [∀ i, HasStar (f i)] [∀ i, StarModule R (f i)] :
    StarModule R (∀ i, f i) where star_smul := fun r x => funext fun i => star_smul r (x i)

theorem single_star [∀ i, AddMonoidₓ (f i)] [∀ i, StarAddMonoid (f i)] [DecidableEq I] (i : I) (a : f i) :
    Pi.single i (star a) = star (Pi.single i a) :=
  single_op (fun i => @star (f i) _) (fun i => star_zero _) i a

end Pi

namespace Function

theorem update_star [∀ i, HasStar (f i)] [DecidableEq I] (h : ∀ i : I, f i) (i : I) (a : f i) :
    Function.update (star h) i (star a) = star (Function.update h i a) :=
  funext fun j => (apply_update (fun i => star) h i a j).symm

end Function

