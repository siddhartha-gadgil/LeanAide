/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Star.Basic
import Mathbin.Algebra.Ring.Prod
import Mathbin.Algebra.Module.Prod

/-!
# `star` on product types

We put a `has_star` structure on product types that operates elementwise.
-/


universe u v w

variable {R : Type u} {S : Type v}

namespace Prod

instance [HasStar R] [HasStar S] : HasStar (R × S) where star := fun x => (star x.1, star x.2)

@[simp]
theorem fst_star [HasStar R] [HasStar S] (x : R × S) : (star x).1 = star x.1 :=
  rfl

@[simp]
theorem snd_star [HasStar R] [HasStar S] (x : R × S) : (star x).2 = star x.2 :=
  rfl

theorem star_def [HasStar R] [HasStar S] (x : R × S) : star x = (star x.1, star x.2) :=
  rfl

instance [HasInvolutiveStar R] [HasInvolutiveStar S] :
    HasInvolutiveStar (R × S) where star_involutive := fun _ => Prod.extₓ (star_star _) (star_star _)

instance [Semigroupₓ R] [Semigroupₓ S] [StarSemigroup R] [StarSemigroup S] :
    StarSemigroup (R × S) where star_mul := fun _ _ => Prod.extₓ (star_mul _ _) (star_mul _ _)

instance [AddMonoidₓ R] [AddMonoidₓ S] [StarAddMonoid R] [StarAddMonoid S] :
    StarAddMonoid (R × S) where star_add := fun _ _ => Prod.extₓ (star_add _ _) (star_add _ _)

instance [NonUnitalSemiringₓ R] [NonUnitalSemiringₓ S] [StarRing R] [StarRing S] : StarRing (R × S) :=
  { Prod.starAddMonoid, (Prod.starSemigroup : StarSemigroup (R × S)) with }

instance {α : Type w} [HasSmul α R] [HasSmul α S] [HasStar α] [HasStar R] [HasStar S] [StarModule α R]
    [StarModule α S] : StarModule α (R × S) where star_smul := fun r x => Prod.extₓ (star_smul _ _) (star_smul _ _)

end Prod

@[simp]
theorem Units.embed_product_star [Monoidₓ R] [StarSemigroup R] (u : Rˣ) :
    Units.embedProduct R (star u) = star (Units.embedProduct R u) :=
  rfl

