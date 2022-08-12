/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import Mathbin.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathbin.CategoryTheory.Punit

/-!
# Fundamental groupoid of punit

The fundamental groupoid of punit is naturally isomorphic to `category_theory.discrete punit`
-/


noncomputable section

open CategoryTheory

universe u v

namespace Path

instance : Subsingleton (Path PUnit.unit PUnit.unit) :=
  ⟨fun x y => by
    ext⟩

end Path

namespace FundamentalGroupoid

instance {x y : FundamentalGroupoid PUnit} : Subsingleton (x ⟶ y) := by
  convert_to Subsingleton (Path.Homotopic.Quotient PUnit.unit PUnit.unit)
  · congr <;> apply punit_eq_star
    
  apply Quotientₓ.subsingleton

/-- Equivalence of groupoids between fundamental groupoid of punit and punit -/
def punitEquivDiscretePunit : FundamentalGroupoid PUnit.{u + 1} ≌ Discrete PUnit.{v + 1} :=
  Equivalence.mk (Functor.star _) ((CategoryTheory.Functor.const _).obj PUnit.unit)
    (NatIso.ofComponents
      (fun _ =>
        eqToIso
          (by
            decide))
      fun _ _ _ => by
      decide)
    (Functor.punitExt _ _)

end FundamentalGroupoid

