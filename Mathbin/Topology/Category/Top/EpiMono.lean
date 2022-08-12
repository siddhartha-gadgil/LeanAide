/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathbin.Topology.Category.Top.Adjunctions
import Mathbin.CategoryTheory.EpiMono

/-!
# Epi- and monomorphisms in `Top`

This file shows that a continuous function is an epimorphism in the category of topological spaces
if and only if it is surjective, and that a continuous function is a monomorphism in the category of
topological spaces if and only if it is injective.
-/


universe u

open CategoryTheory

open Top

namespace Top

theorem epi_iff_surjective {X Y : Top.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := by
  suffices epi f ↔ epi ((forget Top).map f) by
    rw [this, CategoryTheory.epi_iff_surjective]
    rfl
  constructor
  · intro
    infer_instance
    
  · apply functor.epi_of_epi_map
    

theorem mono_iff_injective {X Y : Top.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := by
  suffices mono f ↔ mono ((forget Top).map f) by
    rw [this, CategoryTheory.mono_iff_injective]
    rfl
  constructor
  · intro
    infer_instance
    
  · apply functor.mono_of_mono_map
    

end Top

