/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.Tropical.Basic
import Mathbin.Order.ConditionallyCompleteLattice

/-!

# Order on tropical algebraic structure

This file defines the orders induced on tropical algebraic structures by the underlying type.

## Main declarations

* `conditionally_complete_lattice (tropical R)`
* `conditionally_complete_linear_order (tropical R)`

## Implementation notes

The order induced is the definitionally equal underlying order, which makes the proofs and
constructions quicker to implement.

-/


variable {R S : Type _}

open Tropical

instance [HasSup R] : HasSup (Tropical R) where sup := fun x y => trop (untrop x⊔untrop y)

instance [HasInf R] : HasInf (Tropical R) where inf := fun x y => trop (untrop x⊓untrop y)

instance [SemilatticeInf R] : SemilatticeInf (Tropical R) :=
  { Tropical.hasInf, Tropical.partialOrder with le_inf := fun _ _ _ => le_inf, inf_le_left := fun _ _ => inf_le_left,
    inf_le_right := fun _ _ => inf_le_right }

instance [SemilatticeSup R] : SemilatticeSup (Tropical R) :=
  { Tropical.hasSup, Tropical.partialOrder with sup_le := fun _ _ _ => sup_le, le_sup_left := fun _ _ => le_sup_left,
    le_sup_right := fun _ _ => le_sup_right }

instance [Lattice R] : Lattice (Tropical R) :=
  { Tropical.semilatticeInf, Tropical.semilatticeSup with }

instance [HasSupₓ R] : HasSupₓ (Tropical R) where sup := fun s => trop (sup (untrop '' s))

instance [HasInfₓ R] : HasInfₓ (Tropical R) where inf := fun s => trop (inf (untrop '' s))

instance [ConditionallyCompleteLattice R] : ConditionallyCompleteLattice (Tropical R) :=
  { Tropical.hasSupₓ, Tropical.hasInfₓ, Tropical.lattice with
    le_cSup := fun s x hs hx => le_cSup (untrop_monotone.map_bdd_above hs) (Set.mem_image_of_mem untrop hx),
    cSup_le := fun s x hs hx => cSup_le (hs.Image untrop) (untrop_monotone.mem_upper_bounds_image hx),
    le_cInf := fun s x hs hx => le_cInf (hs.Image untrop) (untrop_monotone.mem_lower_bounds_image hx),
    cInf_le := fun s x hs hx => cInf_le (untrop_monotone.map_bdd_below hs) (Set.mem_image_of_mem untrop hx) }

instance [ConditionallyCompleteLinearOrder R] : ConditionallyCompleteLinearOrder (Tropical R) :=
  { Tropical.conditionallyCompleteLattice, Tropical.linearOrder with }

