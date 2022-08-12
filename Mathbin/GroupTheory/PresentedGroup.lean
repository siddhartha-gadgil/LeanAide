/-
Copyright (c) 2019 Michael Howes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Howes
-/
import Mathbin.GroupTheory.FreeGroup
import Mathbin.GroupTheory.QuotientGroup

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `presented_group rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `to_group f`: the canonical group homomorphism `presented_group rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/


variable {α : Type}

/-- Given a set of relations, rels, over a type `α`, presented_group constructs the group with
generators `x : α` and relations `rels` as a quotient of free_group `α`.-/
def PresentedGroup (rels : Set (FreeGroup α)) : Type :=
  FreeGroup α ⧸ Subgroup.normalClosure rels

namespace PresentedGroup

instance (rels : Set (FreeGroup α)) : Groupₓ (PresentedGroup rels) :=
  QuotientGroup.Quotient.group _

/-- `of` is the canonical map from `α` to a presented group with generators `x : α`. The term `x` is
mapped to the equivalence class of the image of `x` in `free_group α`. -/
def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  QuotientGroup.mk (FreeGroup.of x)

section ToGroup

/-
Presented groups satisfy a universal property. If `G` is a group and `f : α → G` is a map such that
the images of `f` satisfy all the given relations, then `f` extends uniquely to a group homomorphism
from `presented_group rels` to `G`.
-/
variable {G : Type} [Groupₓ G] {f : α → G} {rels : Set (FreeGroup α)}

-- mathport name: «exprF»
local notation "F" => FreeGroup.lift f

variable (h : ∀, ∀ r ∈ rels, ∀, F r = 1)

theorem closure_rels_subset_ker : Subgroup.normalClosure rels ≤ MonoidHom.ker F :=
  Subgroup.normal_closure_le_normal fun x w => (MonoidHom.mem_ker _).2 (h x w)

theorem to_group_eq_one_of_mem_closure : ∀, ∀ x ∈ Subgroup.normalClosure rels, ∀, F x = 1 := fun x w =>
  (MonoidHom.mem_ker _).1 <| closure_rels_subset_ker h w

/-- The extension of a map `f : α → G` that satisfies the given relations to a group homomorphism
from `presented_group rels → G`. -/
def toGroup : PresentedGroup rels →* G :=
  QuotientGroup.lift (Subgroup.normalClosure rels) F (to_group_eq_one_of_mem_closure h)

@[simp]
theorem toGroup.of {x : α} : toGroup h (of x) = f x :=
  FreeGroup.lift.of

theorem toGroup.unique (g : PresentedGroup rels →* G) (hg : ∀ x : α, g (of x) = f x) : ∀ {x}, g x = toGroup h x :=
  fun x => QuotientGroup.induction_on x fun _ => FreeGroup.lift.unique (g.comp (QuotientGroup.mk' _)) hg

end ToGroup

instance (rels : Set (FreeGroup α)) : Inhabited (PresentedGroup rels) :=
  ⟨1⟩

end PresentedGroup

