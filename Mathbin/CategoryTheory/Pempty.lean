/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

namespace Functor

variable (C : Type u) [Category.{v} C]

/-- Equivalence between two empty categories. -/
def emptyEquivalence : Discrete.{w} Pempty ≌ Discrete.{v} Pempty :=
  Equivalence.mk { obj := Pempty.elimₓ ∘ discrete.as, map := fun x => x.as.elim }
    { obj := Pempty.elimₓ ∘ discrete.as, map := fun x => x.as.elim }
    (by
      tidy)
    (by
      tidy)

/-- The canonical functor out of the empty category. -/
def empty : Discrete.{w} Pempty ⥤ C :=
  Discrete.functor Pempty.elimₓ

variable {C}

/-- Any two functors out of the empty category are isomorphic. -/
def emptyExt (F G : Discrete.{w} Pempty ⥤ C) : F ≅ G :=
  Discrete.natIso fun x => x.as.elim

/-- Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def uniqueFromEmpty (F : Discrete.{w} Pempty ⥤ C) : F ≅ empty C :=
  emptyExt _ _

/-- Any two functors out of the empty category are *equal*. You probably want to use
`empty_ext` instead of this.
-/
theorem empty_ext' (F G : Discrete.{w} Pempty ⥤ C) : F = G :=
  Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim

end Functor

end CategoryTheory

