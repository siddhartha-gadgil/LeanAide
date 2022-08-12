/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Bifunctor
import Mathbin.Control.Traversable.Basic

/-!
# Bitraversable type class

Type class for traversing bifunctors.

Simple examples of `bitraversable` are `prod` and `sum`. A more elaborate example is
to define an a-list as:

```
def alist (key val : Type) := list (key × val)
```

Then we can use `f : key → io key'` and `g : val → io val'` to manipulate the `alist`'s key
and value respectively with `bitraverse f g : alist key val → io (alist key' val')`

## Main definitions

* `bitraversable`: Bare typeclass to hold the `bitraverse` function.
* `is_lawful_bitraversable`: Typeclass for the laws of the `bitraverse` function. Similar to
  `is_lawful_traversable`.

## References

The concepts and laws are taken from
<https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable iterator functor bifunctor applicative
-/


universe u

/-- Lawless bitraversable bifunctor. This only holds data for the bimap and bitraverse. -/
class Bitraversable (t : Type u → Type u → Type u) extends Bifunctor t where
  bitraverse : ∀ {m : Type u → Type u} [Applicativeₓ m] {α α' β β'}, (α → m α') → (β → m β') → t α β → m (t α' β')

export Bitraversable (bitraverse)

/-- A bitraversable functor commutes with all applicative functors. -/
def bisequence {t m} [Bitraversable t] [Applicativeₓ m] {α β} : t (m α) (m β) → m (t α β) :=
  bitraverse id id

open Functor

/-- Bifunctor. This typeclass asserts that a lawless bitraversable bifunctor is lawful. -/
class IsLawfulBitraversable (t : Type u → Type u → Type u) [Bitraversable t] extends IsLawfulBifunctor t where
  id_bitraverse : ∀ {α β} (x : t α β), bitraverse id.mk id.mk x = id.mk x
  comp_bitraverse :
    ∀ {F G} [Applicativeₓ F] [Applicativeₓ G] [IsLawfulApplicative F] [IsLawfulApplicative G] {α α' β β' γ γ'}
      (f : β → F γ) (f' : β' → F γ') (g : α → G β) (g' : α' → G β') (x : t α α'),
      bitraverse (comp.mk ∘ map f ∘ g) (comp.mk ∘ map f' ∘ g') x = Comp.mk (bitraverse f f' <$> bitraverse g g' x)
  bitraverse_eq_bimap_id :
    ∀ {α α' β β'} (f : α → β) (f' : α' → β') (x : t α α'), bitraverse (id.mk ∘ f) (id.mk ∘ f') x = id.mk (bimap f f' x)
  binaturality :
    ∀ {F G} [Applicativeₓ F] [Applicativeₓ G] [IsLawfulApplicative F] [IsLawfulApplicative G]
      (η : ApplicativeTransformation F G) {α α' β β'} (f : α → F β) (f' : α' → F β') (x : t α α'),
      η (bitraverse f f' x) = bitraverse (@η _ ∘ f) (@η _ ∘ f') x

export IsLawfulBitraversable (id_bitraverse comp_bitraverse bitraverse_eq_bimap_id)

open IsLawfulBitraversable

attribute [higher_order bitraverse_id_id] id_bitraverse

attribute [higher_order bitraverse_comp] comp_bitraverse

attribute [higher_order] binaturality bitraverse_eq_bimap_id

export IsLawfulBitraversable (bitraverse_id_id bitraverse_comp)

