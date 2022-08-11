/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Functor

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `list`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → io response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : list email`, using calling
`invite` using `map` gives us the following: `map invite guests : list
(io response)`.  It is not what we need. We need something of type `io
(list response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : io (list response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `io` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
  * `traversable` type class - exposes the `traverse` function
  * `sequence` - based on `traverse`,
    turns a collection of effects into an effect returning a collection
  * `is_lawful_traversable` - laws for a traversable functor
  * `applicative_transformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

 * "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
   Journal of Functional Programming 18:1 (2008) 1-13, online at
   <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
 * "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
   in Mathematically-Structured Functional Programming, 2006, online at
   <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
 * "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
   in Mathematically-Structured Functional Programming, 2012,
   online at <http://arxiv.org/pdf/1202.2919>
-/


open Function hiding comp

universe u v w

section ApplicativeTransformation

variable (F : Type u → Type v) [Applicativeₓ F] [IsLawfulApplicative F]

variable (G : Type u → Type w) [Applicativeₓ G] [IsLawfulApplicative G]

/-- A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `has_pure.pure` and
`functor.map` (`<*>`) operations. See
`applicative_transformation.preserves_map` for naturality. -/
structure ApplicativeTransformation : Type max (u + 1) v w where
  app : ∀ α : Type u, F α → G α
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y

end ApplicativeTransformation

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicativeₓ F] [IsLawfulApplicative F]

variable (G : Type u → Type w) [Applicativeₓ G] [IsLawfulApplicative G]

instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨ApplicativeTransformation.app⟩

variable {F G}

@[simp]
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl

@[simp]
theorem coe_mk (f : ∀ α : Type u, F α → G α) (pp ps) : ⇑(ApplicativeTransformation.mk f pp ps) = f :=
  rfl

protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u} (x : F α) : η x = η' x :=
  congr_arg (fun η'' : ApplicativeTransformation F G => η'' x) h

protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α} (h : x = y) : η x = η y :=
  congr_arg (fun z : F α => η z) h

theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : ∀ α, F α → G α) = η') : η = η' := by
  cases η
  cases η'
  congr
  exact h

@[ext]
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) : η = η' := by
  apply coe_inj
  ext1 α
  exact funext (h α)

theorem ext_iff {η η' : ApplicativeTransformation F G} : η = η' ↔ ∀ (α : Type u) (x : F α), η x = η' x :=
  ⟨fun h α x => h ▸ rfl, fun h => ext h⟩

section Preserves

variable (η : ApplicativeTransformation F G)

@[functor_norm]
theorem preserves_pure : ∀ {α} (x : α), η (pure x) = pure x :=
  η.preserves_pure'

@[functor_norm]
theorem preserves_seq : ∀ {α β : Type u} (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'

@[functor_norm]
theorem preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y := by
  rw [← pure_seq_eq_map, η.preserves_seq] <;> simp' with functor_norm

theorem preserves_map' {α β} (x : α → β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  exact preserves_map η x y

end Preserves

/-- The identity applicative transformation from an applicative functor to itself. -/
def idTransformation : ApplicativeTransformation F F where
  app := fun α => id
  preserves_pure' := by
    simp
  preserves_seq' := fun α β x y => by
    simp

instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩

universe s t

variable {H : Type u → Type s} [Applicativeₓ H] [IsLawfulApplicative H]

/-- The composition of applicative transformations. -/
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) : ApplicativeTransformation F H where
  app := fun α x => η' (η x)
  preserves_pure' := fun α x => by
    simp' with functor_norm
  preserves_seq' := fun α β x y => by
    simp' with functor_norm

@[simp]
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) {α : Type u} (x : F α) :
    η'.comp η x = η' (η x) :=
  rfl

theorem comp_assoc {I : Type u → Type t} [Applicativeₓ I] [IsLawfulApplicative I] (η'' : ApplicativeTransformation H I)
    (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl

@[simp]
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun α x => rfl

@[simp]
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun α x => rfl

end ApplicativeTransformation

open ApplicativeTransformation

/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `list` and `m` is the applicative functor
`io`, then given a function `f : α → io β`, the function `functor.map f` is
`list α → list (io β)`, but `traverse f` is `list α → io (list β)`. -/
class Traversable (t : Type u → Type u) extends Functor t where
  traverse : ∀ {m : Type u → Type u} [Applicativeₓ m] {α β}, (α → m β) → t α → m (t β)

open Functor

export Traversable (traverse)

section Functions

variable {t : Type u → Type u}

variable {m : Type u → Type v} [Applicativeₓ m]

variable {α β : Type u}

variable {f : Type u → Type u} [Applicativeₓ f]

/-- A traversable functor commutes with all applicative functors. -/
def sequence [Traversable t] : t (f α) → f (t α) :=
  traverse id

end Functions

/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `id.mk` to `id.mk`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `λ x, f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
class IsLawfulTraversable (t : Type u → Type u) [Traversable t] extends IsLawfulFunctor t : Type (u + 1) where
  id_traverse : ∀ {α} (x : t α), traverse id.mk x = x
  comp_traverse :
    ∀ {F G} [Applicativeₓ F] [Applicativeₓ G] [IsLawfulApplicative F] [IsLawfulApplicative G] {α β γ} (f : β → F γ)
      (g : α → G β) (x : t α), traverse (comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α), traverse (id.mk ∘ f) x = id.mk (f <$> x)
  naturality :
    ∀ {F G} [Applicativeₓ F] [Applicativeₓ G] [IsLawfulApplicative F] [IsLawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α → F β) (x : t α), η (traverse f x) = traverse (@η _ ∘ f) x

instance : Traversable id :=
  ⟨fun _ _ _ _ => id⟩

instance : IsLawfulTraversable id := by
  refine' { .. } <;> intros <;> rfl

section

variable {F : Type u → Type v} [Applicativeₓ F]

instance : Traversable Option :=
  ⟨@Option.traverseₓₓ⟩

instance : Traversable List :=
  ⟨@List.traverseₓₓ⟩

end

namespace Sum

variable {σ : Type u}

variable {F : Type u → Type u}

variable [Applicativeₓ F]

/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `traversable` instance for the functor `σ ⊕ -`. -/
protected def traverseₓ {α β} (f : α → F β) : Sum σ α → F (Sum σ β)
  | Sum.inl x => pure (Sum.inl x)
  | Sum.inr x => Sum.inr <$> f x

end Sum

instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverseₓ _⟩

