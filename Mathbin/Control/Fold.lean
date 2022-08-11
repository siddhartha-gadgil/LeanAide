/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather
-/
import Mathbin.Algebra.FreeMonoid
import Mathbin.Algebra.Opposites
import Mathbin.Control.Traversable.Instances
import Mathbin.Control.Traversable.Lemmas
import Mathbin.CategoryTheory.Endomorphism
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Category.Kleisli

/-!

# List folds generalized to `traversable`

Informally, we can think of `foldl` as a special case of `traverse` where we do not care about the
reconstructed data structure and, in a state monad, we care about the final state.

The obvious way to define `foldl` would be to use the state monad but it
is nicer to reason about a more abstract interface with `fold_map` as a
primitive and `fold_map_hom` as a defining property.

```
def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω := ...

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α →* β)
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
...
```

`fold_map` uses a monoid ω to accumulate a value for every element of
a data structure and `fold_map_hom` uses a monoid homomorphism to
substitute the monoid used by `fold_map`. The two are sufficient to
define `foldl`, `foldr` and `to_list`. `to_list` permits the
formulation of specifications in terms of operations on lists.

Each fold function can be defined using a specialized
monoid. `to_list` uses a free monoid represented as a list with
concatenation while `foldl` uses endofunctions together with function
composition.

The definition through monoids uses `traverse` together with the
applicative functor `const m` (where `m` is the monoid). As an
implementation, `const` guarantees that no resource is spent on
reconstructing the structure during traversal.

A special class could be defined for `foldable`, similarly to Haskell,
but the author cannot think of instances of `foldable` that are not also
`traversable`.
-/


universe u v

open ULift CategoryTheory MulOpposite

namespace Monoidₓ

variable {m : Type u → Type u} [Monadₓ m]

variable {α β : Type u}

/-- For a list, foldl f x [y₀,y₁] reduces as follows:

```
calc  foldl f x [y₀,y₁]
    = foldl f (f x y₀) [y₁]      : rfl
... = foldl f (f (f x y₀) y₁) [] : rfl
... = f (f x y₀) y₁              : rfl
```
with
```
f : α → β → α
x : α
[y₀,y₁] : list β
```

We can view the above as a composition of functions:
```
... = f (f x y₀) y₁              : rfl
... = flip f y₁ (flip f y₀ x)    : rfl
... = (flip f y₁ ∘ flip f y₀) x  : rfl
```

We can use traverse and const to construct this composition:
```
calc   const.run (traverse (λ y, const.mk' (flip f y)) [y₀,y₁]) x
     = const.run ((::) <$> const.mk' (flip f y₀) <*> traverse (λ y, const.mk' (flip f y)) [y₁]) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> traverse (λ y, const.mk' (flip f y)) [] )) x
...  = const.run ((::) <$> const.mk' (flip f y₀) <*>
         ( (::) <$> const.mk' (flip f y₁) <*> pure [] )) x
...  = const.run ( ((::) <$> const.mk' (flip f y₁) <*> pure []) ∘
         ((::) <$> const.mk' (flip f y₀)) ) x
...  = const.run ( const.mk' (flip f y₁) ∘ const.mk' (flip f y₀) ) x
...  = const.run ( flip f y₁ ∘ flip f y₀ ) x
...  = f (f x y₀) y₁
```

And this is how `const` turns a monoid into an applicative functor and
how the monoid of endofunctions define `foldl`.
-/
@[reducible]
def Foldl (α : Type u) : Type u :=
  (End α)ᵐᵒᵖ

def Foldl.mk (f : α → α) : Foldl α :=
  op f

def Foldl.get (x : Foldl α) : α → α :=
  unop x

@[simps]
def Foldl.ofFreeMonoid (f : β → α → β) : FreeMonoid α →* Monoidₓ.Foldl β where
  toFun := fun xs => op <| flip (List.foldlₓ f) xs
  map_one' := rfl
  map_mul' := by
    intros <;> simp only [← FreeMonoid.mul_def, ← flip, ← unop_op, ← List.foldl_append, ← op_inj] <;> rfl

@[reducible]
def Foldr (α : Type u) : Type u :=
  End α

def Foldr.mk (f : α → α) : Foldr α :=
  f

def Foldr.get (x : Foldr α) : α → α :=
  x

@[simps]
def Foldr.ofFreeMonoid (f : α → β → β) : FreeMonoid α →* Monoidₓ.Foldr β where
  toFun := fun xs => flip (List.foldr f) xs
  map_one' := rfl
  map_mul' := by
    intros
    simp only [← FreeMonoid.mul_def, ← List.foldr_append, ← flip]
    rfl

@[reducible]
def Mfoldl (m : Type u → Type u) [Monadₓ m] (α : Type u) : Type u :=
  MulOpposite <| End <| KleisliCat.mk m α

def Mfoldl.mk (f : α → m α) : Mfoldl m α :=
  op f

def Mfoldl.get (x : Mfoldl m α) : α → m α :=
  unop x

@[simps]
def Mfoldl.ofFreeMonoid [IsLawfulMonad m] (f : β → α → m β) : FreeMonoid α →* Monoidₓ.Mfoldl m β where
  toFun := fun xs => op <| flip (List.mfoldl f) xs
  map_one' := rfl
  map_mul' := by
    intros <;> apply unop_injective <;> ext <;> apply List.mfoldl_append

@[reducible]
def Mfoldr (m : Type u → Type u) [Monadₓ m] (α : Type u) : Type u :=
  End <| KleisliCat.mk m α

def Mfoldr.mk (f : α → m α) : Mfoldr m α :=
  f

def Mfoldr.get (x : Mfoldr m α) : α → m α :=
  x

@[simps]
def Mfoldr.ofFreeMonoid [IsLawfulMonad m] (f : α → β → m β) : FreeMonoid α →* Monoidₓ.Mfoldr m β where
  toFun := fun xs => flip (List.mfoldr f) xs
  map_one' := rfl
  map_mul' := by
    intros <;> ext <;> apply List.mfoldr_append

end Monoidₓ

namespace Traversable

open Monoidₓ Functor

section Defs

variable {α β : Type u} {t : Type u → Type u} [Traversable t]

def foldMap {α ω} [One ω] [Mul ω] (f : α → ω) : t α → ω :=
  traverse (const.mk' ∘ f)

def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
  (foldMap (foldl.mk ∘ flip f) xs).get x

def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
  (foldMap (foldr.mk ∘ f) xs).get x

/-- Conceptually, `to_list` collects all the elements of a collection
in a list. This idea is formalized by

  `lemma to_list_spec (x : t α) : to_list x = fold_map free_monoid.mk x`.

The definition of `to_list` is based on `foldl` and `list.cons` for
speed. It is faster than using `fold_map free_monoid.mk` because, by
using `foldl` and `list.cons`, each insertion is done in constant
time. As a consequence, `to_list` performs in linear.

On the other hand, `fold_map free_monoid.mk` creates a singleton list
around each element and concatenates all the resulting lists. In
`xs ++ ys`, concatenation takes a time proportional to `length xs`. Since
the order in which concatenation is evaluated is unspecified, nothing
prevents each element of the traversable to be appended at the end
`xs ++ [x]` which would yield a `O(n²)` run time. -/
def toList : t α → List α :=
  List.reverse ∘ foldl (flip List.cons) []

def length (xs : t α) : ℕ :=
  down <| foldl (fun l _ => up <| l.down + 1) (up 0) xs

variable {m : Type u → Type u} [Monadₓ m]

def mfoldl (f : α → β → m α) (x : α) (xs : t β) : m α :=
  (foldMap (mfoldl.mk ∘ flip f) xs).get x

def mfoldr (f : α → β → m β) (x : β) (xs : t α) : m β :=
  (foldMap (mfoldr.mk ∘ f) xs).get x

end Defs

section ApplicativeTransformation

variable {α β γ : Type u}

open Function hiding const

def mapFold [Monoidₓ α] [Monoidₓ β] (f : α →* β) : ApplicativeTransformation (Const α) (Const β) where
  app := fun x => f
  preserves_seq' := by
    intros
    simp only [← f.map_mul, ← (· <*> ·)]
  preserves_pure' := by
    intros
    simp only [← f.map_one, ← pure]

def Free.mk : α → FreeMonoid α :=
  List.ret

def Free.map (f : α → β) : FreeMonoid α →* FreeMonoid β where
  toFun := List.map f
  map_mul' := fun x y => by
    simp only [← FreeMonoid.mul_def, ← List.map_append, ← FreeAddMonoid.add_def]
  map_one' := by
    simp only [← FreeMonoid.one_def, ← List.map, ← FreeAddMonoid.zero_def]

theorem Free.map_eq_map (f : α → β) (xs : List α) : f <$> xs = Free.map f xs :=
  rfl

theorem foldl.unop_of_free_monoid (f : β → α → β) (xs : FreeMonoid α) (a : β) :
    unop (Foldl.ofFreeMonoid f xs) a = List.foldlₓ f a xs :=
  rfl

variable (m : Type u → Type u) [Monadₓ m] [IsLawfulMonad m]

variable {t : Type u → Type u} [Traversable t] [IsLawfulTraversable t]

open IsLawfulTraversable

theorem fold_map_hom [Monoidₓ α] [Monoidₓ β] (f : α →* β) (g : γ → α) (x : t γ) : f (foldMap g x) = foldMap (f ∘ g) x :=
  calc
    f (foldMap g x) = f (traverse (const.mk' ∘ g) x) := rfl
    _ = (mapFold f).app _ (traverse (const.mk' ∘ g) x) := rfl
    _ = traverse ((mapFold f).app _ ∘ const.mk' ∘ g) x := naturality (mapFold f) _ _
    _ = foldMap (f ∘ g) x := rfl
    

theorem fold_map_hom_free [Monoidₓ β] (f : FreeMonoid α →* β) (x : t α) :
    f (foldMap Free.mk x) = foldMap (f ∘ free.mk) x :=
  fold_map_hom f _ x

variable {m}

theorem fold_mfoldl_cons (f : α → β → m α) (x : β) (y : α) : List.mfoldl f y (Free.mk x) = f y x := by
  simp only [← free.mk, ← List.ret, ← List.mfoldl, ← bind_pureₓ]

theorem fold_mfoldr_cons (f : β → α → m α) (x : β) (y : α) : List.mfoldr f y (Free.mk x) = f x y := by
  simp only [← free.mk, ← List.ret, ← List.mfoldr, ← pure_bind]

end ApplicativeTransformation

section Equalities

open IsLawfulTraversable

open List (cons)

variable {α β γ : Type u}

variable {t : Type u → Type u} [Traversable t] [IsLawfulTraversable t]

@[simp]
theorem foldl.of_free_monoid_comp_free_mk (f : α → β → α) : Foldl.ofFreeMonoid f ∘ free.mk = foldl.mk ∘ flip f :=
  rfl

@[simp]
theorem foldr.of_free_monoid_comp_free_mk (f : β → α → α) : Foldr.ofFreeMonoid f ∘ free.mk = foldr.mk ∘ f :=
  rfl

@[simp]
theorem mfoldl.of_free_monoid_comp_free_mk {m} [Monadₓ m] [IsLawfulMonad m] (f : α → β → m α) :
    Mfoldl.ofFreeMonoid f ∘ free.mk = mfoldl.mk ∘ flip f := by
  ext <;> simp [← (· ∘ ·), ← mfoldl.of_free_monoid, ← mfoldl.mk, ← flip, ← fold_mfoldl_cons] <;> rfl

@[simp]
theorem mfoldr.of_free_monoid_comp_free_mk {m} [Monadₓ m] [IsLawfulMonad m] (f : β → α → m α) :
    Mfoldr.ofFreeMonoid f ∘ free.mk = mfoldr.mk ∘ f := by
  ext
  simp [← (· ∘ ·), ← mfoldr.of_free_monoid, ← mfoldr.mk, ← flip, ← fold_mfoldr_cons]

theorem to_list_spec (xs : t α) : toList xs = (foldMap Free.mk xs : FreeMonoid _) :=
  Eq.symm <|
    calc
      foldMap Free.mk xs = (foldMap Free.mk xs).reverse.reverse := by
        simp only [← List.reverse_reverse]
      _ = (List.foldr cons [] (foldMap Free.mk xs).reverse).reverse := by
        simp only [← List.foldr_eta]
      _ = (unop (Foldl.ofFreeMonoid (flip cons) (foldMap Free.mk xs)) []).reverse := by
        simp [← flip, ← List.foldr_reverse, ← foldl.of_free_monoid, ← unop_op]
      _ = toList xs := by
        rw [fold_map_hom_free (foldl.of_free_monoid (flip <| @cons α))]
        simp only [← to_list, ← foldl, ← List.reverse_inj, ← foldl.get, ← foldl.of_free_monoid_comp_free_mk]
        all_goals
          infer_instance
      

theorem fold_map_map [Monoidₓ γ] (f : α → β) (g : β → γ) (xs : t α) : foldMap g (f <$> xs) = foldMap (g ∘ f) xs := by
  simp only [← fold_map, ← traverse_map]

theorem foldl_to_list (f : α → β → α) (xs : t β) (x : α) : foldl f x xs = List.foldlₓ f x (toList xs) := by
  rw [← foldl.unop_of_free_monoid]
  simp only [← foldl, ← to_list_spec, ← fold_map_hom_free, ← foldl.of_free_monoid_comp_free_mk, ← foldl.get]

theorem foldr_to_list (f : α → β → β) (xs : t α) (x : β) : foldr f x xs = List.foldr f x (toList xs) := by
  change _ = foldr.of_free_monoid _ _ _
  simp only [← foldr, ← to_list_spec, ← fold_map_hom_free, ← foldr.of_free_monoid_comp_free_mk, ← foldr.get]

theorem to_list_map (f : α → β) (xs : t α) : toList (f <$> xs) = f <$> toList xs := by
  simp only [← to_list_spec, ← free.map_eq_map, ← fold_map_hom (free.map f), ← fold_map_map] <;> rfl

@[simp]
theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
    foldl f a (g <$> l) = foldl (fun x y => f x (g y)) a l := by
  simp only [← foldl, ← fold_map_map, ← (· ∘ ·), ← flip]

@[simp]
theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) : foldr f a (g <$> l) = foldr (f ∘ g) a l := by
  simp only [← foldr, ← fold_map_map, ← (· ∘ ·), ← flip]

@[simp]
theorem to_list_eq_self {xs : List α} : toList xs = xs := by
  simp only [← to_list_spec, ← fold_map, ← traverse]
  induction xs
  case list.nil =>
    rfl
  case list.cons _ _ ih =>
    unfold List.traverseₓₓ List.ret
    rw [ih]
    rfl

theorem length_to_list {xs : t α} : length xs = List.length (toList xs) := by
  unfold length
  rw [foldl_to_list]
  generalize to_list xs = ys
  let f := fun (n : ℕ) (a : α) => n + 1
  trans List.foldlₓ f 0 ys
  · generalize 0 = n
    induction' ys with _ _ ih generalizing n
    · simp only [← List.foldl_nil]
      
    · simp only [← List.foldlₓ, ← ih (n + 1)]
      
    
  · induction' ys with _ tl ih
    · simp only [← List.length, ← List.foldl_nil]
      
    · simp only [← List.foldlₓ, ← List.length]
      rw [← ih]
      exact tl.foldl_hom (fun x => x + 1) f f 0 fun n x => rfl
      
    

variable {m : Type u → Type u} [Monadₓ m] [IsLawfulMonad m]

theorem mfoldl_to_list {f : α → β → m α} {x : α} {xs : t β} : mfoldl f x xs = List.mfoldl f x (toList xs) :=
  calc
    mfoldl f x xs = unop (Mfoldl.ofFreeMonoid f (toList xs)) x := by
      simp only [← mfoldl, ← to_list_spec, ← fold_map_hom_free (mfoldl.of_free_monoid f), ←
        mfoldl.of_free_monoid_comp_free_mk, ← mfoldl.get]
    _ = List.mfoldl f x (toList xs) := by
      simp [← mfoldl.of_free_monoid, ← unop_op, ← flip]
    

theorem mfoldr_to_list (f : α → β → m β) (x : β) (xs : t α) : mfoldr f x xs = List.mfoldr f x (toList xs) := by
  change _ = mfoldr.of_free_monoid f (to_list xs) x
  simp only [← mfoldr, ← to_list_spec, ← fold_map_hom_free (mfoldr.of_free_monoid f), ←
    mfoldr.of_free_monoid_comp_free_mk, ← mfoldr.get]

@[simp]
theorem mfoldl_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
    mfoldl f a (g <$> l) = mfoldl (fun x y => f x (g y)) a l := by
  simp only [← mfoldl, ← fold_map_map, ← (· ∘ ·), ← flip]

@[simp]
theorem mfoldr_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) : mfoldr f a (g <$> l) = mfoldr (f ∘ g) a l := by
  simp only [← mfoldr, ← fold_map_map, ← (· ∘ ·), ← flip]

end Equalities

end Traversable

