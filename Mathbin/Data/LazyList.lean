/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathbin.Tactic.Lint.Default

/-!
# Lazy lists

The type `lazy_list α` is a lazy list with elements of type `α`.
In the VM, these are potentially infinite lists
where all elements after the first are computed on-demand.
(This is only useful for execution in the VM,
logically we can prove that `lazy_list α` is isomorphic to `list α`.)
-/


universe u v w

/-- Lazy list.
All elements (except the first) are computed lazily.
-/
inductive LazyList (α : Type u) : Type u
  | nil : LazyList
  | cons (hd : α) (tl : Thunkₓ LazyList) : LazyList

namespace LazyList

variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
  ⟨nil⟩

/-- The singleton lazy list.  -/
def singleton : α → LazyList α
  | a => cons a nil

/-- Constructs a lazy list from a list. -/
def ofList : List α → LazyList α
  | [] => nil
  | h :: t => cons h (of_list t)

/-- Converts a lazy list to a list.
If the lazy list is infinite,
then this function does not terminate.
-/
def toList : LazyList α → List α
  | nil => []
  | cons h t => h :: to_list (t ())

/-- Returns the first element of the lazy list,
or `default` if the lazy list is empty.
-/
def head [Inhabited α] : LazyList α → α
  | nil => default
  | cons h t => h

/-- Removes the first element of the lazy list.
-/
def tail : LazyList α → LazyList α
  | nil => nil
  | cons h t => t ()

/-- Appends two lazy lists.  -/
def append : LazyList α → Thunkₓ (LazyList α) → LazyList α
  | nil, l => l ()
  | cons h t, l => cons h (@append (t ()) l)

/-- Maps a function over a lazy list. -/
def map (f : α → β) : LazyList α → LazyList β
  | nil => nil
  | cons h t => cons (f h) (map (t ()))

/-- Maps a binary function over two lazy list.
Like `lazy_list.zip`, the result is only as long as the smaller input.
-/
def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
  | nil, _ => nil
  | _, nil => nil
  | cons h₁ t₁, cons h₂ t₂ => cons (f h₁ h₂) (map₂ (t₁ ()) (t₂ ()))

/-- Zips two lazy lists. -/
def zip : LazyList α → LazyList β → LazyList (α × β) :=
  map₂ Prod.mk

/-- The monadic join operation for lazy lists. -/
def join : LazyList (LazyList α) → LazyList α
  | nil => nil
  | cons h t => append h (join (t ()))

/-- Maps a function over a lazy list.
Same as `lazy_list.map`, but with swapped arguments.
-/
def for (l : LazyList α) (f : α → β) : LazyList β :=
  map f l

/-- The list containing the first `n` elements of a lazy list.  -/
def approx : Nat → LazyList α → List α
  | 0, l => []
  | _, nil => []
  | a + 1, cons h t => h :: approx a (t ())

/-- The lazy list of all elements satisfying the predicate.
If the lazy list is infinite and none of the elements satisfy the predicate,
then this function will not terminate.
-/
def filter (p : α → Prop) [DecidablePred p] : LazyList α → LazyList α
  | nil => nil
  | cons h t => if p h then cons h (filter (t ())) else filter (t ())

/-- The nth element of a lazy list as an option (like `list.nth`). -/
def nth : LazyList α → Nat → Option α
  | nil, n => none
  | cons a l, 0 => some a
  | cons a l, n + 1 => nth (l ()) n

/-- The infinite lazy list `[x, f x, f (f x), ...]` of iterates of a function.
This definition is meta because it creates an infinite list.
-/
unsafe def iterates (f : α → α) : α → LazyList α
  | x => cons x (iterates (f x))

/-- The infinite lazy list `[i, i+1, i+2, ...]` -/
unsafe def iota (i : Nat) : LazyList Nat :=
  iterates Nat.succ i

end LazyList

