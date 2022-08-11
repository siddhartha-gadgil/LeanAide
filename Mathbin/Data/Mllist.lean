/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Keeley Hoek, Simon Hudon, Scott Morrison
-/
import Mathbin.Data.Option.Defs

/-! # Monadic lazy lists.

An alternative construction of lazy lists (see also `data.lazy_list`),
with "lazyness" controlled by an arbitrary monad.

The inductive construction is not allowed outside of meta (indeed, we can build infinite objects).
This isn't so bad, as the typical use is with the tactic monad, in any case.

As we're in meta anyway, we don't bother with proofs about these constructions.
-/


universe u v

namespace Tactic

/-- A monadic lazy list, controlled by an arbitrary monad. -/
-- We hide this away in the tactic namespace, just because it's all meta.
unsafe inductive mllist (m : Type u → Type u) (α : Type u) : Type u
  | nil : mllist
  | cons : m (Option α × mllist) → mllist

namespace Mllist

variable {α β : Type u} {m : Type u → Type u}

/-- Construct an `mllist` recursively. -/
unsafe def fix [Alternativeₓ m] (f : α → m α) : α → mllist m α
  | x => cons <| (fun a => (some x, fix a)) <$> f x <|> pure (some x, nil)

variable [Monadₓ m]

/-- Repeatedly apply a function `f : α → m (α × list β)` to an initial `a : α`,
accumulating the elements of the resulting `list β` as a single monadic lazy list.

(This variant allows starting with a specified `list β` of elements, as well. )-/
unsafe def fixl_with [Alternativeₓ m] (f : α → m (α × List β)) : α → List β → mllist m β
  | s, b :: rest => cons <| pure (some b, fixl_with s rest)
  | s, [] =>
    cons <|
      (do
          let (s', l) ← f s
          match l with
            | b :: rest => pure (some b, fixl_with s' rest)
            | [] => pure (none, fixl_with s' [])) <|>
        pure (none, nil)

/-- Repeatedly apply a function `f : α → m (α × list β)` to an initial `a : α`,
accumulating the elements of the resulting `list β` as a single monadic lazy list. -/
unsafe def fixl [Alternativeₓ m] (f : α → m (α × List β)) (s : α) : mllist m β :=
  fixl_with f s []

/-- Deconstruct an `mllist`, returning inside the monad an optional pair `α × mllist m α`
representing the head and tail of the list. -/
unsafe def uncons {α : Type u} : mllist m α → m (Option (α × mllist m α))
  | nil => pure none
  | cons l => do
    let (x, xs) ← l
    let some x ← return x | uncons xs
    return (x, xs)

/-- Compute, inside the monad, whether an `mllist` is empty. -/
unsafe def empty {α : Type u} (xs : mllist m α) : m (ULift Bool) :=
  (ULift.up ∘ Option.isSome) <$> uncons xs

/-- Convert a `list` to an `mllist`. -/
unsafe def of_list {α : Type u} : List α → mllist m α
  | [] => nil
  | h :: t => cons (pure (h, of_list t))

/-- Convert a `list` of values inside the monad into an `mllist`. -/
unsafe def m_of_list {α : Type u} : List (m α) → mllist m α
  | [] => nil
  | h :: t => cons ((fun x => (x, m_of_list t)) <$> some <$> h)

/-- Extract a list inside the monad from an `mllist`. -/
unsafe def force {α} : mllist m α → m (List α)
  | nil => pure []
  | cons l => do
    let (x, xs) ← l
    let some x ← pure x | force xs
    (· :: ·) x <$> force xs

/-- Take the first `n` elements, as a list inside the monad. -/
unsafe def take {α} : mllist m α → ℕ → m (List α)
  | nil, _ => pure []
  | _, 0 => pure []
  | cons l, n + 1 => do
    let (x, xs) ← l
    let some x ← pure x | take xs (n + 1)
    (· :: ·) x <$> take xs n

/-- Apply a function to every element of an `mllist`. -/
unsafe def map {α β : Type u} (f : α → β) : mllist m α → mllist m β
  | nil => nil
  | cons l =>
    cons <| do
      let (x, xs) ← l
      pure (f <$> x, map xs)

/-- Apply a function which returns values in the monad to every element of an `mllist`. -/
unsafe def mmap {α β : Type u} (f : α → m β) : mllist m α → mllist m β
  | nil => nil
  | cons l =>
    cons <| do
      let (x, xs) ← l
      let b ← x.traverse f
      return (b, mmap xs)

/-- Filter a `mllist`. -/
unsafe def filter {α : Type u} (p : α → Prop) [DecidablePred p] : mllist m α → mllist m α
  | nil => nil
  | cons l =>
    cons <| do
      let (a, r) ← l
      let some a ← return a | return (none, filter r)
      return (if p a then some a else none, filter r)

/-- Filter a `mllist` using a function which returns values in the (alternative) monad.
Whenever the function "succeeds", we accept the element, and reject otherwise. -/
unsafe def mfilter [Alternativeₓ m] {α β : Type u} (p : α → m β) : mllist m α → mllist m α
  | nil => nil
  | cons l =>
    cons <| do
      let (a, r) ← l
      let some a ← return a | return (none, mfilter r)
      p a >> return (a, mfilter r) <|> return (none, mfilter r)

/-- Filter and transform a `mllist` using an `option` valued function. -/
unsafe def filter_map {α β : Type u} (f : α → Option β) : mllist m α → mllist m β
  | nil => nil
  | cons l =>
    cons <| do
      let (a, r) ← l
      let some a ← return a | return (none, filter_map r)
      match f a with
        | some b => return (some b, filter_map r)
        | none => return (none, filter_map r)

/-- Filter and transform a `mllist` using a function that returns values inside the monad.
We discard elements where the function fails. -/
unsafe def mfilter_map [Alternativeₓ m] {α β : Type u} (f : α → m β) : mllist m α → mllist m β
  | nil => nil
  | cons l =>
    cons <| do
      let (a, r) ← l
      let some a ← return a | return (none, mfilter_map r)
      (f a >>= fun b => return (some b, mfilter_map r)) <|> return (none, mfilter_map r)

/-- Concatenate two monadic lazty lists. -/
unsafe def append {α : Type u} : mllist m α → mllist m α → mllist m α
  | nil, ys => ys
  | cons xs, ys =>
    cons <| do
      let (x, xs) ← xs
      return (x, append xs ys)

/-- Join a monadic lazy list of monadic lazy lists into a single monadic lazy list. -/
unsafe def join {α : Type u} : mllist m (mllist m α) → mllist m α
  | nil => nil
  | cons l =>
    cons <| do
      let (xs, r) ← l
      let some xs ← return xs | return (none, join r)
      match xs with
        | nil => return (none, join r)
        | cons m => do
          let (a, n) ← m
          return (a, join (cons <| return (n, r)))

/-- Lift a monadic lazy list inside the monad to a monadic lazy list. -/
unsafe def squash {α} (t : m (mllist m α)) : mllist m α :=
  (mllist.m_of_list [t]).join

/-- Enumerate the elements of a monadic lazy list, starting at a specified offset. -/
unsafe def enum_from {α : Type u} : ℕ → mllist m α → mllist m (ℕ × α)
  | _, nil => nil
  | n, cons l =>
    cons <| do
      let (a, r) ← l
      let some a ← return a | return (none, enum_from n r)
      return ((n, a), enum_from (n + 1) r)

/-- Enumerate the elements of a monadic lazy list. -/
unsafe def enum {α : Type u} : mllist m α → mllist m (ℕ × α) :=
  enum_from 0

/-- The infinite monadic lazy list of natural numbers.-/
unsafe def range {m : Type → Type} [Alternativeₓ m] : mllist m ℕ :=
  mllist.fix (fun n => pure (n + 1)) 0

/-- Add one element to the end of a monadic lazy list. -/
unsafe def concat {α : Type u} : mllist m α → α → mllist m α
  | L, a => (mllist.of_list [L, mllist.of_list [a]]).join

/-- Apply a function returning a monadic lazy list to each element of a monadic lazy list,
joining the results. -/
unsafe def bind_ {α β : Type u} : mllist m α → (α → mllist m β) → mllist m β
  | nil, f => nil
  | cons ll, f =>
    cons <| do
      let (x, xs) ← ll
      let some x ← return x | return (none, bind_ xs f)
      return (none, append (f x) (bind_ xs f))

/-- Convert any value in the monad to the singleton monadic lazy list. -/
unsafe def monad_lift {α} (x : m α) : mllist m α :=
  cons <| (flip Prod.mk nil ∘ some) <$> x

/-- Return the head of a monadic lazy list, as a value in the monad. -/
unsafe def head [Alternativeₓ m] {α} (L : mllist m α) : m α := do
  let some (r, _) ← L.uncons | failure
  return r

/-- Apply a function returning values inside the monad to a monadic lazy list,
returning only the first successful result. -/
unsafe def mfirst [Alternativeₓ m] {α β} (L : mllist m α) (f : α → m β) : m β :=
  (L.mfilter_map f).head

end Mllist

end Tactic

