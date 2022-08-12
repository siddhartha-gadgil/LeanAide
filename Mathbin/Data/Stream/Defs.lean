/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!
# Definition of `stream` and functions on streams

A stream `stream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `stream` and some functions that take and/or return streams.
-/


universe u v w

/-- A stream `stream α` is an infinite sequence of elements of `α`. -/
def Streamₓ (α : Type u) :=
  Nat → α

open Nat

namespace Streamₓ

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Prepend an element to a stream. -/
def cons (a : α) (s : Streamₓ α) : Streamₓ α := fun i =>
  match i with
  | 0 => a
  | succ n => s n

/-- Head of a stream: `stream.head s = stream.nth 0 s`. -/
def head (s : Streamₓ α) : α :=
  s 0

/-- Tail of a stream: `stream.tail (h :: t) = t`. -/
def tail (s : Streamₓ α) : Streamₓ α := fun i => s (i + 1)

/-- Drop first `n` elements of a stream. -/
def drop (n : Nat) (s : Streamₓ α) : Streamₓ α := fun i => s (i + n)

/-- `n`-th element of a stream. -/
def nth (s : Streamₓ α) (n : ℕ) : α :=
  s n

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Streamₓ α) :=
  ∀ n, p (nth s n)

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Streamₓ α) :=
  ∃ n, p (nth s n)

/-- `a ∈ s` means that `a = stream.nth n s` for some `n`. -/
instance : HasMem α (Streamₓ α) :=
  ⟨fun a s => Any (fun b => a = b) s⟩

/-- Apply a function `f` to all elements of a stream `s`. -/
def map (f : α → β) (s : Streamₓ α) : Streamₓ β := fun n => f (nth s n)

/-- Zip two streams using a binary operation:
`stream.nth n (stream.zip f s₁ s₂) = f (stream.nth s₁) (stream.nth s₂)`. -/
def zip (f : α → β → δ) (s₁ : Streamₓ α) (s₂ : Streamₓ β) : Streamₓ δ := fun n => f (nth s₁ n) (nth s₂ n)

/-- The constant stream: `stream.nth n (stream.const a) = a`. -/
def const (a : α) : Streamₓ α := fun n => a

/-- Iterates of a function as a stream. -/
def iterate (f : α → α) (a : α) : Streamₓ α := fun n => Nat.recOn n a fun n r => f r

def corec (f : α → β) (g : α → α) : α → Streamₓ β := fun a => map f (iterate g a)

def corecOn (a : α) (f : α → β) (g : α → α) : Streamₓ β :=
  corec f g a

def corec' (f : α → β × α) : α → Streamₓ β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : State σ α) (s : σ) : Streamₓ α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfold
def unfolds (g : α → β) (f : α → α) (a : α) : Streamₓ β :=
  corec g f a

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Streamₓ α) : Streamₓ α :=
  corecOn (s₁, s₂) (fun ⟨s₁, s₂⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

-- mathport name: «expr ⋈ »
infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even (s : Streamₓ α) : Streamₓ α :=
  corec (fun s => head s) (fun s => tail (tail s)) s

/-- Elements of a stream with odd indices. -/
def odd (s : Streamₓ α) : Streamₓ α :=
  even (tail s)

/-- Append a stream to a list. -/
def appendStream : List α → Streamₓ α → Streamₓ α
  | [], s => s
  | List.cons a l, s => a :: append_stream l s

-- mathport name: «expr ++ₛ »
infixl:65 " ++ₛ " => appendStream

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Streamₓ α → List α
  | 0, s => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v

/-- An auxiliary definition for `stream.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (v₁, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (v₁, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Streamₓ α
  | [], h => absurd rfl h
  | List.cons a l, h => corec Streamₓ.cycleF Streamₓ.cycleG (a, l, a, l)

/-- Tails of a stream, starting with `stream.tail s`. -/
def tails (s : Streamₓ α) : Streamₓ (Streamₓ α) :=
  corec id tail (tail s)

/-- An auxiliary definition for `stream.inits`. -/
def initsCore (l : List α) (s : Streamₓ α) : Streamₓ (List α) :=
  corecOn (l, s) (fun ⟨a, b⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/-- Nonempty initial segments of a stream. -/
def inits (s : Streamₓ α) : Streamₓ (List α) :=
  initsCore [head s] (tail s)

/-- A constant stream, same as `stream.const`. -/
def pure (a : α) : Streamₓ α :=
  const a

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Streamₓ (α → β)) (s : Streamₓ α) : Streamₓ β := fun n => (nth f n) (nth s n)

-- mathport name: «expr ⊛ »
infixl:75 " ⊛ " => apply

/-- The stream of natural numbers: `stream.nth n stream.nats = n`. -/
-- input as \o*
def nats : Streamₓ Nat := fun n => n

end Streamₓ

