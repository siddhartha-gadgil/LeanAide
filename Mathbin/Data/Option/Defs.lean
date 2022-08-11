/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

/-!
# Extra definitions on `option`

This file defines more operations involving `option α`. Lemmas about them are located in other
files under `data.option.`.
Other basic operations on `option` are defined in the core library.
-/


namespace Option

variable {α : Type _} {β : Type _}

attribute [inline] Option.isSome Option.isNone

/-- An elimination principle for `option`. It is a nondependent version of `option.rec`. -/
@[simp]
protected def elimₓ (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

instance hasMem : HasMem α (Option α) :=
  ⟨fun a b => b = some a⟩

@[simp]
theorem mem_def {a : α} {b : Option α} : a ∈ b ↔ b = some a :=
  Iff.rfl

theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = a :=
  Iff.rfl

theorem is_none_iff_eq_none {o : Option α} : o.isNone = tt ↔ o = none :=
  ⟨Option.eq_none_of_is_none, fun e => e.symm ▸ rfl⟩

theorem some_inj {a b : α} : some a = some b ↔ a = b := by
  simp

theorem mem_some_iff {α : Type _} {a b : α} : a ∈ some b ↔ b = a := by
  simp

/-- `o = none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to `option.decidable_eq`.
Try to use `o.is_none` or `o.is_some` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidableOfDecidableOfIff (Bool.decidableEq _ _) is_none_iff_eq_none

instance decidableForallMem {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∀, ∀ a ∈ o, ∀, p a)
  | none =>
    isTrue
      (by
        simp [← false_implies_iff])
  | some a => if h : p a then is_true fun o e => some_inj.1 e ▸ h else is_false <| mt (fun H => H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none =>
    isFalse fun ⟨a, ⟨h, _⟩⟩ => by
      cases h
  | some a => if h : p a then is_true <| ⟨_, rfl, h⟩ else is_false fun ⟨_, ⟨rfl, hn⟩⟩ => h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

@[simp]
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none

/-- `filter p o` returns `some a` if `o` is `some a` and `p a` holds, otherwise `none`. -/
def filterₓ (p : α → Prop) [DecidablePred p] (o : Option α) : Option α :=
  o.bind (guard p)

/-- Cast of `option` to `list `. Returns `[a]` if the input is `some a`, and `[]` if it is
`none`. -/
def toList : Option α → List α
  | none => []
  | some a => [a]

@[simp]
theorem mem_to_list {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [← to_list, ← eq_comm]

/-- Two arguments failsafe function. Returns `f a b` if the inputs are `some a` and `some b`, and
"does nothing" otherwise. -/
def liftOrGet (f : α → α → α) : Option α → Option α → Option α
  | none, none => none
  | some a, none => some a
  |-- get a
    none,
    some b => some b
  |-- get b
      some
      a,
    some b => some (f a b)

-- lift f
instance lift_or_get_comm (f : α → α → α) [h : IsCommutative α f] : IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b => by
    cases a <;> cases b <;> simp [← lift_or_get, ← h.comm]⟩

instance lift_or_get_assoc (f : α → α → α) [h : IsAssociative α f] : IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c => by
    cases a <;> cases b <;> cases c <;> simp [← lift_or_get, ← h.assoc]⟩

instance lift_or_get_idem (f : α → α → α) [h : IsIdempotent α f] : IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a => by
    cases a <;> simp [← lift_or_get, ← h.idempotent]⟩

instance lift_or_get_is_left_id (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a => by
    cases a <;> simp [← lift_or_get]⟩

instance lift_or_get_is_right_id (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a => by
    cases a <;> simp [← lift_or_get]⟩

/-- Lifts a relation `α → β → Prop` to a relation `option α → option β → Prop` by just adding
`none ~ none`. -/
inductive Rel (r : α → β → Prop) : Option α → Option β → Prop
  | /-- If `a ~ b`, then `some a ~ some b` -/
  some {a b} : r a b → rel (some a) (some b)
  | /-- `none ~ none` -/
  none : rel none none

/-- Partial bind. If for some `x : option α`, `f : Π (a : α), a ∈ x → option β` is a
  partial function defined on `a : α` giving an `option β`, where `some a = x`,
  then `pbind x f h` is essentially the same as `bind x f`
  but is defined only when all `x = some a`, using the proof to apply `f`. -/
@[simp]
def pbind : ∀ x : Option α, (∀ a : α, a ∈ x → Option β) → Option β
  | none, _ => none
  | some a, f => f a rfl

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f x h` is essentially the same as `map f x` but is defined only when all members of `x`
satisfy `p`, using the proof to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a : α, p a → β) : ∀ x : Option α, (∀, ∀ a ∈ x, ∀, p a) → Option β
  | none, _ => none
  | some a, H => some (f a (H a (mem_def.mpr rfl)))

/-- Flatten an `option` of `option`, a specialization of `mjoin`. -/
@[simp]
def join : Option (Option α) → Option α := fun x => bind x id

protected def traverseₓₓ.{u, v} {F : Type u → Type v} [Applicativeₓ F] {α β : Type _} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x

/-- If you maybe have a monadic computation in a `[monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
-- By analogy with `monad.sequence` in `init/category/combinators.lean`.
def maybeₓ.{u, v} {m : Type u → Type v} [Monadₓ m] {α : Type u} : Option (m α) → m (Option α)
  | none => return none
  | some fn => some <$> fn

/-- Map a monadic function `f : α → m β` over an `o : option α`, maybe producing a result. -/
def mmapₓ.{u, v, w} {m : Type u → Type v} [Monadₓ m] {α : Type w} {β : Type u} (f : α → m β) (o : Option α) :
    m (Option β) :=
  (o.map f).maybe

/-- A monadic analogue of `option.elim`. -/
def melimₓ {α β : Type _} {m : Type _ → Type _} [Monadₓ m] (y : m β) (z : α → m β) (x : m (Option α)) : m β :=
  x >>= Option.elimₓ y z

/-- A monadic analogue of `option.get_or_else`. -/
def mgetOrElse {α : Type _} {m : Type _ → Type _} [Monadₓ m] (x : m (Option α)) (y : m α) : m α :=
  melimₓ y pure x

end Option

