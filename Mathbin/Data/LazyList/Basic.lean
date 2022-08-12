/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathbin.Control.Traversable.Equiv
import Mathbin.Control.Traversable.Instances
import Mathbin.Data.LazyList

/-!
## Definitions on lazy lists

This file contains various definitions and proofs on lazy lists.

TODO: move the `lazy_list.lean` file from core to mathlib.
-/


universe u

namespace Thunkₓ

/-- Creates a thunk with a (non-lazy) constant value. -/
def mk {α} (x : α) : Thunkₓ α := fun _ => x

instance {α : Type u} [DecidableEq α] : DecidableEq (Thunkₓ α)
  | a, b => by
    have : a = b ↔ a () = b () :=
      ⟨by
        cc, by
        intro <;> ext x <;> cases x <;> assumption⟩
    rw [this] <;> infer_instance

end Thunkₓ

namespace LazyList

open Function

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
/-- Isomorphism between strict and lazy lists. -/
def listEquivLazyList (α : Type _) : List α ≃ LazyList α where
  toFun := LazyList.ofList
  invFun := LazyList.toList
  right_inv := by
    intro
    induction x
    rfl
    simp [*]
    ext
    cases x
    rfl
  left_inv := by
    intro
    induction x
    rfl
    simp [*]

instance {α : Type u} [DecidableEq α] : DecidableEq (LazyList α)
  | nil, nil => isTrue rfl
  | cons x xs, cons y ys =>
    if h : x = y then
      match DecidableEq (xs ()) (ys ()) with
      | is_false h2 =>
        isFalse
          (by
            intro <;> cc)
      | is_true h2 =>
        have : xs = ys := by
          ext u <;> cases u <;> assumption
        isTrue
          (by
            cc)
    else
      isFalse
        (by
          intro <;> cc)
  | nil, cons _ _ =>
    isFalse
      (by
        cc)
  | cons _ _, nil =>
    isFalse
      (by
        cc)

/-- Traversal of lazy lists using an applicative effect. -/
protected def traverse {m : Type u → Type u} [Applicativeₓ m] {α β : Type u} (f : α → m β) : LazyList α → m (LazyList β)
  | LazyList.nil => pure LazyList.nil
  | LazyList.cons x xs => LazyList.cons <$> f x <*> Thunkₓ.mk <$> traverse (xs ())

instance : Traversable LazyList where
  map := @LazyList.traverse id _
  traverse := @LazyList.traverse

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
instance : IsLawfulTraversable LazyList := by
  apply Equivₓ.isLawfulTraversable' list_equiv_lazy_list <;> intros <;> skip <;> ext
  · induction x
    rfl
    simp [← Equivₓ.map, ← Functor.map] at *
    simp [*]
    rfl
    
  · induction x
    rfl
    simp [← Equivₓ.map, ← Functor.mapConst] at *
    simp [*]
    rfl
    
  · induction x
    · simp' [← Traversable.traverse, ← Equivₓ.traverse] with functor_norm
      rfl
      
    simp [← Equivₓ.map, ← Functor.mapConst, ← Traversable.traverse] at *
    rw [x_ih]
    dsimp' [← list_equiv_lazy_list, ← Equivₓ.traverse, ← to_list, ← Traversable.traverse, ← List.traverseₓₓ]
    simp' with functor_norm
    rfl
    

/-- `init xs`, if `xs` non-empty, drops the last element of the list.
Otherwise, return the empty list. -/
def init {α} : LazyList α → LazyList α
  | LazyList.nil => LazyList.nil
  | LazyList.cons x xs =>
    let xs' := xs ()
    match xs' with
    | LazyList.nil => LazyList.nil
    | LazyList.cons _ _ => LazyList.cons x (init xs')

/-- Return the first object contained in the list that satisfies
predicate `p` -/
def find {α} (p : α → Prop) [DecidablePred p] : LazyList α → Option α
  | nil => none
  | cons h t => if p h then some h else find (t ())

/-- `interleave xs ys` creates a list where elements of `xs` and `ys` alternate. -/
def interleave {α} : LazyList α → LazyList α → LazyList α
  | LazyList.nil, xs => xs
  | a@(LazyList.cons x xs), LazyList.nil => a
  | LazyList.cons x xs, LazyList.cons y ys => LazyList.cons x (LazyList.cons y (interleave (xs ()) (ys ())))

/-- `interleave_all (xs::ys::zs::xss)` creates a list where elements of `xs`, `ys`
and `zs` and the rest alternate. Every other element of the resulting list is taken from
`xs`, every fourth is taken from `ys`, every eighth is taken from `zs` and so on. -/
def interleaveAll {α} : List (LazyList α) → LazyList α
  | [] => LazyList.nil
  | x :: xs => interleave x (interleave_all xs)

/-- Monadic bind operation for `lazy_list`. -/
protected def bind {α β} : LazyList α → (α → LazyList β) → LazyList β
  | LazyList.nil, _ => LazyList.nil
  | LazyList.cons x xs, f => LazyList.append (f x) (bind (xs ()) f)

/-- Reverse the order of a `lazy_list`.
It is done by converting to a `list` first because reversal involves evaluating all
the list and if the list is all evaluated, `list` is a better representation for
it than a series of thunks. -/
def reverse {α} (xs : LazyList α) : LazyList α :=
  ofList xs.toList.reverse

instance : Monadₓ LazyList where
  pure := @LazyList.singleton
  bind := @LazyList.bind

theorem append_nil {α} (xs : LazyList α) : xs.append LazyList.nil = xs := by
  induction xs
  rfl
  simp [← LazyList.append, ← xs_ih]
  ext
  congr

theorem append_assoc {α} (xs ys zs : LazyList α) : (xs.append ys).append zs = xs.append (ys.append zs) := by
  induction xs <;> simp [← append, *]

theorem append_bind {α β} (xs : LazyList α) (ys : Thunkₓ (LazyList α)) (f : α → LazyList β) :
    (@LazyList.append _ xs ys).bind f = (xs.bind f).append ((ys ()).bind f) := by
  induction xs <;> simp [← LazyList.bind, ← append, *, ← append_assoc, ← append, ← LazyList.bind]

instance : IsLawfulMonad LazyList where
  pure_bind := by
    intros
    apply append_nil
  bind_assoc := by
    intros
    dsimp' [← (· >>= ·)]
    induction x <;> simp [← LazyList.bind, ← append_bind, *]
  id_map := by
    intros
    simp [← (· <$> ·)]
    induction x <;> simp [← LazyList.bind, *, ← singleton, ← append]
    ext ⟨⟩
    rfl

/-- Try applying function `f` to every element of a `lazy_list` and
return the result of the first attempt that succeeds. -/
def mfirstₓ {m} [Alternativeₓ m] {α β} (f : α → m β) : LazyList α → m β
  | nil => failure
  | cons x xs => f x <|> mfirst (xs ())

/-- Membership in lazy lists -/
protected def Mem {α} (x : α) : LazyList α → Prop
  | LazyList.nil => False
  | LazyList.cons y ys => x = y ∨ mem (ys ())

instance {α} : HasMem α (LazyList α) :=
  ⟨LazyList.Mem⟩

instance Mem.decidable {α} [DecidableEq α] (x : α) : ∀ xs : LazyList α, Decidable (x ∈ xs)
  | LazyList.nil => Decidable.false
  | LazyList.cons y ys =>
    if h : x = y then Decidable.isTrue (Or.inl h)
    else
      decidableOfDecidableOfIff (mem.decidable (ys ()))
        (by
          simp [*, ← (· ∈ ·), ← LazyList.Mem])

@[simp]
theorem mem_nil {α} (x : α) : x ∈ @LazyList.nil α ↔ False :=
  Iff.rfl

@[simp]
theorem mem_cons {α} (x y : α) (ys : Thunkₓ (LazyList α)) : x ∈ @LazyList.cons α y ys ↔ x = y ∨ x ∈ ys () :=
  Iff.rfl

theorem forall_mem_cons {α} {p : α → Prop} {a : α} {l : Thunkₓ (LazyList α)} :
    (∀, ∀ x ∈ @LazyList.cons _ a l, ∀, p x) ↔ p a ∧ ∀, ∀ x ∈ l (), ∀, p x := by
  simp only [← HasMem.Mem, ← LazyList.Mem, ← or_imp_distrib, ← forall_and_distrib, ← forall_eq]

/-! ### map for partial functions -/


/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp]
def pmap {α β} {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : LazyList α, (∀, ∀ a ∈ l, ∀, p a) → LazyList β
  | LazyList.nil, H => LazyList.nil
  | LazyList.cons x xs, H => LazyList.cons (f x (forall_mem_cons.1 H).1) (pmap (xs ()) (forall_mem_cons.1 H).2)

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new `lazy_list`
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach {α} (l : LazyList α) : LazyList { x // x ∈ l } :=
  pmap Subtype.mk l fun a => id

instance {α} [HasRepr α] : HasRepr (LazyList α) :=
  ⟨fun xs => reprₓ xs.toList⟩

end LazyList

