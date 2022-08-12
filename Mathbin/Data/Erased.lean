/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Logic.Equiv.Basic

/-!
# A type for VM-erased data

This file defines a type `erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `erased α` is
represented as `0`, just like types and proofs.
-/


universe u

/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def Erased (α : Sort u) : Sort max 1 u :=
  Σ's : α → Prop, ∃ a, (fun b => a = b) = s

namespace Erased

/-- Erase a value. -/
@[inline]
def mk {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- Extracts the erased value, noncomputably. -/
noncomputable def out {α} : Erased α → α
  | ⟨s, h⟩ => Classical.some h

/-- Extracts the erased value, if it is a type.

Note: `(mk a).out_type` is not definitionally equal to `a`.
-/
@[reducible]
def OutType (a : Erased (Sort u)) : Sort u :=
  out a

/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : Erased p) : p :=
  out a

@[simp]
theorem out_mk {α} (a : α) : (mk a).out = a := by
  let h
  show Classical.some h = a
  have := Classical.some_spec h
  exact cast (congr_fun this a).symm rfl

@[simp]
theorem mk_out {α} : ∀ a : Erased α, mk (out a) = a
  | ⟨s, h⟩ => by
    simp [← mk] <;> congr <;> exact Classical.some_spec h

@[ext]
theorem out_inj {α} (a b : Erased α) (h : a.out = b.out) : a = b := by
  simpa using congr_arg mk h

/-- Equivalence between `erased α` and `α`. -/
noncomputable def equiv (α) : Erased α ≃ α :=
  ⟨out, mk, mk_out, out_mk⟩

instance (α : Type u) : HasRepr (Erased α) :=
  ⟨fun _ => "erased"⟩

instance (α : Type u) : HasToString (Erased α) :=
  ⟨fun _ => "erased"⟩

unsafe instance (α : Type u) : has_to_format (Erased α) :=
  ⟨fun _ => ("erased" : format)⟩

/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : Nonempty α) : Erased α :=
  mk (Classical.choice h)

@[simp]
theorem nonempty_iff {α} : Nonempty (Erased α) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => ⟨a.out⟩, fun ⟨a⟩ => ⟨mk a⟩⟩

instance {α} [h : Nonempty α] : Inhabited (Erased α) :=
  ⟨choice h⟩

/-- `(>>=)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `monad`).
-/
def bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.out).1 b, (f a.out).2⟩

@[simp]
theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out := by
  delta' bind bind._proof_1 <;> cases f a.out <;> rfl

/-- Collapses two levels of erasure.
-/
def join {α} (a : Erased (Erased α)) : Erased α :=
  bind a id

@[simp]
theorem join_eq_out {α} (a) : @join α a = a.out :=
  bind_eq_out _ _

/-- `(<$>)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `functor`).
-/
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  bind a (mk ∘ f)

@[simp]
theorem map_out {α β} {f : α → β} (a : Erased α) : (a.map f).out = f a.out := by
  simp [← map]

instance : Monadₓ Erased where
  pure := @mk
  bind := @bind
  map := @map

@[simp]
theorem pure_def {α} : (pure : α → Erased α) = @mk _ :=
  rfl

@[simp]
theorem bind_def {α β} : ((· >>= ·) : Erased α → (α → Erased β) → Erased β) = @bind _ _ :=
  rfl

@[simp]
theorem map_def {α β} : ((· <$> ·) : (α → β) → Erased α → Erased β) = @map _ _ :=
  rfl

instance : IsLawfulMonad Erased := by
  refine' { .. } <;> intros <;> ext <;> simp

end Erased

