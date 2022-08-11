/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Logic.Equiv.Basic

/-!
# Extra lemmas about `ulift` and `plift`

In this file we provide `subsingleton`, `unique`, `decidable_eq`, and `is_empty` instances for
`ulift α` and `plift α`. We also prove `ulift.forall`, `ulift.exists`, `plift.forall`, and
`plift.exists`.
-/


universe u v

open Function

namespace Plift

variable {α : Sort u} {β : Sort v}

instance [Subsingleton α] : Subsingleton (Plift α) :=
  Equivₓ.plift.Subsingleton

instance [Nonempty α] : Nonempty (Plift α) :=
  Equivₓ.plift.Nonempty

instance [Unique α] : Unique (Plift α) :=
  Equivₓ.plift.unique

instance [DecidableEq α] : DecidableEq (Plift α) :=
  Equivₓ.plift.DecidableEq

instance [IsEmpty α] : IsEmpty (Plift α) :=
  Equivₓ.plift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equivₓ.plift.symm.Injective

theorem up_surjective : Surjective (@up α) :=
  Equivₓ.plift.symm.Surjective

theorem up_bijective : Bijective (@up α) :=
  Equivₓ.plift.symm.Bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff

theorem down_surjective : Surjective (@down α) :=
  Equivₓ.plift.Surjective

theorem down_bijective : Bijective (@down α) :=
  Equivₓ.plift.Bijective

@[simp]
theorem forall {p : Plift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (Plift.up x) :=
  up_surjective.forall

@[simp]
theorem exists {p : Plift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (Plift.up x) :=
  up_surjective.exists

end Plift

namespace ULift

variable {α : Type u} {β : Type v}

instance [Subsingleton α] : Subsingleton (ULift α) :=
  Equivₓ.ulift.Subsingleton

instance [Nonempty α] : Nonempty (ULift α) :=
  Equivₓ.ulift.Nonempty

instance [Unique α] : Unique (ULift α) :=
  Equivₓ.ulift.unique

instance [DecidableEq α] : DecidableEq (ULift α) :=
  Equivₓ.ulift.DecidableEq

instance [IsEmpty α] : IsEmpty (ULift α) :=
  Equivₓ.ulift.isEmpty

theorem up_injective : Injective (@up α) :=
  Equivₓ.ulift.symm.Injective

theorem up_surjective : Surjective (@up α) :=
  Equivₓ.ulift.symm.Surjective

theorem up_bijective : Bijective (@up α) :=
  Equivₓ.ulift.symm.Bijective

@[simp]
theorem up_inj {x y : α} : up x = up y ↔ x = y :=
  up_injective.eq_iff

theorem down_surjective : Surjective (@down α) :=
  Equivₓ.ulift.Surjective

theorem down_bijective : Bijective (@down α) :=
  Equivₓ.ulift.Bijective

@[simp]
theorem forall {p : ULift α → Prop} : (∀ x, p x) ↔ ∀ x : α, p (ULift.up x) :=
  up_surjective.forall

@[simp]
theorem exists {p : ULift α → Prop} : (∃ x, p x) ↔ ∃ x : α, p (ULift.up x) :=
  up_surjective.exists

end ULift

