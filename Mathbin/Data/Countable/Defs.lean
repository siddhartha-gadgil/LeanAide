/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Finite.Defs

/-!
# Countable types

In this file we define a typeclass saying that a given `Sort*` is countable. See also `encodable`
for a version that singles out a specific encoding of elements of `α` by natural numbers.

This file also provides a few instances of this typeclass. More instances can be found in other
files.
-/


open Function

universe u v

variable {α : Sort u} {β : Sort v}

/-!
### Definition and basic properties
-/


-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`exists_injective_nat] []
/-- A type `α` is countable if there exists an injective map `α → ℕ`. -/
@[mk_iff countable_iff_exists_injective]
class Countable (α : Sort u) : Prop where
  exists_injective_nat : ∃ f : α → ℕ, Injective f

instance : Countable ℕ :=
  ⟨⟨id, injective_id⟩⟩

export Countable (exists_injective_nat)

protected theorem Function.Injective.countable [Countable β] {f : α → β} (hf : Injective f) : Countable α :=
  let ⟨g, hg⟩ := exists_injective_nat β
  ⟨⟨g ∘ f, hg.comp hf⟩⟩

protected theorem Function.Surjective.countable [Countable α] {f : α → β} (hf : Surjective f) : Countable β :=
  (injective_surj_inv hf).Countable

theorem exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f :=
  let ⟨f, hf⟩ := exists_injective_nat α
  ⟨invFun f, inv_fun_surjectiveₓ hf⟩

theorem countable_iff_exists_surjective [Nonempty α] : Countable α ↔ ∃ f : ℕ → α, Surjective f :=
  ⟨@exists_surjective_nat _ _, fun ⟨f, hf⟩ => hf.Countable⟩

theorem Countable.of_equiv (α : Sort _) [Countable α] (e : α ≃ β) : Countable β :=
  e.symm.Injective.Countable

theorem Equivₓ.countable_iff (e : α ≃ β) : Countable α ↔ Countable β :=
  ⟨fun h => @Countable.of_equiv _ _ h e, fun h => @Countable.of_equiv _ _ h e.symm⟩

instance {β : Type v} [Countable β] : Countable (ULift.{u} β) :=
  Countable.of_equiv _ Equivₓ.ulift.symm

/-!
### Operations on `Sort*`s
-/


instance [Countable α] : Countable (Plift α) :=
  Equivₓ.plift.Injective.Countable

instance (priority := 100) Subsingleton.to_countable [Subsingleton α] : Countable α :=
  ⟨⟨fun _ => 0, fun x y h => Subsingleton.elimₓ x y⟩⟩

instance (priority := 500) [Countable α] {p : α → Prop} : Countable { x // p x } :=
  Subtype.val_injective.Countable

instance {n : ℕ} : Countable (Finₓ n) :=
  Subtype.countable

instance (priority := 100) Finite.to_countable [Finite α] : Countable α :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  Countable.of_equiv _ e.symm

instance : Countable PUnit.{u} :=
  Subsingleton.to_countable

@[nolint instance_priority]
instance Prop.countable (p : Prop) : Countable p :=
  Subsingleton.to_countable

instance Bool.countable : Countable Bool :=
  ⟨⟨fun b => cond b 0 1, Bool.injective_iff.2 Nat.one_ne_zero⟩⟩

instance Prop.countable' : Countable Prop :=
  Countable.of_equiv Bool Equivₓ.propEquivBool.symm

instance (priority := 500) [Countable α] {r : α → α → Prop} : Countable (Quot r) :=
  (surjective_quot_mk r).Countable

instance (priority := 500) [Countable α] {s : Setoidₓ α} : Countable (Quotientₓ s) :=
  Quot.countable

