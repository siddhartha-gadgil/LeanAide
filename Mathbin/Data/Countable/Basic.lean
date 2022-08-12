/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Logic.Equiv.Nat
import Mathbin.Logic.Equiv.Fin
import Mathbin.Data.Countable.Defs

/-!
# Countable types

In this file we provide basic instances of the `countable` typeclass defined elsewhere.
-/


universe u v w

open Function

instance : Countable ℤ :=
  Countable.of_equiv ℕ Equivₓ.intEquivNat.symm

/-!
### Definition in terms of `function.embedding`
-/


section Embedding

variable {α : Sort u} {β : Sort v}

theorem countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ ℕ) :=
  ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩

theorem nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ ℕ) :=
  countable_iff_nonempty_embedding.1 ‹_›

protected theorem Function.Embedding.countable [Countable β] (f : α ↪ β) : Countable α :=
  f.Injective.Countable

end Embedding

/-!
### Operations on `Type*`s
-/


section Type

variable {α : Type u} {β : Type v} {π : α → Type w}

instance [Countable α] [Countable β] : Countable (Sum α β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (equiv.nat_sum_nat_equiv_nat.injective.comp <| hf.sum_map hg).Countable

instance [Countable α] : Countable (Option α) :=
  Countable.of_equiv _ (Equivₓ.optionEquivSumPunit α).symm

instance [Countable α] [Countable β] : Countable (α × β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (equiv.nat_prod_nat_equiv_nat.injective.comp <| hf.prod_map hg).Countable

instance [Countable α] [∀ a, Countable (π a)] : Countable (Sigma π) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  choose g hg using fun a => exists_injective_nat (π a)
  exact ((Equivₓ.sigmaEquivProd ℕ ℕ).Injective.comp <| hf.sigma_map hg).Countable

end Type

section Sort

variable {α : Sort u} {β : Sort v} {π : α → Sort w}

/-!
### Operations on and `Sort*`s
-/


instance (priority := 500) SetCoe.countable {α} [Countable α] (s : Set α) : Countable s :=
  Subtype.countable

instance [Countable α] [Countable β] : Countable (PSum α β) :=
  Countable.of_equiv (Sum (Plift α) (Plift β)) (Equivₓ.plift.sumPsum Equivₓ.plift)

instance [Countable α] [Countable β] : Countable (PProd α β) :=
  Countable.of_equiv (Plift α × Plift β) (Equivₓ.plift.prodPprod Equivₓ.plift)

instance [Countable α] [∀ a, Countable (π a)] : Countable (PSigma π) :=
  Countable.of_equiv (Σa : Plift α, Plift (π a.down)) (Equivₓ.psigmaEquivSigmaPlift π).symm

instance [Finite α] [∀ a, Countable (π a)] : Countable (∀ a, π a) := by
  have : ∀ n, Countable (Finₓ n → ℕ) := by
    intro n
    induction' n with n ihn
    · infer_instance
      
    · exact Countable.of_equiv _ (Equivₓ.piFinSucc _ _).symm
      
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  have f := fun a => (nonempty_embedding_nat (π a)).some
  exact ((embedding.Pi_congr_right f).trans (Equivₓ.piCongrLeft' _ e).toEmbedding).Countable

end Sort

