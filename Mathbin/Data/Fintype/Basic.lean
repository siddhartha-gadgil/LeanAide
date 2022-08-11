/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Array.Lemmas
import Mathbin.Data.Finset.Fin
import Mathbin.Data.Finset.Option
import Mathbin.Data.Finset.Pi
import Mathbin.Data.Finset.Powerset
import Mathbin.Data.Finset.Prod
import Mathbin.Data.Finset.Sigma
import Mathbin.Data.List.NodupEquivFin
import Mathbin.Data.Sym.Basic
import Mathbin.Data.Ulift
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.Order.WellFounded
import Mathbin.Tactic.Wlog

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `fintype α`:  Typeclass saying that a type is finite. It takes as fields a `finset` and a proof
  that all terms of type `α` are in it.
* `finset.univ`: The finset of all elements of a fintype.
* `fintype.card α`: Cardinality of a fintype. Equal to `finset.univ.card`.
* `perms_of_finset s`: The finset of permutations of the finset `s`.
* `fintype.trunc_equiv_fin`: A fintype `α` is computably equivalent to `fin (card α)`. The
  `trunc`-free, noncomputable version is `fintype.equiv_fin`.
* `fintype.trunc_equiv_of_card_eq` `fintype.equiv_of_card_eq`: Two fintypes of same cardinality are
  equivalent. See above.
* `fin.equiv_iff_eq`: `fin m ≃ fin n` iff `m = n`.
* `infinite α`: Typeclass saying that a type is infinite. Defined as `fintype α → false`.
* `not_fintype`: No `fintype` has an `infinite` instance.
* `infinite.nat_embedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `fintype.exists_ne_map_eq_of_card_lt` and `is_empty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `fintype.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `fintype.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `data.fintype.card_embedding`.

## Instances

Among others, we provide `fintype` instances for
* A `subtype` of a fintype. See `fintype.subtype`.
* The `option` of a fintype.
* The product of two fintypes.
* The sum of two fintypes.
* `Prop`.

and `infinite` instances for
* specific types: `ℕ`, `ℤ`
* type constructors: `set α`, `finset α`, `multiset α`, `list α`, `α ⊕ β`, `α × β`

along with some machinery
* Types which have a surjection from/an injection to a `fintype` are themselves fintypes. See
  `fintype.of_injective` and `fintype.of_surjective`.
* Types which have an injection from/a surjection to an `infinite` type are themselves `infinite`.
  See `infinite.of_injective` and `infinite.of_surjective`.
-/


open Function

open Nat

universe u v

variable {α β γ : Type _}

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`elems] []
/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class Fintype (α : Type _) where
  elems : Finset α
  complete : ∀ x : α, x ∈ elems

namespace Finset

variable [Fintype α] {s : Finset α}

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : Finset α :=
  Fintype.elems α

@[simp]
theorem mem_univ (x : α) : x ∈ (univ : Finset α) :=
  Fintype.complete x

@[simp]
theorem mem_univ_val : ∀ x, x ∈ (univ : Finset α).1 :=
  mem_univ

theorem eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s := by
  simp [← ext_iff]

theorem eq_univ_of_forall : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2

@[simp, norm_cast]
theorem coe_univ : ↑(univ : Finset α) = (Set.Univ : Set α) := by
  ext <;> simp

@[simp, norm_cast]
theorem coe_eq_univ : (s : Set α) = Set.Univ ↔ s = univ := by
  rw [← coe_univ, coe_inj]

theorem univ_nonempty_iff : (univ : Finset α).Nonempty ↔ Nonempty α := by
  rw [← coe_nonempty, coe_univ, Set.nonempty_iff_univ_nonempty]

theorem univ_nonempty [Nonempty α] : (univ : Finset α).Nonempty :=
  univ_nonempty_iff.2 ‹_›

theorem univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ IsEmpty α := by
  rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]

@[simp]
theorem univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅ :=
  univ_eq_empty_iff.2 ‹_›

@[simp]
theorem univ_unique [Unique α] : (univ : Finset α) = {default} :=
  Finset.ext fun x => iff_of_true (mem_univ _) <| mem_singleton.2 <| Subsingleton.elimₓ x default

@[simp]
theorem subset_univ (s : Finset α) : s ⊆ univ := fun a _ => mem_univ a

instance : OrderTop (Finset α) where
  top := univ
  le_top := subset_univ

section BooleanAlgebra

variable [DecidableEq α] {a : α}

instance : BooleanAlgebra (Finset α) :=
  { Finset.orderTop, Finset.orderBot, Finset.generalizedBooleanAlgebra with compl := fun s => univ \ s,
    inf_compl_le_bot := fun s x hx => by
      simpa using hx,
    top_le_sup_compl := fun s x hx => by
      simp ,
    sdiff_eq := fun s t => by
      simp [← ext_iff, ← compl] }

theorem compl_eq_univ_sdiff (s : Finset α) : sᶜ = univ \ s :=
  rfl

@[simp]
theorem mem_compl : a ∈ sᶜ ↔ a ∉ s := by
  simp [← compl_eq_univ_sdiff]

theorem not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by
  rw [mem_compl, not_not]

@[simp, norm_cast]
theorem coe_compl (s : Finset α) : ↑(sᶜ) = (↑s : Set α)ᶜ :=
  Set.ext fun x => mem_compl

@[simp]
theorem compl_empty : (∅ : Finset α)ᶜ = univ :=
  compl_bot

@[simp]
theorem union_compl (s : Finset α) : s ∪ sᶜ = univ :=
  sup_compl_eq_top

@[simp]
theorem inter_compl (s : Finset α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot

@[simp]
theorem compl_union (s t : Finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup

@[simp]
theorem compl_inter (s t : Finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf

@[simp]
theorem compl_erase : s.erase aᶜ = insert a (sᶜ) := by
  ext
  simp only [← or_iff_not_imp_left, ← mem_insert, ← not_and, ← mem_compl, ← mem_erase]

@[simp]
theorem compl_insert : insert a sᶜ = sᶜ.erase a := by
  ext
  simp only [← not_or_distrib, ← mem_insert, ← iff_selfₓ, ← mem_compl, ← mem_erase]

@[simp]
theorem insert_compl_self (x : α) : insert x ({x}ᶜ : Finset α) = univ := by
  rw [← compl_erase, erase_singleton, compl_empty]

@[simp]
theorem compl_filter (p : α → Prop) [DecidablePred p] [∀ x, Decidable ¬p x] :
    univ.filter pᶜ = univ.filter fun x => ¬p x :=
  (filter_not _ _).symm

theorem compl_ne_univ_iff_nonempty (s : Finset α) : sᶜ ≠ univ ↔ s.Nonempty := by
  simp [← eq_univ_iff_forall, ← Finset.Nonempty]

theorem compl_singleton (a : α) : ({a} : Finset α)ᶜ = univ.erase a := by
  rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]

theorem insert_inj_on' (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ : Finset α) := by
  rw [coe_compl]
  exact s.insert_inj_on

theorem image_univ_of_surjective [Fintype β] {f : β → α} (hf : Surjective f) : univ.Image f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_image_of_mem _ <| mem_univ _

end BooleanAlgebra

theorem map_univ_of_surjective [Fintype β] {f : β ↪ α} (hf : Surjective f) : univ.map f = univ :=
  eq_univ_of_forall <| hf.forall.2 fun _ => mem_map_of_mem _ <| mem_univ _

@[simp]
theorem map_univ_equiv [Fintype β] (f : β ≃ α) : univ.map f.toEmbedding = univ :=
  map_univ_of_surjective f.Surjective

@[simp]
theorem univ_inter [DecidableEq α] (s : Finset α) : univ ∩ s = s :=
  ext fun a => by
    simp

@[simp]
theorem inter_univ [DecidableEq α] (s : Finset α) : s ∩ univ = s := by
  rw [inter_comm, univ_inter]

@[simp]
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (univ : Finset α))] {δ : α → Sort _} (f g : ∀ i, δ i) :
    univ.piecewise f g = f := by
  ext i
  simp [← piecewise]

theorem piecewise_compl [DecidableEq α] (s : Finset α) [∀ i : α, Decidable (i ∈ s)] [∀ i : α, Decidable (i ∈ sᶜ)]
    {δ : α → Sort _} (f g : ∀ i, δ i) : sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [← piecewise]

@[simp]
theorem piecewise_erase_univ {δ : α → Sort _} [DecidableEq α] (a : α) (f g : ∀ a, δ a) :
    (Finset.univ.erase a).piecewise f g = Function.update f a (g a) := by
  rw [← compl_singleton, piecewise_compl, piecewise_singleton]

theorem univ_map_equiv_to_embedding {α β : Type _} [Fintype α] [Fintype β] (e : α ≃ β) :
    univ.map e.toEmbedding = univ :=
  eq_univ_iff_forall.mpr fun b =>
    mem_map.mpr
      ⟨e.symm b, mem_univ _, by
        simp ⟩

@[simp]
theorem univ_filter_exists (f : α → β) [Fintype β] [DecidablePred fun y => ∃ x, f x = y] [DecidableEq β] :
    (Finset.univ.filter fun y => ∃ x, f x = y) = Finset.univ.Image f := by
  ext
  simp

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
theorem univ_filter_mem_range (f : α → β) [Fintype β] [DecidablePred fun y => y ∈ Set.Range f] [DecidableEq β] :
    (Finset.univ.filter fun y => y ∈ Set.Range f) = Finset.univ.Image f :=
  univ_filter_exists f

theorem coe_filter_univ (p : α → Prop) [DecidablePred p] : (univ.filter p : Set α) = { x | p x } := by
  rw [coe_filter, coe_univ, Set.sep_univ]

/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_supr [CompleteLattice β] (f : α → β) : Finset.univ.sup f = supr f :=
  (sup_eq_supr _ f).trans <| congr_arg _ <| funext fun a => supr_pos (mem_univ _)

/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_infi [CompleteLattice β] (f : α → β) : Finset.univ.inf f = infi f :=
  sup_univ_eq_supr (f : α → βᵒᵈ)

@[simp]
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) : (Finset.univ.fold (·⊓·) a fun x => x) = ⊥ :=
  eq_bot_iff.2 <| ((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ <| Finset.mem_univ _

@[simp]
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) : (Finset.univ.fold (·⊔·) a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ ‹Fintype α› _ _ _

end Finset

open Finset Function

namespace Fintype

instance decidablePiFintype {α} {β : α → Type _} [∀ a, DecidableEq (β a)] [Fintype α] : DecidableEq (∀ a, β a) :=
  fun f g =>
  decidableOfIff (∀, ∀ a ∈ Fintype.elems α, ∀, f a = g a)
    (by
      simp [← Function.funext_iffₓ, ← Fintype.complete])

instance decidableForallFintype {p : α → Prop} [DecidablePred p] [Fintype α] : Decidable (∀ a, p a) :=
  decidableOfIff (∀, ∀ a ∈ @univ α _, ∀, p a)
    (by
      simp )

instance decidableExistsFintype {p : α → Prop} [DecidablePred p] [Fintype α] : Decidable (∃ a, p a) :=
  decidableOfIff (∃ a ∈ @univ α _, p a)
    (by
      simp )

instance decidableMemRangeFintype [Fintype α] [DecidableEq β] (f : α → β) : DecidablePred (· ∈ Set.Range f) := fun x =>
  Fintype.decidableExistsFintype

section BundledHoms

instance decidableEqEquivFintype [DecidableEq β] [Fintype α] : DecidableEq (α ≃ β) := fun a b =>
  decidableOfIff (a.1 = b.1) Equivₓ.coe_fn_injective.eq_iff

instance decidableEqEmbeddingFintype [DecidableEq β] [Fintype α] : DecidableEq (α ↪ β) := fun a b =>
  decidableOfIff ((a : α → β) = b) Function.Embedding.coe_injective.eq_iff

@[to_additive]
instance decidableEqOneHomFintype [DecidableEq β] [Fintype α] [One α] [One β] : DecidableEq (OneHom α β) := fun a b =>
  decidableOfIff ((a : α → β) = b) (Injective.eq_iff OneHom.coe_inj)

@[to_additive]
instance decidableEqMulHomFintype [DecidableEq β] [Fintype α] [Mul α] [Mul β] : DecidableEq (α →ₙ* β) := fun a b =>
  decidableOfIff ((a : α → β) = b) (Injective.eq_iff MulHom.coe_inj)

@[to_additive]
instance decidableEqMonoidHomFintype [DecidableEq β] [Fintype α] [MulOneClassₓ α] [MulOneClassₓ β] :
    DecidableEq (α →* β) := fun a b => decidableOfIff ((a : α → β) = b) (Injective.eq_iff MonoidHom.coe_inj)

instance decidableEqMonoidWithZeroHomFintype [DecidableEq β] [Fintype α] [MulZeroOneClassₓ α] [MulZeroOneClassₓ β] :
    DecidableEq (α →*₀ β) := fun a b => decidableOfIff ((a : α → β) = b) (Injective.eq_iff MonoidWithZeroHom.coe_inj)

instance decidableEqRingHomFintype [DecidableEq β] [Fintype α] [Semiringₓ α] [Semiringₓ β] : DecidableEq (α →+* β) :=
  fun a b => decidableOfIff ((a : α → β) = b) (Injective.eq_iff RingHom.coe_inj)

end BundledHoms

instance decidableInjectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] :
    DecidablePred (Injective : (α → β) → Prop) := fun x => by
  unfold injective <;> infer_instance

instance decidableSurjectiveFintype [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Surjective : (α → β) → Prop) := fun x => by
  unfold surjective <;> infer_instance

instance decidableBijectiveFintype [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] :
    DecidablePred (Bijective : (α → β) → Prop) := fun x => by
  unfold bijective <;> infer_instance

instance decidableRightInverseFintype [DecidableEq α] [Fintype α] (f : α → β) (g : β → α) :
    Decidable (Function.RightInverse f g) :=
  show Decidable (∀ x, g (f x) = x) by
    infer_instance

instance decidableLeftInverseFintype [DecidableEq β] [Fintype β] (f : α → β) (g : β → α) :
    Decidable (Function.LeftInverse f g) :=
  show Decidable (∀ x, f (g x) = x) by
    infer_instance

theorem exists_max [Fintype α] [Nonempty α] {β : Type _} [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by
  simpa using exists_max_image univ f univ_nonempty

theorem exists_min [Fintype α] [Nonempty α] {β : Type _} [LinearOrderₓ β] (f : α → β) : ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by
  simpa using exists_min_image univ f univ_nonempty

/-- Construct a proof of `fintype α` from a universal multiset -/
def ofMultiset [DecidableEq α] (s : Multiset α) (H : ∀ x : α, x ∈ s) : Fintype α :=
  ⟨s.toFinset, by
    simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def ofList [DecidableEq α] (l : List α) (H : ∀ x : α, x ∈ l) : Fintype α :=
  ⟨l.toFinset, by
    simpa using H⟩

theorem exists_univ_list (α) [Fintype α] : ∃ l : List α, l.Nodup ∧ ∀ x : α, x ∈ l :=
  let ⟨l, e⟩ := Quotientₓ.exists_rep (@univ α _).1
  have := And.intro univ.2 mem_univ_val
  ⟨_, by
    rwa [← e] at this⟩

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [Fintype α] : ℕ :=
  (@univ α _).card

/-- There is (computably) an equivalence between `α` and `fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `trunc` to
preserve computability.

See `fintype.equiv_fin` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.

See `fintype.trunc_fin_bijection` for a version without `[decidable_eq α]`.
-/
def truncEquivFin (α) [DecidableEq α] [Fintype α] : Trunc (α ≃ Finₓ (card α)) := by
  unfold card Finset.card
  exact
    Quot.recOnSubsingleton (@univ α _).1
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.nthLeEquivOfForallMemList _ h).symm) mem_univ_val
      univ.2

/-- There is (noncomputably) an equivalence between `α` and `fin (card α)`.

See `fintype.trunc_equiv_fin` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.
-/
noncomputable def equivFin (α) [Fintype α] : α ≃ Finₓ (card α) := by
  let this := Classical.decEq α
  exact (trunc_equiv_fin α).out

/-- There is (computably) a bijection between `fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `trunc` to
preserve computability.

See `fintype.trunc_equiv_fin` for a version that gives an equivalence
given `[decidable_eq α]`.
-/
def truncFinBijection (α) [Fintype α] : Trunc { f : Finₓ (card α) → α // Bijective f } := by
  dunfold card Finset.card
  exact
    Quot.recOnSubsingleton (@univ α _).1
      (fun l (h : ∀ x : α, x ∈ l) (nd : l.Nodup) => Trunc.mk (nd.nthLeBijectionOfForallMemList _ h)) mem_univ_val univ.2

instance (α : Type _) : Subsingleton (Fintype α) :=
  ⟨fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ => by
    congr <;> simp [← Finset.ext_iff, ← h₁, ← h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) : Fintype { x // p x } :=
  ⟨⟨s.1.pmap Subtype.mk fun x => (H x).1, s.Nodup.pmap fun a _ b _ => congr_arg Subtype.val⟩, fun ⟨x, px⟩ =>
    Multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

theorem subtype_card {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
    @card { x // p x } (Fintype.subtype s H) = s.card :=
  Multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) [Fintype { x // p x }] :
    card { x // p x } = s.card := by
  rw [← subtype_card s H]
  congr

/-- Construct a fintype from a finset with the same elements. -/
def ofFinset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
  Fintype.subtype s H

@[simp]
theorem card_of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : @Fintype.card p (ofFinset s H) = s.card :=
  Fintype.subtype_card s H

theorem card_of_finset' {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) [Fintype p] : Fintype.card p = s.card := by
  rw [← card_of_finset s H] <;> congr

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def ofBijective [Fintype α] (f : α → β) (H : Function.Bijective f) : Fintype β :=
  ⟨univ.map ⟨f, H.1⟩, fun b =>
    let ⟨a, e⟩ := H.2 b
    e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def ofSurjective [DecidableEq β] [Fintype α] (f : α → β) (H : Function.Surjective f) : Fintype β :=
  ⟨univ.Image f, fun b =>
    let ⟨a, e⟩ := H b
    e ▸ mem_image_of_mem _ (mem_univ _)⟩

end Fintype

section Inv

namespace Function

variable [Fintype α] [DecidableEq β]

namespace Injective

variable {f : α → β} (hf : Function.Injective f)

/-- The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def invOfMemRange : Set.Range f → α := fun b =>
  Finset.choose (fun a => f a = b) Finset.univ
    ((exists_unique_congr
          (by
            simp )).mp
      (hf.exists_unique_of_mem_range b.property))

theorem left_inv_of_inv_of_mem_range (b : Set.Range f) : f (hf.invOfMemRange b) = b :=
  (Finset.choose_spec (fun a => f a = b) _ _).right

@[simp]
theorem right_inv_of_inv_of_mem_range (a : α) : hf.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  hf (Finset.choose_spec (fun a' => f a' = f a) _ _).right

theorem inv_fun_restrict [Nonempty α] : (Set.Range f).restrict (invFun f) = hf.invOfMemRange := by
  ext ⟨b, h⟩
  apply hf
  simp [← hf.left_inv_of_inv_of_mem_range, ← @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]

theorem inv_of_mem_range_surjective : Function.Surjective hf.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by
    simp ⟩

end Injective

namespace Embedding

variable (f : α ↪ β) (b : Set.Range f)

/-- The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def invOfMemRange : α :=
  f.Injective.invOfMemRange b

@[simp]
theorem left_inv_of_inv_of_mem_range : f (f.invOfMemRange b) = b :=
  f.Injective.left_inv_of_inv_of_mem_range b

@[simp]
theorem right_inv_of_inv_of_mem_range (a : α) : f.invOfMemRange ⟨f a, Set.mem_range_self a⟩ = a :=
  f.Injective.right_inv_of_inv_of_mem_range a

theorem inv_fun_restrict [Nonempty α] : (Set.Range f).restrict (invFun f) = f.invOfMemRange := by
  ext ⟨b, h⟩
  apply f.injective
  simp [← f.left_inv_of_inv_of_mem_range, ← @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]

theorem inv_of_mem_range_surjective : Function.Surjective f.invOfMemRange := fun a =>
  ⟨⟨f a, Set.mem_range_self a⟩, by
    simp ⟩

end Embedding

end Function

end Inv

namespace Fintype

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def ofInjective [Fintype β] (f : α → β) (H : Function.Injective f) : Fintype α := by
  let this := Classical.dec <;>
    exact
      if hα : Nonempty α then by
        let this := Classical.inhabitedOfNonempty hα <;> exact of_surjective (inv_fun f) (inv_fun_surjective H)
      else ⟨∅, fun x => (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def ofEquiv (α : Type _) [Fintype α] (f : α ≃ β) : Fintype β :=
  ofBijective _ f.Bijective

theorem of_equiv_card [Fintype α] (f : α ≃ β) : @card β (ofEquiv α f) = card α :=
  Multiset.card_map _ _

theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
  rw [← of_equiv_card f] <;> congr

@[congr]
theorem card_congr' {α β} [Fintype α] [Fintype β] (h : α = β) : card α = card β :=
  card_congr
    (by
      rw [h])

section

variable [Fintype α] [Fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `fin n`.

See `fintype.equiv_fin_of_card_eq` for the noncomputable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
def truncEquivFinOfCardEq [DecidableEq α] {n : ℕ} (h : Fintype.card α = n) : Trunc (α ≃ Finₓ n) :=
  (truncEquivFin α).map fun e => e.trans (Finₓ.cast h).toEquiv

/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `fin n`.

See `fintype.trunc_equiv_fin_of_card_eq` for the computable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
noncomputable def equivFinOfCardEq {n : ℕ} (h : Fintype.card α = n) : α ≃ Finₓ n := by
  let this := Classical.decEq α
  exact (trunc_equiv_fin_of_card_eq h).out

/-- Two `fintype`s with the same cardinality are (computably) in bijection.

See `fintype.equiv_of_card_eq` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
def truncEquivOfCardEq [DecidableEq α] [DecidableEq β] (h : card α = card β) : Trunc (α ≃ β) :=
  (truncEquivFinOfCardEq h).bind fun e => (truncEquivFin β).map fun e' => e.trans e'.symm

/-- Two `fintype`s with the same cardinality are (noncomputably) in bijection.

See `fintype.trunc_equiv_of_card_eq` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
noncomputable def equivOfCardEq (h : card α = card β) : α ≃ β := by
  let this := Classical.decEq α
  let this := Classical.decEq β
  exact (trunc_equiv_of_card_eq h).out

end

theorem card_eq {α β} [F : Fintype α] [G : Fintype β] : card α = card β ↔ Nonempty (α ≃ β) :=
  ⟨fun h => by
    have := Classical.propDecidable
    exact (trunc_equiv_of_card_eq h).Nonempty, fun ⟨f⟩ => card_congr f⟩

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def ofSubsingleton (a : α) [Subsingleton α] : Fintype α :=
  ⟨{a}, fun b => Finset.mem_singleton.2 (Subsingleton.elimₓ _ _)⟩

@[simp]
theorem univ_of_subsingleton (a : α) [Subsingleton α] : @univ _ (ofSubsingleton a) = {a} :=
  rfl

/-- Note: this lemma is specifically about `fintype.of_subsingleton`. For a statement about
arbitrary `fintype` instances, use either `fintype.card_le_one_iff_subsingleton` or
`fintype.card_unique`. -/
@[simp]
theorem card_of_subsingleton (a : α) [Subsingleton α] : @Fintype.card _ (ofSubsingleton a) = 1 :=
  rfl

@[simp]
theorem card_unique [Unique α] [h : Fintype α] : Fintype.card α = 1 :=
  Subsingleton.elimₓ (ofSubsingleton default) h ▸ card_of_subsingleton _

-- see Note [lower instance priority]
instance (priority := 100) ofIsEmpty [IsEmpty α] : Fintype α :=
  ⟨∅, isEmptyElim⟩

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `finset.univ_eq_empty`. -/
-- no-lint since while `finset.univ_eq_empty` can prove this, it isn't applicable for `dsimp`.
@[simp, nolint simp_nf]
theorem univ_of_is_empty [IsEmpty α] : @univ α _ = ∅ :=
  rfl

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.card_eq_zero_iff`. -/
@[simp]
theorem card_of_is_empty [IsEmpty α] : Fintype.card α = 0 :=
  rfl

open Classical

variable (α)

/-- Any subsingleton type is (noncomputably) a fintype (with zero or one term). -/
-- see Note [lower instance priority]
noncomputable instance (priority := 5) ofSubsingleton' [Subsingleton α] : Fintype α :=
  if h : Nonempty α then ofSubsingleton (Nonempty.some h) else @Fintype.ofIsEmpty _ <| not_nonempty_iff.mp h

end Fintype

namespace Set

/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def toFinset (s : Set α) [Fintype s] : Finset α :=
  ⟨(@Finset.univ s _).1.map Subtype.val, Finset.univ.Nodup.map fun a b => Subtype.eq⟩

@[congr]
theorem to_finset_congr {s t : Set α} [Fintype s] [Fintype t] (h : s = t) : toFinset s = toFinset t := by
  cc

@[simp]
theorem mem_to_finset {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset ↔ a ∈ s := by
  simp [← to_finset]

@[simp]
theorem mem_to_finset_val {s : Set α} [Fintype s] {a : α} : a ∈ s.toFinset.1 ↔ a ∈ s :=
  mem_to_finset

/-- Membership of a set with a `fintype` instance is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidableMemOfFintype [DecidableEq α] (s : Set α) [Fintype s] (a) : Decidable (a ∈ s) :=
  decidableOfIff _ mem_to_finset

-- We use an arbitrary `[fintype s]` instance here,
-- not necessarily coming from a `[fintype α]`.
@[simp]
theorem to_finset_card {α : Type _} (s : Set α) [Fintype s] : s.toFinset.card = Fintype.card s :=
  Multiset.card_map Subtype.val Finset.univ.val

@[simp]
theorem coe_to_finset (s : Set α) [Fintype s] : (↑s.toFinset : Set α) = s :=
  Set.ext fun _ => mem_to_finset

@[simp]
theorem to_finset_inj {s t : Set α} [Fintype s] [Fintype t] : s.toFinset = t.toFinset ↔ s = t :=
  ⟨fun h => by
    rw [← s.coe_to_finset, h, t.coe_to_finset], fun h => by
    simp [← h] <;> congr⟩

@[simp, mono]
theorem to_finset_mono {s t : Set α} [Fintype s] [Fintype t] : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp [← Finset.subset_iff, ← Set.subset_def]

@[simp, mono]
theorem to_finset_strict_mono {s t : Set α} [Fintype s] [Fintype t] : s.toFinset ⊂ t.toFinset ↔ s ⊂ t := by
  simp only [← Finset.ssubset_def, ← to_finset_mono, ← ssubset_def]

@[simp]
theorem to_finset_disjoint_iff [DecidableEq α] {s t : Set α} [Fintype s] [Fintype t] :
    Disjoint s.toFinset t.toFinset ↔ Disjoint s t := by
  simp only [disjoint_coe, ← coe_to_finset]

theorem to_finset_inter {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∩ t : Set α)] [Fintype s] [Fintype t] :
    (s ∩ t).toFinset = s.toFinset ∩ t.toFinset := by
  ext
  simp

theorem to_finset_union {α : Type _} [DecidableEq α] (s t : Set α) [Fintype (s ∪ t : Set α)] [Fintype s] [Fintype t] :
    (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext
  simp

theorem to_finset_diff {α : Type _} [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] [Fintype (s \ t : Set α)] :
    (s \ t).toFinset = s.toFinset \ t.toFinset := by
  ext
  simp

theorem to_finset_ne_eq_erase {α : Type _} [DecidableEq α] [Fintype α] (a : α) [Fintype { x : α | x ≠ a }] :
    { x : α | x ≠ a }.toFinset = Finset.univ.erase a := by
  ext
  simp

theorem to_finset_compl [DecidableEq α] [Fintype α] (s : Set α) [Fintype s] [Fintype ↥(sᶜ)] :
    sᶜ.toFinset = s.toFinsetᶜ := by
  ext
  simp

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug;
it essentially infers `fintype.{v} (set.univ.{u} : set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp]
theorem to_finset_univ [Fintype ↥(Set.Univ : Set α)] [Fintype α] : (Set.Univ : Set α).toFinset = Finset.univ := by
  ext
  simp

@[simp]
theorem to_finset_range [DecidableEq α] [Fintype β] (f : β → α) [Fintype (Set.Range f)] :
    (Set.Range f).toFinset = Finset.univ.Image f := by
  ext
  simp

-- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`.
theorem to_finset_singleton (a : α) [Fintype ↥({a} : Set α)] : ({a} : Set α).toFinset = {a} := by
  ext
  simp

-- TODO The `↥` circumvents an elaboration bug. See comment on `set.to_finset_univ`.
@[simp]
theorem to_finset_insert [DecidableEq α] {a : α} {s : Set α} [Fintype ↥(insert a s : Set α)] [Fintype s] :
    (insert a s).toFinset = insert a s.toFinset := by
  ext
  simp

theorem filter_mem_univ_eq_to_finset [Fintype α] (s : Set α) [Fintype s] [DecidablePred (· ∈ s)] :
    Finset.univ.filter (· ∈ s) = s.toFinset := by
  ext
  simp only [← mem_filter, ← Finset.mem_univ, ← true_andₓ, ← mem_to_finset]

end Set

@[simp]
theorem Finset.to_finset_coe (s : Finset α) [Fintype ↥(s : Set α)] : (s : Set α).toFinset = s :=
  ext fun _ => Set.mem_to_finset

theorem Finset.card_univ [Fintype α] : (Finset.univ : Finset α).card = Fintype.card α :=
  rfl

theorem Finset.eq_univ_of_card [Fintype α] (s : Finset α) (hs : s.card = Fintype.card α) : s = univ :=
  eq_of_subset_of_card_le (subset_univ _) <| by
    rw [hs, Finset.card_univ]

theorem Finset.card_eq_iff_eq_univ [Fintype α] (s : Finset α) : s.card = Fintype.card α ↔ s = Finset.univ :=
  ⟨s.eq_univ_of_card, by
    rintro rfl
    exact Finset.card_univ⟩

theorem Finset.card_le_univ [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α :=
  card_le_of_subset (subset_univ s)

theorem Finset.card_lt_univ_of_not_mem [Fintype α] {s : Finset α} {x : α} (hx : x ∉ s) : s.card < Fintype.card α :=
  card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, fun hx' => hx (hx' <| mem_univ x)⟩⟩

theorem Finset.card_lt_iff_ne_univ [Fintype α] (s : Finset α) : s.card < Fintype.card α ↔ s ≠ Finset.univ :=
  s.card_le_univ.lt_iff_ne.trans (not_iff_not_of_iff s.card_eq_iff_eq_univ)

theorem Finset.card_compl_lt_iff_nonempty [Fintype α] [DecidableEq α] (s : Finset α) :
    sᶜ.card < Fintype.card α ↔ s.Nonempty :=
  sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

theorem Finset.card_univ_diff [DecidableEq α] [Fintype α] (s : Finset α) :
    (Finset.univ \ s).card = Fintype.card α - s.card :=
  Finset.card_sdiff (subset_univ s)

theorem Finset.card_compl [DecidableEq α] [Fintype α] (s : Finset α) : sᶜ.card = Fintype.card α - s.card :=
  Finset.card_univ_diff s

theorem Fintype.card_compl_set [Fintype α] (s : Set α) [Fintype s] [Fintype ↥(sᶜ)] :
    Fintype.card ↥(sᶜ) = Fintype.card α - Fintype.card s := by
  classical
  rw [← Set.to_finset_card, ← Set.to_finset_card, ← Finset.card_compl, Set.to_finset_compl]

instance (n : ℕ) : Fintype (Finₓ n) :=
  ⟨Finset.finRange n, Finset.mem_fin_range⟩

theorem Finₓ.univ_def (n : ℕ) : (univ : Finset (Finₓ n)) = Finset.finRange n :=
  rfl

@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Finₓ n) = n :=
  List.length_fin_range n

@[simp]
theorem Finset.card_fin (n : ℕ) : Finset.card (Finset.univ : Finset (Finₓ n)) = n := by
  rw [Finset.card_univ, Fintype.card_fin]

/-- `fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
theorem fin_injective : Function.Injective Finₓ := fun m n h =>
  (Fintype.card_fin m).symm.trans <| (Fintype.card_congr <| Equivₓ.cast h).trans (Fintype.card_fin n)

/-- A reversed version of `fin.cast_eq_cast` that is easier to rewrite with. -/
theorem Finₓ.cast_eq_cast' {n m : ℕ} (h : Finₓ n = Finₓ m) : cast h = ⇑(Finₓ.cast <| fin_injective h) :=
  (Finₓ.cast_eq_cast _).symm

theorem card_finset_fin_le {n : ℕ} (s : Finset (Finₓ n)) : s.card ≤ n := by
  simpa only [← Fintype.card_fin] using s.card_le_univ

theorem Finₓ.equiv_iff_eq {m n : ℕ} : Nonempty (Finₓ m ≃ Finₓ n) ↔ m = n :=
  ⟨fun ⟨h⟩ => by
    simpa using Fintype.card_congr h, fun h => ⟨Equivₓ.cast <| h ▸ rfl⟩⟩

@[simp]
theorem Finₓ.image_succ_above_univ {n : ℕ} (i : Finₓ (n + 1)) : univ.Image i.succAbove = {i}ᶜ := by
  ext m
  simp

@[simp]
theorem Finₓ.image_succ_univ (n : ℕ) : (univ : Finset (Finₓ n)).Image Finₓ.succ = {0}ᶜ := by
  rw [← Finₓ.succ_above_zero, Finₓ.image_succ_above_univ]

@[simp]
theorem Finₓ.image_cast_succ (n : ℕ) : (univ : Finset (Finₓ n)).Image Finₓ.castSucc = {Finₓ.last n}ᶜ := by
  rw [← Finₓ.succ_above_last, Finₓ.image_succ_above_univ]

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
/- The following three lemmas use `finset.cons` instead of `insert` and `finset.map` instead of
`finset.image` to reduce proof obligations downstream. -/
theorem Finₓ.univ_succ (n : ℕ) :
    (univ : Finset (Finₓ (n + 1))) =
      cons 0 (univ.map ⟨Finₓ.succ, Finₓ.succ_injective _⟩)
        (by
          simp [← map_eq_image]) :=
  by
  simp [← map_eq_image]

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
theorem Finₓ.univ_cast_succ (n : ℕ) :
    (univ : Finset (Finₓ (n + 1))) =
      cons (Finₓ.last n) (univ.map Finₓ.castSucc.toEmbedding)
        (by
          simp [← map_eq_image]) :=
  by
  simp [← map_eq_image]

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
theorem Finₓ.univ_succ_above (n : ℕ) (p : Finₓ (n + 1)) :
    (univ : Finset (Finₓ (n + 1))) =
      cons p (univ.map <| (Finₓ.succAbove p).toEmbedding)
        (by
          simp ) :=
  by
  simp [← map_eq_image]

@[instance]
def Unique.fintype {α : Type _} [Unique α] : Fintype α :=
  Fintype.ofSubsingleton default

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq (y : α) : Fintype { x // x = y } :=
  Fintype.subtype {y}
    (by
      simp )

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance Fintype.subtypeEq' (y : α) : Fintype { x // y = x } :=
  Fintype.subtype {y}
    (by
      simp [← eq_comm])

@[simp]
theorem Fintype.card_subtype_eq (y : α) [Fintype { x // x = y }] : Fintype.card { x // x = y } = 1 :=
  Fintype.card_unique

@[simp]
theorem Fintype.card_subtype_eq' (y : α) [Fintype { x // y = x }] : Fintype.card { x // y = x } = 1 :=
  Fintype.card_unique

@[simp]
theorem Fintype.univ_empty : @univ Empty _ = ∅ :=
  rfl

@[simp]
theorem Fintype.card_empty : Fintype.card Empty = 0 :=
  rfl

@[simp]
theorem Fintype.univ_pempty : @univ Pempty _ = ∅ :=
  rfl

@[simp]
theorem Fintype.card_pempty : Fintype.card Pempty = 0 :=
  rfl

instance : Fintype Unit :=
  Fintype.ofSubsingleton ()

theorem Fintype.univ_unit : @univ Unit _ = {()} :=
  rfl

theorem Fintype.card_unit : Fintype.card Unit = 1 :=
  rfl

instance : Fintype PUnit :=
  Fintype.ofSubsingleton PUnit.unit

@[simp]
theorem Fintype.univ_punit : @univ PUnit _ = {PUnit.unit} :=
  rfl

@[simp]
theorem Fintype.card_punit : Fintype.card PUnit = 1 :=
  rfl

instance : Fintype Bool :=
  ⟨⟨tt ::ₘ ff ::ₘ 0, by
      simp ⟩,
    fun x => by
    cases x <;> simp ⟩

@[simp]
theorem Fintype.univ_bool : @univ Bool _ = {true, false} :=
  rfl

instance UnitsInt.fintype : Fintype ℤˣ :=
  ⟨{1, -1}, fun x => by
    cases Int.units_eq_one_or x <;> simp [*]⟩

@[simp]
theorem UnitsInt.univ : (Finset.univ : Finset ℤˣ) = {1, -1} :=
  rfl

instance Additive.fintype : ∀ [Fintype α], Fintype (Additive α) :=
  id

instance Multiplicative.fintype : ∀ [Fintype α], Fintype (Multiplicative α) :=
  id

@[simp]
theorem Fintype.card_units_int : Fintype.card ℤˣ = 2 :=
  rfl

@[simp]
theorem Fintype.card_bool : Fintype.card Bool = 2 :=
  rfl

instance {α : Type _} [Fintype α] : Fintype (Option α) :=
  ⟨univ.insertNone, fun a => by
    simp ⟩

theorem univ_option (α : Type _) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl

@[simp]
theorem Fintype.card_option {α : Type _} [Fintype α] : Fintype.card (Option α) = Fintype.card α + 1 :=
  (Finset.card_cons _).trans <| congr_arg2ₓ _ (card_map _) rfl

/-- If `option α` is a `fintype` then so is `α` -/
def fintypeOfOption {α : Type _} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (Option α)), fun x => mem_erase_none.mpr (Fintype.complete (some x))⟩

/-- A type is a `fintype` if its successor (using `option`) is a `fintype`. -/
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β := by
  have := Fintype.ofEquiv _ f
  exact fintypeOfOption

instance {α : Type _} (β : α → Type _) [Fintype α] [∀ a, Fintype (β a)] : Fintype (Sigma β) :=
  ⟨univ.Sigma fun _ => univ, fun ⟨a, b⟩ => by
    simp ⟩

@[simp]
theorem Finset.univ_sigma_univ {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] :
    ((univ : Finset α).Sigma fun a => (univ : Finset (β a))) = univ :=
  rfl

instance (α β : Type _) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ.product univ, fun ⟨a, b⟩ => by
    simp ⟩

@[simp]
theorem Finset.univ_product_univ {α β : Type _} [Fintype α] [Fintype β] :
    (univ : Finset α).product (univ : Finset β) = univ :=
  rfl

@[simp]
theorem Fintype.card_prod (α β : Type _) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def Fintype.prodLeft {α β} [DecidableEq α] [Fintype (α × β)] [Nonempty β] : Fintype α :=
  ⟨(Fintype.elems (α × β)).Image Prod.fst, fun a => by
    let ⟨b⟩ := ‹Nonempty β›
    simp <;> exact ⟨b, Fintype.complete _⟩⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def Fintype.prodRight {α β} [DecidableEq β] [Fintype (α × β)] [Nonempty α] : Fintype β :=
  ⟨(Fintype.elems (α × β)).Image Prod.snd, fun b => by
    let ⟨a⟩ := ‹Nonempty α›
    simp <;> exact ⟨a, Fintype.complete _⟩⟩

instance (α : Type _) [Fintype α] : Fintype (ULift α) :=
  Fintype.ofEquiv _ Equivₓ.ulift.symm

@[simp]
theorem Fintype.card_ulift (α : Type _) [Fintype α] : Fintype.card (ULift α) = Fintype.card α :=
  Fintype.of_equiv_card _

instance (α : Type _) [Fintype α] : Fintype (Plift α) :=
  Fintype.ofEquiv _ Equivₓ.plift.symm

@[simp]
theorem Fintype.card_plift (α : Type _) [Fintype α] : Fintype.card (Plift α) = Fintype.card α :=
  Fintype.of_equiv_card _

instance (α : Type _) [Fintype α] : Fintype αᵒᵈ :=
  ‹Fintype α›

@[simp]
theorem Fintype.card_order_dual (α : Type _) [Fintype α] : Fintype.card αᵒᵈ = Fintype.card α :=
  rfl

instance (α : Type _) [Fintype α] : Fintype (Lex α) :=
  ‹Fintype α›

@[simp]
theorem Fintype.card_lex (α : Type _) [Fintype α] : Fintype.card (Lex α) = Fintype.card α :=
  rfl

theorem univ_sum_type {α β : Type _} [Fintype α] [Fintype β] [Fintype (Sum α β)] [DecidableEq (Sum α β)] :
    (univ : Finset (Sum α β)) = map Function.Embedding.inl univ ∪ map Function.Embedding.inr univ := by
  rw [eq_comm, eq_univ_iff_forall]
  simp only [← mem_union, ← mem_map, ← exists_prop, ← mem_univ, ← true_andₓ]
  rintro (x | y)
  exacts[Or.inl ⟨x, rfl⟩, Or.inr ⟨y, rfl⟩]

instance (α : Type u) (β : Type v) [Fintype α] [Fintype β] : Fintype (Sum α β) :=
  @Fintype.ofEquiv _ _
    (@Sigma.fintype _ (fun b => cond b (ULift α) (ULift.{max u v, v} β)) _ fun b => by
      cases b <;> apply ULift.fintype)
    ((Equivₓ.sumEquivSigmaBool _ _).symm.trans (Equivₓ.sumCongr Equivₓ.ulift Equivₓ.ulift))

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def Fintype.sumLeft {α β} [Fintype (Sum α β)] : Fintype α :=
  Fintype.ofInjective (Sum.inl : α → Sum α β) Sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def Fintype.sumRight {α β} [Fintype (Sum α β)] : Fintype β :=
  Fintype.ofInjective (Sum.inr : β → Sum α β) Sum.inr_injective

@[simp]
theorem Fintype.card_sum [Fintype α] [Fintype β] : Fintype.card (Sum α β) = Fintype.card α + Fintype.card β := by
  classical
  rw [← Finset.card_univ, univ_sum_type, Finset.card_union_eq]
  · simp [← Finset.card_univ]
    
  · intro x hx
    suffices (∃ a : α, Sum.inl a = x) ∧ ∃ b : β, Sum.inr b = x by
      obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := this
      simpa using hb
    simpa using hx
    

/-- If the subtype of all-but-one elements is a `fintype` then the type itself is a `fintype`. -/
def fintypeOfFintypeNe (a : α) (h : Fintype { b // b ≠ a }) : Fintype α :=
  Fintype.ofBijective (Sum.elim (coe : { b // b = a } → α) (coe : { b // b ≠ a } → α)) <| by
    classical
    exact (Equivₓ.sumCompl (· = a)).Bijective

section Finset

/-! ### `fintype (s : finset α)` -/


instance Finset.fintypeCoeSort {α : Type u} (s : Finset α) : Fintype s :=
  ⟨s.attach, s.mem_attach⟩

@[simp]
theorem Finset.univ_eq_attach {α : Type u} (s : Finset α) : (univ : Finset s) = s.attach :=
  rfl

end Finset

namespace Fintype

variable [Fintype α] [Fintype β]

theorem card_le_of_injective (f : α → β) (hf : Function.Injective f) : card α ≤ card β :=
  Finset.card_le_card_of_inj_on f (fun _ _ => Finset.mem_univ _) fun _ _ _ _ h => hf h

theorem card_le_of_embedding (f : α ↪ β) : card α ≤ card β :=
  card_le_of_injective f f.2

theorem card_lt_of_injective_of_not_mem (f : α → β) (h : Function.Injective f) {b : β} (w : b ∉ Set.Range f) :
    card α < card β :=
  calc
    card α = (univ.map ⟨f, h⟩).card := (card_map _).symm
    _ < card β :=
      Finset.card_lt_univ_of_not_mem <| by
        rwa [← mem_coe, coe_map, coe_univ, Set.image_univ]
    

theorem card_lt_of_injective_not_surjective (f : α → β) (h : Function.Injective f) (h' : ¬Function.Surjective f) :
    card α < card β :=
  let ⟨y, hy⟩ := not_forall.1 h'
  card_lt_of_injective_of_not_mem f h hy

theorem card_le_of_surjective (f : α → β) (h : Function.Surjective f) : card β ≤ card α :=
  card_le_of_injective _ (Function.injective_surj_inv h)

theorem card_range_le {α β : Type _} (f : α → β) [Fintype α] [Fintype (Set.Range f)] :
    Fintype.card (Set.Range f) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective
    (fun a =>
      ⟨f a, by
        simp ⟩)
    fun ⟨_, a, ha⟩ =>
    ⟨a, by
      simpa using ha⟩

theorem card_range {α β F : Type _} [EmbeddingLike F α β] (f : F) [Fintype α] [Fintype (Set.Range f)] :
    Fintype.card (Set.Range f) = Fintype.card α :=
  Eq.symm <| Fintype.card_congr <| Equivₓ.ofInjective _ <| EmbeddingLike.injective f

/-- The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
theorem exists_ne_map_eq_of_card_lt (f : α → β) (h : Fintype.card β < Fintype.card α) : ∃ x y, x ≠ y ∧ f x = f y :=
  let ⟨x, _, y, _, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to h fun x _ => mem_univ (f x)
  ⟨x, y, h⟩

theorem card_eq_one_iff : card α = 1 ↔ ∃ x : α, ∀ y, y = x := by
  rw [← card_unit, card_eq] <;>
    exact
      ⟨fun ⟨a⟩ => ⟨a.symm (), fun y => a.Injective (Subsingleton.elimₓ _ _)⟩, fun ⟨x, hx⟩ =>
        ⟨⟨fun _ => (), fun _ => x, fun _ => (hx _).trans (hx _).symm, fun _ => Subsingleton.elimₓ _ _⟩⟩⟩

theorem card_eq_zero_iff : card α = 0 ↔ IsEmpty α := by
  rw [card, Finset.card_eq_zero, univ_eq_empty_iff]

theorem card_eq_zero [IsEmpty α] : card α = 0 :=
  card_eq_zero_iff.2 ‹_›

theorem card_eq_one_iff_nonempty_unique : card α = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨d, h⟩ := Fintype.card_eq_one_iff.mp h
    ⟨{ default := d, uniq := h }⟩,
    fun ⟨h⟩ => Fintype.card_unique⟩

/-- A `fintype` with cardinality zero is equivalent to `empty`. -/
def cardEqZeroEquivEquivEmpty : card α = 0 ≃ (α ≃ Empty) :=
  (Equivₓ.ofIff card_eq_zero_iff).trans (Equivₓ.equivEmptyEquiv α).symm

theorem card_pos_iff : 0 < card α ↔ Nonempty α :=
  pos_iff_ne_zero.trans <| not_iff_comm.mp <| not_nonempty_iff.trans card_eq_zero_iff.symm

theorem card_pos [h : Nonempty α] : 0 < card α :=
  card_pos_iff.mpr h

theorem card_ne_zero [Nonempty α] : card α ≠ 0 :=
  ne_of_gtₓ card_pos

theorem card_le_one_iff : card α ≤ 1 ↔ ∀ a b : α, a = b :=
  let n := card α
  have hn : n = card α := rfl
  match n, hn with
  | 0 => fun ha => ⟨fun h => fun a => (card_eq_zero_iff.1 ha.symm).elim a, fun _ => ha ▸ Nat.le_succₓ _⟩
  | 1 => fun ha =>
    ⟨fun h => fun a b => by
      let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm
      rw [hx a, hx b], fun _ => ha ▸ le_rfl⟩
  | n + 2 => fun ha =>
    ⟨fun h => by
      rw [← ha] at h <;>
        exact
          absurd h
            (by
              decide),
      fun h => card_unit ▸ card_le_of_injective (fun _ => ()) fun _ _ _ => h _ _⟩

theorem card_le_one_iff_subsingleton : card α ≤ 1 ↔ Subsingleton α :=
  card_le_one_iff.trans subsingleton_iff.symm

theorem one_lt_card_iff_nontrivial : 1 < card α ↔ Nontrivial α := by
  classical
  rw [← not_iff_not]
  push_neg
  rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]

theorem exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a := by
  have : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exact exists_ne a

theorem exists_pair_of_one_lt_card (h : 1 < card α) : ∃ a b : α, a ≠ b := by
  have : Nontrivial α := one_lt_card_iff_nontrivial.1 h
  exact exists_pair_ne α

theorem card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
  Fintype.card_eq_one_iff.2 ⟨i, h⟩

theorem one_lt_card [h : Nontrivial α] : 1 < Fintype.card α :=
  Fintype.one_lt_card_iff_nontrivial.mpr h

theorem one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
  one_lt_card_iff_nontrivial.trans nontrivial_iff

theorem two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  simp_rw [← Finset.card_univ, two_lt_card_iff, mem_univ, true_andₓ]

theorem injective_iff_surjective {f : α → α} : Injective f ↔ Surjective f :=
  have := Classical.propDecidable
  have : ∀ {f : α → α}, injective f → surjective f := fun f hinj x =>
    have h₁ : image f univ = univ :=
      eq_of_subset_of_card_le (subset_univ _) ((card_image_of_injective univ hinj).symm ▸ le_rfl)
    have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _
    exists_of_bex (mem_image.1 h₂)
  ⟨this, fun hsurj =>
    has_left_inverse.injective
      ⟨surj_inv hsurj,
        left_inverse_of_surjective_of_right_inverse (this (injective_surj_inv _)) (right_inverse_surj_inv _)⟩⟩

theorem injective_iff_bijective {f : α → α} : Injective f ↔ Bijective f := by
  simp [← bijective, ← injective_iff_surjective]

theorem surjective_iff_bijective {f : α → α} : Surjective f ↔ Bijective f := by
  simp [← bijective, ← injective_iff_surjective]

theorem injective_iff_surjective_of_equiv {β : Type _} {f : α → β} (e : α ≃ β) : Injective f ↔ Surjective f :=
  have : Injective (e.symm ∘ f) ↔ Surjective (e.symm ∘ f) := injective_iff_surjective
  ⟨fun hinj => by
    simpa [← Function.comp] using e.surjective.comp (this.1 (e.symm.injective.comp hinj)), fun hsurj => by
    simpa [← Function.comp] using e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

alias Fintype.injective_iff_surjective_of_equiv ↔
  _root_.function.injective.surjective_of_fintype _root_.function.surjective.injective_of_fintype

theorem card_of_bijective {f : α → β} (hf : Bijective f) : card α = card β :=
  card_congr (Equivₓ.ofBijective f hf)

theorem bijective_iff_injective_and_card (f : α → β) : Bijective f ↔ Injective f ∧ card α = card β :=
  ⟨fun h => ⟨h.1, card_of_bijective h⟩, fun h => ⟨h.1, h.1.surjective_of_fintype <| equivOfCardEq h.2⟩⟩

theorem bijective_iff_surjective_and_card (f : α → β) : Bijective f ↔ Surjective f ∧ card α = card β :=
  ⟨fun h => ⟨h.2, card_of_bijective h⟩, fun h => ⟨h.1.injective_of_fintype <| equivOfCardEq h.2, h.1⟩⟩

theorem _root_.function.left_inverse.right_inverse_of_card_le {f : α → β} {g : β → α} (hfg : LeftInverse f g)
    (hcard : card α ≤ card β) : RightInverse f g :=
  have hsurj : Surjective f := surjective_iff_has_right_inverse.2 ⟨g, hfg⟩
  right_inverse_of_injective_of_left_inverse
    ((bijective_iff_surjective_and_card _).2 ⟨hsurj, le_antisymmₓ hcard (card_le_of_surjective f hsurj)⟩).1 hfg

theorem _root_.function.right_inverse.left_inverse_of_card_le {f : α → β} {g : β → α} (hfg : RightInverse f g)
    (hcard : card β ≤ card α) : LeftInverse f g :=
  Function.LeftInverse.right_inverse_of_card_le hfg hcard

end Fintype

namespace Equivₓ

variable [Fintype α] [Fintype β]

open Fintype

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofLeftInverseOfCardLe (hβα : card β ≤ card α) (f : α → β) (g : β → α) (h : LeftInverse g f) : α ≃ β where
  toFun := f
  invFun := g
  left_inv := h
  right_inv := h.right_inverse_of_card_le hβα

/-- Construct an equivalence from functions that are inverse to each other. -/
@[simps]
def ofRightInverseOfCardLe (hαβ : card α ≤ card β) (f : α → β) (g : β → α) (h : RightInverse g f) : α ≃ β where
  toFun := f
  invFun := g
  left_inv := h.left_inverse_of_card_le hαβ
  right_inv := h

end Equivₓ

theorem Fintype.coe_image_univ [Fintype α] [DecidableEq β] {f : α → β} : ↑(Finset.image f Finset.univ) = Set.Range f :=
  by
  ext x
  simp

instance List.Subtype.fintype [DecidableEq α] (l : List α) : Fintype { x // x ∈ l } :=
  Fintype.ofList l.attach l.mem_attach

instance Multiset.Subtype.fintype [DecidableEq α] (s : Multiset α) : Fintype { x // x ∈ s } :=
  Fintype.ofMultiset s.attach s.mem_attach

instance Finset.subtype.fintype (s : Finset α) : Fintype { x // x ∈ s } :=
  ⟨s.attach, s.mem_attach⟩

instance FinsetCoe.fintype (s : Finset α) : Fintype (↑s : Set α) :=
  Finset.subtype.fintype s

@[simp]
theorem Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.card s = s.card :=
  Fintype.card_of_finset' s fun _ => Iff.rfl

/-- Noncomputable equivalence between a finset `s` coerced to a type and `fin s.card`. -/
noncomputable def Finset.equivFin (s : Finset α) : s ≃ Finₓ s.card :=
  Fintype.equivFinOfCardEq (Fintype.card_coe _)

/-- Noncomputable equivalence between a finset `s` as a fintype and `fin n`, when there is a
proof that `s.card = n`. -/
noncomputable def Finset.equivFinOfCardEq {s : Finset α} {n : ℕ} (h : s.card = n) : s ≃ Finₓ n :=
  Fintype.equivFinOfCardEq ((Fintype.card_coe _).trans h)

/-- Noncomputable equivalence between two finsets `s` and `t` as fintypes when there is a proof
that `s.card = t.card`.-/
noncomputable def Finset.equivOfCardEq {s t : Finset α} (h : s.card = t.card) : s ≃ t :=
  Fintype.equivOfCardEq ((Fintype.card_coe _).trans (h.trans (Fintype.card_coe _).symm))

theorem Finset.attach_eq_univ {s : Finset α} : s.attach = Finset.univ :=
  rfl

instance Plift.fintypeProp (p : Prop) [Decidable p] : Fintype (Plift p) :=
  ⟨if h : p then {⟨h⟩} else ∅, fun ⟨h⟩ => by
    simp [← h]⟩

instance Prop.fintype : Fintype Prop :=
  ⟨⟨True ::ₘ False ::ₘ 0, by
      simp [← true_ne_false]⟩,
    Classical.cases
      (by
        simp )
      (by
        simp )⟩

@[simp]
theorem Fintype.card_Prop : Fintype.card Prop = 2 :=
  rfl

instance Subtype.fintype (p : α → Prop) [DecidablePred p] [Fintype α] : Fintype { x // p x } :=
  Fintype.subtype (univ.filter p)
    (by
      simp )

@[simp]
theorem Set.to_finset_eq_empty_iff {s : Set α} [Fintype s] : s.toFinset = ∅ ↔ s = ∅ := by
  simp only [← ext_iff, ← Set.ext_iff, ← Set.mem_to_finset, ← not_mem_empty, ← Set.mem_empty_eq]

@[simp]
theorem Set.to_finset_empty : (∅ : Set α).toFinset = ∅ :=
  Set.to_finset_eq_empty_iff.mpr rfl

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def setFintype [Fintype α] (s : Set α) [DecidablePred (· ∈ s)] : Fintype s :=
  Subtype.fintype fun x => x ∈ s

theorem set_fintype_card_le_univ [Fintype α] (s : Set α) [Fintype ↥s] : Fintype.card ↥s ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype s)

theorem set_fintype_card_eq_univ_iff [Fintype α] (s : Set α) [Fintype ↥s] :
    Fintype.card s = Fintype.card α ↔ s = Set.Univ := by
  rw [← Set.to_finset_card, Finset.card_eq_iff_eq_univ, ← Set.to_finset_univ, Set.to_finset_inj]

section

variable (α)

/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def _root_.units_equiv_prod_subtype [Monoidₓ α] : αˣ ≃ { p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1 } where
  toFun := fun u => ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩
  invFun := fun p => Units.mk (p : α × α).1 (p : α × α).2 p.Prop.1 p.Prop.2
  left_inv := fun u => Units.ext rfl
  right_inv := fun p => Subtype.ext <| Prod.extₓ rfl rfl

/-- In a `group_with_zero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def _root_.units_equiv_ne_zero [GroupWithZeroₓ α] : αˣ ≃ { a : α // a ≠ 0 } :=
  ⟨fun a => ⟨a, a.ne_zero⟩, fun a => Units.mk0 _ a.Prop, fun _ => Units.ext rfl, fun _ => Subtype.ext rfl⟩

end

instance [Monoidₓ α] [Fintype α] [DecidableEq α] : Fintype αˣ :=
  Fintype.ofEquiv _ (unitsEquivProdSubtype α).symm

theorem Fintype.card_units [GroupWithZeroₓ α] [Fintype α] [Fintype αˣ] : Fintype.card αˣ = Fintype.card α - 1 := by
  classical
  rw [eq_comm, Nat.sub_eq_iff_eq_addₓ (Fintype.card_pos_iff.2 ⟨(0 : α)⟩), Fintype.card_congr (unitsEquivNeZero α)]
  have := Fintype.card_congr (Equivₓ.sumCompl (· = (0 : α))).symm
  rwa [Fintype.card_sum, add_commₓ, Fintype.card_subtype_eq] at this

namespace Function.Embedding

/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equivOfFintypeSelfEmbedding [Fintype α] (e : α ↪ α) : α ≃ α :=
  Equivₓ.ofBijective e (Fintype.injective_iff_bijective.1 e.2)

@[simp]
theorem equiv_of_fintype_self_embedding_to_embedding [Fintype α] (e : α ↪ α) :
    e.equivOfFintypeSelfEmbedding.toEmbedding = e := by
  ext
  rfl

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp]
theorem is_empty_of_card_lt [Fintype α] [Fintype β] (h : Fintype.card β < Fintype.card α) : IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨x, y, Ne, feq⟩ := Fintype.exists_ne_map_eq_of_card_lt f h
    Ne <| f.Injective feq⟩

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def truncOfCardLe [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (h : Fintype.card α ≤ Fintype.card β) :
    Trunc (α ↪ β) :=
  (Fintype.truncEquivFin α).bind fun ea =>
    (Fintype.truncEquivFin β).map fun eb => ea.toEmbedding.trans ((Finₓ.castLe h).toEmbedding.trans eb.symm.toEmbedding)

theorem nonempty_of_card_le [Fintype α] [Fintype β] (h : Fintype.card α ≤ Fintype.card β) : Nonempty (α ↪ β) := by
  classical
  exact (trunc_of_card_le h).Nonempty

theorem exists_of_card_le_finset [Fintype α] {s : Finset β} (h : Fintype.card α ≤ s.card) :
    ∃ f : α ↪ β, Set.Range f ⊆ s := by
  rw [← Fintype.card_coe] at h
  rcases nonempty_of_card_le h with ⟨f⟩
  exact
    ⟨f.trans (embedding.subtype _), by
      simp [← Set.range_subset_iff]⟩

end Function.Embedding

@[simp]
theorem Finset.univ_map_embedding {α : Type _} [Fintype α] (e : α ↪ α) : univ.map e = univ := by
  rw [← e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]

namespace Fintype

/-- Given `fintype α`, `finset_equiv_set` is the equiv between `finset α` and `set α`. (All
sets on a finite type are finite.) -/
noncomputable def finsetEquivSet [Fintype α] : Finset α ≃ Set α where
  toFun := coe
  invFun := by
    classical
    exact fun s => s.toFinset
  left_inv := fun s => by
    convert Finset.to_finset_coe s
  right_inv := fun s => s.coe_to_finset

@[simp]
theorem finset_equiv_set_apply [Fintype α] (s : Finset α) : finsetEquivSet s = s :=
  rfl

@[simp]
theorem finset_equiv_set_symm_apply [Fintype α] (s : Set α) [Fintype s] : finsetEquivSet.symm s = s.toFinset := by
  convert rfl

theorem card_lt_of_surjective_not_injective [Fintype α] [Fintype β] (f : α → β) (h : Function.Surjective f)
    (h' : ¬Function.Injective f) : card β < card α :=
  (card_lt_of_injective_not_surjective _ (Function.injective_surj_inv h)) fun hg =>
    have w : Function.Bijective (Function.surjInv h) := ⟨Function.injective_surj_inv h, hg⟩
    h' <| h.injective_of_fintype (Equivₓ.ofBijective _ w).symm

variable [DecidableEq α] [Fintype α] {δ : α → Type _}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def piFinset (t : ∀ a, Finset (δ a)) : Finset (∀ a, δ a) :=
  (Finset.univ.pi t).map
    ⟨fun f a => f a (mem_univ a), fun _ _ => by
      simp [← Function.funext_iffₓ]⟩

@[simp]
theorem mem_pi_finset {t : ∀ a, Finset (δ a)} {f : ∀ a, δ a} : f ∈ piFinset t ↔ ∀ a, f a ∈ t a := by
  constructor
  · simp only [← pi_finset, ← mem_map, ← and_imp, ← forall_prop_of_true, ← exists_prop, ← mem_univ, ←
      exists_imp_distrib, ← mem_pi]
    rintro g hg hgf a
    rw [← hgf]
    exact hg a
    
  · simp only [← pi_finset, ← mem_map, ← forall_prop_of_true, ← exists_prop, ← mem_univ, ← mem_pi]
    exact fun hf => ⟨fun a ha => f a, hf, rfl⟩
    

@[simp]
theorem coe_pi_finset (t : ∀ a, Finset (δ a)) : (piFinset t : Set (∀ a, δ a)) = Set.Pi Set.Univ fun a => t a :=
  Set.ext fun x => by
    rw [Set.mem_univ_pi]
    exact Fintype.mem_pi_finset

theorem pi_finset_subset (t₁ t₂ : ∀ a, Finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) : piFinset t₁ ⊆ piFinset t₂ := fun g hg =>
  mem_pi_finset.2 fun a => h a <| mem_pi_finset.1 hg a

@[simp]
theorem pi_finset_empty [Nonempty α] : piFinset (fun _ => ∅ : ∀ i, Finset (δ i)) = ∅ :=
  eq_empty_of_forall_not_mem fun _ => by
    simp

@[simp]
theorem pi_finset_singleton (f : ∀ i, δ i) : piFinset (fun i => {f i} : ∀ i, Finset (δ i)) = {f} :=
  ext fun _ => by
    simp only [← Function.funext_iffₓ, ← Fintype.mem_pi_finset, ← mem_singleton]

theorem pi_finset_subsingleton {f : ∀ i, Finset (δ i)} (hf : ∀ i, (f i : Set (δ i)).Subsingleton) :
    (Fintype.piFinset f : Set (∀ i, δ i)).Subsingleton := fun a ha b hb =>
  funext fun i => hf _ (mem_pi_finset.1 ha _) (mem_pi_finset.1 hb _)

theorem pi_finset_disjoint_of_disjoint [∀ a, DecidableEq (δ a)] (t₁ t₂ : ∀ a, Finset (δ a)) {a : α}
    (h : Disjoint (t₁ a) (t₂ a)) : Disjoint (piFinset t₁) (piFinset t₂) :=
  disjoint_iff_ne.2 fun f₁ hf₁ f₂ hf₂ eq₁₂ =>
    disjoint_iff_ne.1 h (f₁ a) (mem_pi_finset.1 hf₁ a) (f₂ a) (mem_pi_finset.1 hf₂ a) (congr_fun eq₁₂ a)

end Fintype

/-! ### pi -/


/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance Pi.fintype {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    Fintype (∀ a, β a) :=
  ⟨Fintype.piFinset fun _ => univ, by
    simp ⟩

@[simp]
theorem Fintype.pi_finset_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    (Fintype.piFinset fun a : α => (Finset.univ : Finset (β a))) = (Finset.univ : Finset (∀ a, β a)) :=
  rfl

instance DArray.fintype {n : ℕ} {α : Finₓ n → Type _} [∀ n, Fintype (α n)] : Fintype (DArray n α) :=
  Fintype.ofEquiv _ (Equivₓ.dArrayEquivFin _).symm

instance Arrayₓ.fintype {n : ℕ} {α : Type _} [Fintype α] : Fintype (Arrayₓ n α) :=
  DArray.fintype

instance Vector.fintype {α : Type _} [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equivₓ.vectorEquivFin _ _).symm

instance Quotientₓ.fintype [Fintype α] (s : Setoidₓ α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype (Quotientₓ s) :=
  Fintype.ofSurjective Quotientₓ.mk fun x => Quotientₓ.induction_on x fun x => ⟨x, rfl⟩

instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.Powerset, fun x => Finset.mem_powerset.2 (Finset.subset_univ _)⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
-- irreducible due to this conversation on Zulip:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/
-- topic/.60simp.60.20ignoring.20lemmas.3F/near/241824115
irreducible_def Function.Embedding.fintype {α β} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] :
  Fintype (α ↪ β) :=
  Fintype.ofEquiv _ (Equivₓ.subtypeInjectiveEquivEmbedding α β)

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  Quotientₓ.fintype _

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm

@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ

@[simp]
theorem Finset.powerset_univ [Fintype α] : (univ : Finset α).Powerset = univ :=
  coe_injective <| by
    simp [-coe_eq_univ]

@[simp]
theorem Finset.powerset_eq_univ [Fintype α] {s : Finset α} : s.Powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]

theorem Finset.mem_powerset_len_univ_iff [Fintype α] {s : Finset α} {k : ℕ} :
    s ∈ powersetLen k (univ : Finset α) ↔ card s = k :=
  mem_powerset_len.trans <| and_iff_right <| subset_univ _

@[simp]
theorem Finset.univ_filter_card_eq (α : Type _) [Fintype α] (k : ℕ) :
    ((Finset.univ : Finset (Finset α)).filter fun s => s.card = k) = Finset.univ.powersetLen k := by
  ext
  simp [← Finset.mem_powerset_len]

@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k := by
  simp [← Fintype.subtype_card, ← Finset.card_univ]

theorem Fintype.card_subtype_le [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } ≤ Fintype.card α :=
  Fintype.card_le_of_embedding (Function.Embedding.subtype _)

theorem Fintype.card_subtype_lt [Fintype α] {p : α → Prop} [DecidablePred p] {x : α} (hx : ¬p x) :
    Fintype.card { x // p x } < Fintype.card α :=
  Fintype.card_lt_of_injective_of_not_mem coe Subtype.coe_injective <| by
    rwa [Subtype.range_coe_subtype]

theorem Fintype.card_subtype [Fintype α] (p : α → Prop) [DecidablePred p] :
    Fintype.card { x // p x } = ((Finset.univ : Finset α).filter p).card := by
  refine' Fintype.card_of_subtype _ _
  simp

theorem Fintype.card_subtype_or (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // q x }]
    [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } ≤ Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
  convert Fintype.card_le_of_embedding (subtypeOrLeftEmbedding p q)
  rw [Fintype.card_sum]

theorem Fintype.card_subtype_or_disjoint (p q : α → Prop) (h : Disjoint p q) [Fintype { x // p x }]
    [Fintype { x // q x }] [Fintype { x // p x ∨ q x }] :
    Fintype.card { x // p x ∨ q x } = Fintype.card { x // p x } + Fintype.card { x // q x } := by
  classical
  convert Fintype.card_congr (subtypeOrEquiv p q h)
  simp

@[simp]
theorem Fintype.card_subtype_compl [Fintype α] (p : α → Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] :
    Fintype.card { x // ¬p x } = Fintype.card α - Fintype.card { x // p x } := by
  classical
  rw [Fintype.card_of_subtype (Set.toFinset (pᶜ)), Set.to_finset_compl p, Finset.card_compl,
      Fintype.card_of_subtype (Set.toFinset p)] <;>
    intro <;> simp only [← Set.mem_to_finset, ← Set.mem_compl_eq] <;> rfl

theorem Fintype.card_subtype_mono (p q : α → Prop) (h : p ≤ q) [Fintype { x // p x }] [Fintype { x // q x }] :
    Fintype.card { x // p x } ≤ Fintype.card { x // q x } :=
  Fintype.card_le_of_embedding (Subtype.impEmbedding _ _ h)

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
theorem Fintype.card_compl_eq_card_compl [Fintype α] (p q : α → Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }]
    [Fintype { x // q x }] [Fintype { x // ¬q x }] (h : Fintype.card { x // p x } = Fintype.card { x // q x }) :
    Fintype.card { x // ¬p x } = Fintype.card { x // ¬q x } := by
  simp only [← Fintype.card_subtype_compl, ← h]

theorem Fintype.card_quotient_le [Fintype α] (s : Setoidₓ α) [DecidableRel ((· ≈ ·) : α → α → Prop)] :
    Fintype.card (Quotientₓ s) ≤ Fintype.card α :=
  Fintype.card_le_of_surjective _ (surjective_quotient_mk _)

theorem Fintype.card_quotient_lt [Fintype α] {s : Setoidₓ α} [DecidableRel ((· ≈ ·) : α → α → Prop)] {x y : α}
    (h1 : x ≠ y) (h2 : x ≈ y) : Fintype.card (Quotientₓ s) < Fintype.card α :=
  (Fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _)) fun w => h1 (w <| Quotientₓ.eq.mpr h2)

instance PSigma.fintype {α : Type _} {β : α → Type _} [Fintype α] [∀ a, Fintype (β a)] : Fintype (Σ'a, β a) :=
  Fintype.ofEquiv _ (Equivₓ.psigmaEquivSigma _).symm

instance PSigma.fintypePropLeft {α : Prop} {β : α → Type _} [Decidable α] [∀ a, Fintype (β a)] : Fintype (Σ'a, β a) :=
  if h : α then Fintype.ofEquiv (β h) ⟨fun x => ⟨h, x⟩, PSigma.snd, fun _ => rfl, fun ⟨_, _⟩ => rfl⟩
  else ⟨∅, fun x => h x.1⟩

instance PSigma.fintypePropRight {α : Type _} {β : α → Prop} [∀ a, Decidable (β a)] [Fintype α] : Fintype (Σ'a, β a) :=
  Fintype.ofEquiv { a // β a } ⟨fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => ⟨x, y⟩, fun ⟨x, y⟩ => rfl, fun ⟨x, y⟩ => rfl⟩

instance PSigma.fintypePropProp {α : Prop} {β : α → Prop} [Decidable α] [∀ a, Decidable (β a)] : Fintype (Σ'a, β a) :=
  if h : ∃ a, β a then
    ⟨{⟨h.fst, h.snd⟩}, fun ⟨_, _⟩ => by
      simp ⟩
  else ⟨∅, fun ⟨x, y⟩ => h ⟨x, y⟩⟩

instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).Powerset.map ⟨coe, coe_injective⟩, fun s => by
    classical
    refine' mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩
    apply (coe_filter _ _).trans
    rw [coe_univ, Set.sep_univ]
    rfl⟩

@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)

instance pfunFintype (p : Prop) [Decidable p] (α : p → Type _) [∀ hp, Fintype (α hp)] : Fintype (∀ hp : p, α hp) :=
  if hp : p then Fintype.ofEquiv (α hp) ⟨fun a _ => a, fun f => f hp, fun _ => rfl, fun _ => rfl⟩
  else
    ⟨singleton fun h => (hp h).elim, by
      simp [← hp, ← Function.funext_iffₓ]⟩

@[simp]
theorem Finset.univ_pi_univ {α : Type _} {β : α → Type _} [DecidableEq α] [Fintype α] [∀ a, Fintype (β a)] :
    (Finset.univ.pi fun a : α => (Finset.univ : Finset (β a))) = Finset.univ := by
  ext
  simp

theorem mem_image_univ_iff_mem_range {α β : Type _} [Fintype α] [DecidableEq β] {f : α → β} {b : β} :
    b ∈ univ.Image f ↔ b ∈ Set.Range f := by
  simp

/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def Quotientₓ.finChoiceAux {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)] :
    ∀ l : List ι,
      (∀, ∀ i ∈ l, ∀, Quotientₓ (S i)) →
        @Quotientₓ (∀, ∀ i ∈ l, ∀, α i)
          (by
            infer_instance)
  | [], f => ⟦fun i => False.elim⟧
  | i :: l, f => by
    refine'
      Quotientₓ.liftOn₂ (f i (List.mem_cons_selfₓ _ _))
        (Quotientₓ.finChoiceAux l fun j h => f j (List.mem_cons_of_memₓ _ h)) _ _
    exact fun a l =>
      ⟦fun j h =>
        if e : j = i then by
          rw [e] <;> exact a
        else l _ (h.resolve_left e)⟧
    refine' fun a₁ l₁ a₂ l₂ h₁ h₂ => Quotientₓ.sound fun j h => _
    by_cases' e : j = i <;> simp [← e]
    · subst j
      exact h₁
      
    · exact h₂ _ _
      

theorem Quotientₓ.fin_choice_aux_eq {ι : Type _} [DecidableEq ι] {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)] :
    ∀ (l : List ι) (f : ∀, ∀ i ∈ l, ∀, α i), (Quotientₓ.finChoiceAux l fun i h => ⟦f i h⟧) = ⟦f⟧
  | [], f => Quotientₓ.sound fun i h => h.elim
  | i :: l, f => by
    simp [← Quotientₓ.finChoiceAux, ← Quotientₓ.fin_choice_aux_eq l]
    refine' Quotientₓ.sound fun j h => _
    by_cases' e : j = i <;> simp [← e]
    subst j
    rfl

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def Quotientₓ.finChoice {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _} [S : ∀ i, Setoidₓ (α i)]
    (f : ∀ i, Quotientₓ (S i)) :
    @Quotientₓ (∀ i, α i)
      (by
        infer_instance) :=
  Quotientₓ.liftOn
    (@Quotientₓ.recOn _ _
      (fun l : Multiset ι =>
        @Quotientₓ (∀, ∀ i ∈ l, ∀, α i)
          (by
            infer_instance))
      Finset.univ.1 (fun l => Quotientₓ.finChoiceAux l fun i _ => f i) fun a b h => by
      have := fun a => Quotientₓ.fin_choice_aux_eq a fun i h => Quotientₓ.out (f i)
      simp [← Quotientₓ.out_eq] at this
      simp [← this]
      let g := fun a : Multiset ι => ⟦fun (i : ι) (h : i ∈ a) => Quotientₓ.out (f i)⟧
      refine' eq_of_heq ((eq_rec_heq _ _).trans (_ : HEq (g a) (g b)))
      congr 1
      exact Quotientₓ.sound h)
    (fun f => ⟦fun i => f i (Finset.mem_univ _)⟧) fun a b h => Quotientₓ.sound fun i => h _ _

theorem Quotientₓ.fin_choice_eq {ι : Type _} [DecidableEq ι] [Fintype ι] {α : ι → Type _} [∀ i, Setoidₓ (α i)]
    (f : ∀ i, α i) : (Quotientₓ.finChoice fun i => ⟦f i⟧) = ⟦f⟧ := by
  let q
  swap
  change Quotientₓ.liftOn q _ _ = _
  have : q = ⟦fun i h => f i⟧ := by
    dsimp' [← q]
    exact Quotientₓ.induction_on (@Finset.univ ι _).1 fun l => Quotientₓ.fin_choice_aux_eq _ _
  simp [← this]
  exact Setoidₓ.refl _

section Equivₓ

open List Equivₓ Equivₓ.Perm

variable [DecidableEq α] [DecidableEq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def permsOfList : List α → List (Perm α)
  | [] => [1]
  | a :: l => permsOfList l ++ l.bind fun b => (permsOfList l).map fun f => swap a b * f

theorem length_perms_of_list : ∀ l : List α, length (permsOfList l) = l.length !
  | [] => rfl
  | a :: l => by
    rw [length_cons, Nat.factorial_succ]
    simp [← permsOfList, ← length_bind, ← length_perms_of_list, ← Function.comp, ← Nat.succ_mul]
    cc

theorem mem_perms_of_list_of_mem {l : List α} {f : Perm α} (h : ∀ x, f x ≠ x → x ∈ l) : f ∈ permsOfList l := by
  induction' l with a l IH generalizing f h
  · exact List.mem_singletonₓ.2 (Equivₓ.ext fun x => Decidable.by_contradiction <| h _)
    
  by_cases' hfa : f a = a
  · refine' mem_append_left _ (IH fun x hx => mem_of_ne_of_mem _ (h x hx))
    rintro rfl
    exact hx hfa
    
  have hfa' : f (f a) ≠ f a := mt (fun h => f.injective h) hfa
  have : ∀ x : α, (swap a (f a) * f) x ≠ x → x ∈ l := by
    intro x hx
    have hxa : x ≠ a := by
      rintro rfl
      apply hx
      simp only [← mul_apply, ← swap_apply_right]
    refine' List.mem_of_ne_of_memₓ hxa (h x fun h => _)
    simp only [← h, ← mul_apply, ← swap_apply_def, ← mul_apply, ← Ne.def, ← apply_eq_iff_eq] at hx <;> split_ifs  at hx
    exacts[hxa (h.symm.trans h_1), hx h]
  suffices f ∈ permsOfList l ∨ ∃ b ∈ l, ∃ g ∈ permsOfList l, swap a b * g = f by
    simpa only [← permsOfList, ← exists_prop, ← List.mem_mapₓ, ← mem_append, ← List.mem_bindₓ]
  refine' or_iff_not_imp_left.2 fun hfl => ⟨f a, _, swap a (f a) * f, IH this, _⟩
  · exact mem_of_ne_of_mem hfa (h _ hfa')
    
  · rw [← mul_assoc, mul_def (swap a (f a)) (swap a (f a)), swap_swap, ← perm.one_def, one_mulₓ]
    

theorem mem_of_mem_perms_of_list : ∀ {l : List α} {f : Perm α}, f ∈ permsOfList l → ∀ {x}, f x ≠ x → x ∈ l
  | [], f, h => by
    have : f = 1 := by
      simpa [← permsOfList] using h
    rw [this] <;> simp
  | a :: l, f, h =>
    (mem_appendₓ.1 h).elim (fun h x hx => mem_cons_of_memₓ _ (mem_of_mem_perms_of_list h hx)) fun h x hx =>
      let ⟨y, hy, hy'⟩ := List.mem_bindₓ.1 h
      let ⟨g, hg₁, hg₂⟩ := List.mem_mapₓ.1 hy'
      if hxa : x = a then by
        simp [← hxa]
      else
        if hxy : x = y then
          mem_cons_of_memₓ _ <| by
            rwa [hxy]
        else
          mem_cons_of_memₓ _ <|
            mem_of_mem_perms_of_list hg₁ <| by
              rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def] <;>
                split_ifs <;> [exact Ne.symm hxy, exact Ne.symm hxa, exact hx]

theorem mem_perms_of_list_iff {l : List α} {f : Perm α} : f ∈ permsOfList l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
  ⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩

theorem nodup_perms_of_list : ∀ {l : List α} (hl : l.Nodup), (permsOfList l).Nodup
  | [], hl => by
    simp [← permsOfList]
  | a :: l, hl => by
    have hl' : l.Nodup := hl.of_cons
    have hln' : (permsOfList l).Nodup := nodup_perms_of_list hl'
    have hmeml : ∀ {f : Perm α}, f ∈ permsOfList l → f a = a := fun f hf =>
      not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1)
    rw [permsOfList, List.nodup_append, List.nodup_bind, pairwise_iff_nth_le] <;>
      exact
        ⟨hln',
          ⟨fun _ _ => hln'.map fun _ _ => mul_left_cancelₓ, fun i j hj hij x hx₁ hx₂ =>
            let ⟨f, hf⟩ := List.mem_mapₓ.1 hx₁
            let ⟨g, hg⟩ := List.mem_mapₓ.1 hx₂
            have hix : x a = nth_le l i (lt_transₓ hij hj) := by
              rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left]
            have hiy : x a = nth_le l j hj := by
              rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left]
            (absurd (hf.2.trans hg.2.symm)) fun h =>
              ne_of_ltₓ hij <|
                nodup_iff_nth_le_inj.1 hl' i j (lt_transₓ hij hj) hj <| by
                  rw [← hix, hiy]⟩,
          fun f hf₁ hf₂ =>
          let ⟨x, hx, hx'⟩ := List.mem_bindₓ.1 hf₂
          let ⟨g, hg⟩ := List.mem_mapₓ.1 hx'
          have hgxa : g⁻¹ x = a :=
            f.Injective <| by
              rw [hmeml hf₁, ← hg.2] <;> simp
          have hxa : x ≠ a := fun h => (List.nodup_cons.1 hl).1 (h ▸ hx)
          (List.nodup_cons.1 hl).1 <|
            hgxa ▸
              mem_of_mem_perms_of_list hg.1
                (by
                  rwa [apply_inv_self, hgxa])⟩

/-- Given a finset, produce the finset of all permutations of its elements. -/
def permsOfFinset (s : Finset α) : Finset (Perm α) :=
  Quotientₓ.hrecOn s.1 (fun l hl => ⟨permsOfList l, nodup_perms_of_list hl⟩)
    (fun a b hab =>
      hfunext (congr_arg _ (Quotientₓ.sound hab)) fun ha hb _ =>
        heq_of_eq <|
          Finset.ext <| by
            simp [← mem_perms_of_list_iff, ← hab.mem_iff])
    s.2

theorem mem_perms_of_finset_iff : ∀ {s : Finset α} {f : Perm α}, f ∈ permsOfFinset s ↔ ∀ {x}, f x ≠ x → x ∈ s := by
  rintro ⟨⟨l⟩, hs⟩ f <;> exact mem_perms_of_list_iff

theorem card_perms_of_finset : ∀ s : Finset α, (permsOfFinset s).card = s.card ! := by
  rintro ⟨⟨l⟩, hs⟩ <;> exact length_perms_of_list l

/-- The collection of permutations of a fintype is a fintype. -/
def fintypePerm [Fintype α] : Fintype (Perm α) :=
  ⟨permsOfFinset (@Finset.univ α _), by
    simp [← mem_perms_of_finset_iff]⟩

instance [Fintype α] [Fintype β] : Fintype (α ≃ β) :=
  if h : Fintype.card β = Fintype.card α then
    Trunc.recOnSubsingleton (Fintype.truncEquivFin α) fun eα =>
      Trunc.recOnSubsingleton (Fintype.truncEquivFin β) fun eβ =>
        @Fintype.ofEquiv _ (Perm α) fintypePerm
          (equivCongr (Equivₓ.refl α) (eα.trans (Eq.recOnₓ h eβ.symm)) : α ≃ α ≃ (α ≃ β))
  else ⟨∅, fun x => False.elim (h (Fintype.card_eq.2 ⟨x.symm⟩))⟩

theorem Fintype.card_perm [Fintype α] : Fintype.card (Perm α) = (Fintype.card α)! :=
  Subsingleton.elimₓ (@fintypePerm α _ _) (@Equivₓ.fintype α α _ _ _ _) ▸ card_perms_of_finset _

theorem Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) : Fintype.card (α ≃ β) = (Fintype.card α)! :=
  Fintype.card_congr (equivCongr (Equivₓ.refl α) e) ▸ Fintype.card_perm

theorem univ_eq_singleton_of_card_one {α} [Fintype α] (x : α) (h : Fintype.card α = 1) : (univ : Finset α) = {x} := by
  symm
  apply eq_of_subset_of_card_le (subset_univ {x})
  apply le_of_eqₓ
  simp [← h, ← Finset.card_univ]

end Equivₓ

namespace Fintype

section Choose

open Fintype Equivₓ

variable [Fintype α] (p : α → Prop) [DecidablePred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a : α, p a) : { a // p a } :=
  ⟨Finset.choose p univ
      (by
        simp <;> exact hp),
    Finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α :=
  chooseX p hp

theorem choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
  (chooseX p hp).property

@[simp]
theorem choose_subtype_eq {α : Type _} (p : α → Prop) [Fintype { a : α // p a }] [DecidableEq α] (x : { a : α // p a })
    (h : ∃! a : { a // p a }, (a : α) = x :=
      ⟨x, rfl, fun y hy => by
        simpa [← Subtype.ext_iff] using hy⟩) :
    Fintype.choose (fun y : { a : α // p a } => (y : α) = x) h = x := by
  rw [Subtype.ext_iff, Fintype.choose_spec (fun y : { a : α // p a } => (y : α) = x) _]

end Choose

section BijectionInverse

open Function

variable [Fintype α] [DecidableEq β] {f : α → β}

/-- `bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bijInv (f_bij : Bijective f) (b : β) : α :=
  Fintype.choose (fun a => f a = b)
    (by
      rcases f_bij.right b with ⟨a', fa_eq_b⟩
      rw [← fa_eq_b]
      exact ⟨a', ⟨rfl, fun a h => f_bij.left h⟩⟩)

theorem left_inverse_bij_inv (f_bij : Bijective f) : LeftInverse (bijInv f_bij) f := fun a =>
  f_bij.left (choose_spec (fun a' => f a' = f a) _)

theorem right_inverse_bij_inv (f_bij : Bijective f) : RightInverse (bijInv f_bij) f := fun b =>
  choose_spec (fun a' => f a' = b) _

theorem bijective_bij_inv (f_bij : Bijective f) : Bijective (bijInv f_bij) :=
  ⟨(right_inverse_bij_inv _).Injective, (left_inverse_bij_inv _).Surjective⟩

end BijectionInverse

theorem well_founded_of_trans_of_irrefl [Fintype α] (r : α → α → Prop) [IsTrans α r] [IsIrrefl α r] : WellFounded r :=
  by
  classical <;>
    exact
      have : ∀ x y, r x y → (univ.filter fun z => r z x).card < (univ.filter fun z => r z y).card := fun x y hxy =>
        Finset.card_lt_card <| by
          simp only [← finset.lt_iff_ssubset.symm, ← lt_iff_le_not_leₓ, ← Finset.le_iff_subset, ← Finset.subset_iff, ←
              mem_filter, ← true_andₓ, ← mem_univ, ← hxy] <;>
            exact ⟨fun z hzx => trans hzx hxy, not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩
      Subrelation.wfₓ this (measure_wf _)

theorem Preorder.well_founded_lt [Fintype α] [Preorderₓ α] : WellFounded ((· < ·) : α → α → Prop) :=
  well_founded_of_trans_of_irrefl _

theorem Preorder.well_founded_gt [Fintype α] [Preorderₓ α] : WellFounded ((· > ·) : α → α → Prop) :=
  well_founded_of_trans_of_irrefl _

@[instance]
theorem LinearOrder.is_well_order_lt [Fintype α] [LinearOrderₓ α] : IsWellOrder α (· < ·) :=
  { wf := Preorder.well_founded_lt }

@[instance]
theorem LinearOrder.is_well_order_gt [Fintype α] [LinearOrderₓ α] : IsWellOrder α (· > ·) :=
  { wf := Preorder.well_founded_gt }

end Fintype

/-- A type is said to be infinite if it has no fintype instance.
  Note that `infinite α` is equivalent to `is_empty (fintype α)`. -/
class Infinite (α : Type _) : Prop where
  not_fintype : Fintype α → False

theorem not_fintype (α : Type _) [h1 : Infinite α] [h2 : Fintype α] : False :=
  Infinite.not_fintype h2

protected theorem Fintype.false {α : Type _} [Infinite α] (h : Fintype α) : False :=
  not_fintype α

protected theorem Infinite.false {α : Type _} [Fintype α] (h : Infinite α) : False :=
  not_fintype α

@[simp]
theorem is_empty_fintype {α : Type _} : IsEmpty (Fintype α) ↔ Infinite α :=
  ⟨fun ⟨x⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨x⟩⟩

/-- A non-infinite type is a fintype. -/
noncomputable def fintypeOfNotInfinite {α : Type _} (h : ¬Infinite α) : Fintype α :=
  Nonempty.some <| by
    rwa [← not_is_empty_iff, is_empty_fintype]

section

open Classical

/-- Any type is (classically) either a `fintype`, or `infinite`.

One can obtain the relevant typeclasses via `cases fintype_or_infinite α; resetI`.
-/
noncomputable def fintypeOrInfinite (α : Type _) : PSum (Fintype α) (Infinite α) :=
  if h : Infinite α then PSum.inr h else PSum.inl (fintypeOfNotInfinite h)

end

theorem Finset.exists_minimal {α : Type _} [Preorderₓ α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀, ∀ x ∈ s, ∀, ¬x < m := by
  obtain ⟨c, hcs : c ∈ s⟩ := h
  have : WellFounded (@LT.lt { x // x ∈ s } _) := Fintype.well_founded_of_trans_of_irrefl _
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min Set.Univ ⟨⟨c, hcs⟩, trivialₓ⟩
  exact ⟨m, hms, fun x hx hxm => H ⟨x, hx⟩ trivialₓ hxm⟩

theorem Finset.exists_maximal {α : Type _} [Preorderₓ α] (s : Finset α) (h : s.Nonempty) :
    ∃ m ∈ s, ∀, ∀ x ∈ s, ∀, ¬m < x :=
  @Finset.exists_minimal αᵒᵈ _ s h

namespace Infinite

theorem exists_not_mem_finset [Infinite α] (s : Finset α) : ∃ x, x ∉ s :=
  not_forall.1 fun h => Fintype.false ⟨s, h⟩

-- see Note [lower instance priority]
instance (priority := 100) (α : Type _) [H : Infinite α] : Nontrivial α :=
  ⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : Finset α)
    let ⟨y, hy⟩ := exists_not_mem_finset ({x} : Finset α)
    ⟨y, x, by
      simpa only [← mem_singleton] using hy⟩⟩

protected theorem nonempty (α : Type _) [Infinite α] : Nonempty α := by
  infer_instance

theorem of_injective [Infinite β] (f : β → α) (hf : Injective f) : Infinite α :=
  ⟨fun I => (Fintype.ofInjective f hf).False⟩

theorem of_surjective [Infinite β] (f : α → β) (hf : Surjective f) : Infinite α :=
  ⟨fun I => by
    classical
    exact (Fintype.ofSurjective f hf).False⟩

end Infinite

instance : Infinite ℕ :=
  ⟨fun ⟨s, hs⟩ => Finset.not_mem_range_self <| s.subset_range_sup_succ (hs _)⟩

instance : Infinite ℤ :=
  Infinite.of_injective Int.ofNat fun _ _ => Int.ofNat.injₓ

instance Infinite.set [Infinite α] : Infinite (Set α) :=
  Infinite.of_injective singleton fun a b => Set.singleton_eq_singleton_iff.1

instance [Infinite α] : Infinite (Finset α) :=
  Infinite.of_injective singleton Finset.singleton_injective

instance [Nonempty α] : Infinite (Multiset α) := by
  inhabit α
  exact Infinite.of_injective (Multiset.repeat default) (Multiset.repeat_injective _)

instance [Nonempty α] : Infinite (List α) :=
  Infinite.of_surjective (coe : List α → Multiset α) (surjective_quot_mk _)

instance [Infinite α] : Infinite (Option α) :=
  Infinite.of_injective some (Option.some_injective α)

instance Sum.infinite_of_left [Infinite α] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inl Sum.inl_injective

instance Sum.infinite_of_right [Infinite β] : Infinite (Sum α β) :=
  Infinite.of_injective Sum.inr Sum.inr_injective

@[simp]
theorem infinite_sum : Infinite (Sum α β) ↔ Infinite α ∨ Infinite β := by
  refine' ⟨fun H => _, fun H => H.elim (@Sum.infinite_of_left α β) (@Sum.infinite_of_right α β)⟩
  contrapose! H
  have := fintypeOfNotInfinite H.1
  have := fintypeOfNotInfinite H.2
  exact Infinite.false

instance Prod.infinite_of_right [Nonempty α] [Infinite β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.snd Prod.snd_surjective

instance Prod.infinite_of_left [Infinite α] [Nonempty β] : Infinite (α × β) :=
  Infinite.of_surjective Prod.fst Prod.fst_surjectiveₓ

@[simp]
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β := by
  refine'
    ⟨fun H => _, fun H => H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [And.comm]
  contrapose! H
  intro H'
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  have := fintypeOfNotInfinite (H.1 ⟨b⟩)
  have := fintypeOfNotInfinite (H.2 ⟨a⟩)
  exact H'.false

namespace Infinite

private noncomputable def nat_embedding_aux (α : Type _) [Infinite α] : ℕ → α
  | n => by
    let this := Classical.decEq α <;>
      exact
        Classical.some
          (exists_not_mem_finset
            ((Multiset.range n).pmap (fun m (hm : m < n) => nat_embedding_aux m) fun _ =>
                Multiset.mem_range.1).toFinset)

private theorem nat_embedding_aux_injective (α : Type _) [Infinite α] : Function.Injective (natEmbeddingAux α) := by
  rintro m n h
  let this := Classical.decEq α
  wlog hmlen : m ≤ n using m n
  by_contra hmn
  have hmn : m < n := lt_of_le_of_neₓ hmlen hmn
  refine'
    (Classical.some_spec
        (exists_not_mem_finset
          ((Multiset.range n).pmap (fun m (hm : m < n) => nat_embedding_aux α m) fun _ =>
              Multiset.mem_range.1).toFinset))
      _
  refine' Multiset.mem_to_finset.2 (Multiset.mem_pmap.2 ⟨m, Multiset.mem_range.2 hmn, _⟩)
  rw [h, nat_embedding_aux]

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def natEmbedding (α : Type _) [Infinite α] : ℕ ↪ α :=
  ⟨_, nat_embedding_aux_injective α⟩

theorem exists_subset_card_eq (α : Type _) [Infinite α] (n : ℕ) : ∃ s : Finset α, s.card = n :=
  ⟨(range n).map (natEmbedding α), by
    rw [card_map, card_range]⟩

end Infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintypeOfFinsetCardLe {ι : Type _} (n : ℕ) (w : ∀ s : Finset ι, s.card ≤ n) : Fintype ι := by
  apply fintypeOfNotInfinite
  intro i
  obtain ⟨s, c⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  specialize w s
  rw [c] at w
  exact Nat.not_succ_le_selfₓ n w

theorem not_injective_infinite_fintype [Infinite α] [Fintype β] (f : α → β) : ¬Injective f := fun hf =>
  (Fintype.ofInjective f hf).False

/-- The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `fintype.exists_infinite_fiber`.
-/
theorem Fintype.exists_ne_map_eq_of_infinite [Infinite α] [Fintype β] (f : α → β) : ∃ x y : α, x ≠ y ∧ f x = f y := by
  classical
  by_contra' hf
  apply not_injective_infinite_fintype f
  intro x y
  contrapose
  apply hf

-- ./././Mathport/Syntax/Translate/Basic.lean:1389:38: unsupported irreducible non-definition
-- irreducible due to this conversation on Zulip:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/
-- topic/.60simp.60.20ignoring.20lemmas.3F/near/241824115
irreducible_def Function.Embedding.is_empty {α β} [Infinite α] [Fintype β] : IsEmpty (α ↪ β) :=
  ⟨fun f =>
    let ⟨x, y, Ne, feq⟩ := Fintype.exists_ne_map_eq_of_infinite f
    Ne <| f.Injective feq⟩

noncomputable instance (priority := 100) Function.Embedding.fintype' {α β : Type _} [Fintype β] : Fintype (α ↪ β) := by
  cases fintypeOrInfinite α <;> infer_instance

/-- The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `fintype.exists_ne_map_eq_of_infinite`
-/
theorem Fintype.exists_infinite_fiber [Infinite α] [Fintype β] (f : α → β) : ∃ y : β, Infinite (f ⁻¹' {y}) := by
  classical
  by_contra' hf
  have := fun y => fintypeOfNotInfinite <| hf y
  let key : Fintype α :=
    { elems := univ.bUnion fun y : β => (f ⁻¹' {y}).toFinset,
      complete := by
        simp }
  exact key.false

theorem not_surjective_fintype_infinite [Fintype α] [Infinite β] (f : α → β) : ¬Surjective f := fun hf : Surjective f =>
  have H : Infinite α := Infinite.of_surjective f hf
  not_fintype α

section Trunc

/-- For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def truncOfMultisetExistsMem {α} (s : Multiset α) : (∃ x, x ∈ s) → Trunc α :=
  (Quotientₓ.recOnSubsingleton s) fun l h =>
    match l, h with
    | [], _ =>
      False.elim
        (by
          tauto)
    | a :: _, _ => Trunc.mk a

/-- A `nonempty` `fintype` constructively contains an element.
-/
def truncOfNonemptyFintype (α) [Nonempty α] [Fintype α] : Trunc α :=
  truncOfMultisetExistsMem Finset.univ.val
    (by
      simp )

/-- A `fintype` with positive cardinality constructively contains an element.
-/
def truncOfCardPos {α} [Fintype α] (h : 0 < Fintype.card α) : Trunc α := by
  let this := fintype.card_pos_iff.mp h
  exact truncOfNonemptyFintype α

/-- By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def truncSigmaOfExists {α} [Fintype α] {P : α → Prop} [DecidablePred P] (h : ∃ a, P a) : Trunc (Σ'a, P a) :=
  @truncOfNonemptyFintype (Σ'a, P a) ((Exists.elim h) fun a ha => ⟨⟨a, ha⟩⟩) _

end Trunc

namespace Multiset

variable [Fintype α] [DecidableEq α]

@[simp]
theorem count_univ (a : α) : count a Finset.univ.val = 1 :=
  count_eq_one_of_mem Finset.univ.Nodup (Finset.mem_univ _)

end Multiset

namespace Fintype

/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def truncRecEmptyOption {P : Type u → Sort v} (of_equiv : ∀ {α β}, α ≃ β → P α → P β) (h_empty : P Pempty)
    (h_option : ∀ {α} [Fintype α] [DecidableEq α], P α → P (Option α)) (α : Type u) [Fintype α] [DecidableEq α] :
    Trunc (P α) := by
  suffices ∀ n : ℕ, Trunc (P (ULift <| Finₓ n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (equiv.ulift.trans e.symm) h
  intro n
  induction' n with n ih
  · have : card Pempty = card (ULift (Finₓ 0)) := by
      simp only [← card_fin, ← card_pempty, ← card_ulift]
    apply Trunc.bind (trunc_equiv_of_card_eq this)
    intro e
    apply Trunc.mk
    refine' of_equiv e h_empty
    
  · have : card (Option (ULift (Finₓ n))) = card (ULift (Finₓ n.succ)) := by
      simp only [← card_fin, ← card_option, ← card_ulift]
    apply Trunc.bind (trunc_equiv_of_card_eq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    refine' of_equiv e (h_option ih)
    

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_eliminator]
theorem induction_empty_option' {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›) (h_empty : P Pempty)
    (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u) [Fintype α] : P α := by
  obtain ⟨p⟩ :=
    @trunc_rec_empty_option (fun α => ∀ h, @P α h) (fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      (fun _i => by
        convert h_empty)
      _ α _ (Classical.decEq α)
  · exact p _
    
  · rintro α hα - Pα hα'
    skip
    convert h_option α (Pα _)
    

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
theorem induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β) (h_empty : P Pempty)
    (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u) [Fintype α] : P α := by
  refine' induction_empty_option' _ _ _ α
  exacts[fun α β _ => of_equiv, h_empty, @h_option]

end Fintype

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seqOfForallFinsetExistsAux {α : Type _} [DecidableEq α] (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, ∃ y, (∀, ∀ x ∈ s, ∀, P x) → P y ∧ ∀, ∀ x ∈ s, ∀, r x y) : ℕ → α
  | n =>
    Classical.some (h (Finset.image (fun i : Finₓ n => seqOfForallFinsetExistsAux i) (Finset.univ : Finset (Finₓ n))))

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists {α : Type _} (P : α → Prop) (r : α → α → Prop)
    (h : ∀ s : Finset α, (∀, ∀ x ∈ s, ∀, P x) → ∃ y, P y ∧ ∀, ∀ x ∈ s, ∀, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m < n → r (f m) (f n) := by
  classical
  have : Nonempty α := by
    rcases h ∅
        (by
          simp ) with
      ⟨y, hy⟩
    exact ⟨y⟩
  choose! F hF using h
  have h' : ∀ s : Finset α, ∃ y, (∀, ∀ x ∈ s, ∀, P x) → P y ∧ ∀, ∀ x ∈ s, ∀, r x y := fun s => ⟨F s, hF s⟩
  set f := seqOfForallFinsetExistsAux P r h' with hf
  have A : ∀ n : ℕ, P (f n) := by
    intro n
    induction' n using Nat.strong_induction_onₓ with n IH
    have IH' : ∀ x : Finₓ n, P (f x) := fun n => IH n.1 n.2
    rw [hf, seqOfForallFinsetExistsAux]
    exact
      (Classical.some_spec (h' (Finset.image (fun i : Finₓ n => f i) (Finset.univ : Finset (Finₓ n))))
          (by
            simp [← IH'])).1
  refine' ⟨f, A, fun m n hmn => _⟩
  nth_rw 1[hf]
  rw [seqOfForallFinsetExistsAux]
  apply
    (Classical.some_spec (h' (Finset.image (fun i : Finₓ n => f i) (Finset.univ : Finset (Finₓ n))))
        (by
          simp [← A])).2
  exact Finset.mem_image.2 ⟨⟨m, hmn⟩, Finset.mem_univ _, rfl⟩

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
theorem exists_seq_of_forall_finset_exists' {α : Type _} (P : α → Prop) (r : α → α → Prop) [IsSymm α r]
    (h : ∀ s : Finset α, (∀, ∀ x ∈ s, ∀, P x) → ∃ y, P y ∧ ∀, ∀ x ∈ s, ∀, r x y) :
    ∃ f : ℕ → α, (∀ n, P (f n)) ∧ ∀ m n, m ≠ n → r (f m) (f n) := by
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩
  refine' ⟨f, hf, fun m n hmn => _⟩
  rcases lt_trichotomyₓ m n with (h | rfl | h)
  · exact hf' m n h
    
  · exact (hmn rfl).elim
    
  · apply symm
    exact hf' n m h
    

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `fintype.card`).

The major premise is `fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_eliminator]
theorem Fintype.induction_subsingleton_or_nontrivial {P : ∀ (α) [Fintype α], Prop} (α : Type _) [Fintype α]
    (hbase : ∀ (α) [Fintype α] [Subsingleton α], P α)
    (hstep :
      ∀ (α) [Fintype α] [Nontrivial α], ∀ ih : ∀ (β) [Fintype β], ∀ h : Fintype.card β < Fintype.card α, P β, P α) :
    P α := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n := ⟨Fintype.card α, rfl⟩
  induction' n using Nat.strong_induction_onₓ with n ih generalizing α
  cases' subsingleton_or_nontrivial α with hsing hnontriv
  · apply hbase
    
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Fintype.card β) hlt _ rfl
    

