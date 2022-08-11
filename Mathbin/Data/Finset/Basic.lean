/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathbin.Data.Int.Basic
import Mathbin.Data.Multiset.FinsetOps
import Mathbin.Tactic.Apply
import Mathbin.Tactic.Monotonicity.Default
import Mathbin.Tactic.NthRewrite.Default

/-!
# Finite sets

Terms of type `finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `finset α` is defined as a structure with 2 fields:

  1. `val` is a `multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `list` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i in (s : finset α), f i`;
  2. `∏ i in (s : finset α), f i`.

Lean refers to these operations as `big_operator`s.
More information can be found in `algebra.big_operators.basic`.

Finsets are directly used to define fintypes in Lean.
A `fintype α` instance for a type `α` consists of
a universal `finset α` containing every term of `α`, called `univ`. See `data.fintype.basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `data.fintype.basic`.

`finset.card`, the size of a finset is defined in `data.finset.card`. This is then used to define
`fintype.card`, the size of a type.

## Main declarations

### Main definitions

* `finset`: Defines a type for the finite subsets of `α`.
  Constructing a `finset` requires two pieces of data: `val`, a `multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `finset.has_mem`: Defines membership `a ∈ (s : finset α)`.
* `finset.has_coe`: Provides a coercion `s : finset α` to `s : set α`.
* `finset.has_coe_to_sort`: Coerce `s : finset α` to the type of all `x ∈ s`.
* `finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `finset α`,
  then it holds for the finset obtained by inserting a new element.
* `finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.has_subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.has_union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `finset.sup`/`finset.bUnion` for finite unions.
* `finset.has_inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `finset.inf` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `finset.has_union`: see "The lattice structure on subsets of finsets"
* `finset.has_inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.has_sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `data.finset.pi`.
* `finset.bUnion`: Finite unions of finsets; given an indexing function `f : α → finset β` and a
  `s : finset α`, `s.bUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `finset.bInter`: TODO: Implemement finite intersections.

### Maps constructed using finsets

* `finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
  to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `finset.nonempty`: A finset is nonempty if it has elements.
  This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `data.equiv` files describe a general type of equivalence, so look in there for any lemmas.
  There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/


open Multiset Subtype Nat Function

universe u

variable {α : Type _} {β : Type _} {γ : Type _}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure Finset (α : Type _) where
  val : Multiset α
  Nodup : Nodup val

namespace Finset

theorem eq_of_veq : ∀ {s t : Finset α}, s.1 = t.1 → s = t
  | ⟨s, _⟩, ⟨t, _⟩, rfl => rfl

@[simp]
theorem val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t :=
  ⟨eq_of_veq, congr_arg _⟩

@[simp]
theorem dedup_eq_self [DecidableEq α] (s : Finset α) : dedup s.1 = s.1 :=
  s.2.dedup

instance hasDecidableEq [DecidableEq α] : DecidableEq (Finset α)
  | s₁, s₂ => decidableOfIff _ val_inj

/-! ### membership -/


instance : HasMem α (Finset α) :=
  ⟨fun a s => a ∈ s.1⟩

theorem mem_def {a : α} {s : Finset α} : a ∈ s ↔ a ∈ s.1 :=
  Iff.rfl

@[simp]
theorem mem_mk {a : α} {s nd} : a ∈ @Finset.mk α s nd ↔ a ∈ s :=
  Iff.rfl

instance decidableMem [h : DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ s) :=
  Multiset.decidableMem _ _

/-! ### set coercion -/


/-- Convert a finset to a set in the natural way. -/
instance : CoeTₓ (Finset α) (Set α) :=
  ⟨fun s => { x | x ∈ s }⟩

@[simp, norm_cast]
theorem mem_coe {a : α} {s : Finset α} : a ∈ (s : Set α) ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem set_of_mem {α} {s : Finset α} : { a | a ∈ s } = s :=
  rfl

@[simp]
theorem coe_mem {s : Finset α} (x : (s : Set α)) : ↑x ∈ s :=
  x.2

@[simp]
theorem mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (s : Set α)) = x :=
  Subtype.coe_eta _ _

instance decidableMem' [DecidableEq α] (a : α) (s : Finset α) : Decidable (a ∈ (s : Set α)) :=
  s.decidableMem _

/-! ### extensionality -/


theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
  val_inj.symm.trans <| s₁.Nodup.ext s₂.Nodup

@[ext]
theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
  ext_iff.2

@[simp, norm_cast]
theorem coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂ :=
  Set.ext_iff.trans ext_iff.symm

theorem coe_injective {α} : Injective (coe : Finset α → Set α) := fun s t => coe_inj.1

/-! ### type coercion -/


/-- Coercion from a finset to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Finset α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

instance PiFinsetCoe.canLift (ι : Type _) (α : ∀ i : ι, Type _) [ne : ∀ i, Nonempty (α i)] (s : Finset ι) :
    CanLift (∀ i : s, α i) (∀ i, α i) :=
  { PiSubtype.canLift ι α (· ∈ s) with coe := fun f i => f i }

instance PiFinsetCoe.canLift' (ι α : Type _) [ne : Nonempty α] (s : Finset ι) : CanLift (s → α) (ι → α) :=
  PiFinsetCoe.canLift ι (fun _ => α) s

instance FinsetCoe.canLift (s : Finset α) : CanLift α s where
  coe := coe
  cond := fun a => a ∈ s
  prf := fun a ha => ⟨⟨a, ha⟩, rfl⟩

@[simp, norm_cast]
theorem coe_sort_coe (s : Finset α) : ((s : Set α) : Sort _) = s :=
  rfl

/-! ### Subset and strict subset relations -/


section Subset

variable {s t : Finset α}

instance : HasSubset (Finset α) :=
  ⟨fun s t => ∀ ⦃a⦄, a ∈ s → a ∈ t⟩

instance : HasSsubset (Finset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

instance : PartialOrderₓ (Finset α) where
  le := (· ⊆ ·)
  lt := (· ⊂ ·)
  le_refl := fun s a => id
  le_trans := fun s t u hst htu a ha => htu <| hst ha
  le_antisymm := fun s t hst hts => ext fun a => ⟨@hst _, @hts _⟩

instance : IsRefl (Finset α) (· ⊆ ·) :=
  LE.le.is_refl

instance : IsTrans (Finset α) (· ⊆ ·) :=
  LE.le.is_trans

instance : IsAntisymm (Finset α) (· ⊆ ·) :=
  LE.le.is_antisymm

instance : IsIrrefl (Finset α) (· ⊂ ·) :=
  LT.lt.is_irrefl

instance : IsTrans (Finset α) (· ⊂ ·) :=
  LT.lt.is_trans

instance : IsAsymm (Finset α) (· ⊂ ·) :=
  LT.lt.is_asymm

instance : IsNonstrictStrictOrder (Finset α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

theorem subset_def : s ⊆ t ↔ s.1 ⊆ t.1 :=
  Iff.rfl

theorem ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬t ⊆ s :=
  Iff.rfl

@[simp]
theorem Subset.refl (s : Finset α) : s ⊆ s :=
  Subset.refl _

protected theorem Subset.rfl {s : Finset α} : s ⊆ s :=
  Subset.refl _

protected theorem subset_of_eq {s t : Finset α} (h : s = t) : s ⊆ t :=
  h ▸ Subset.refl _

theorem Subset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
  subset.trans

theorem Superset.trans {s₁ s₂ s₃ : Finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ := fun h' h => Subset.trans h h'

theorem mem_of_subset {s₁ s₂ : Finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
  mem_of_subset

theorem not_mem_mono {s t : Finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s :=
  mt <| @h _

theorem Subset.antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
  ext fun a => ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : Finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊆ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

@[simp]
theorem val_le_iff {s₁ s₂ : Finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ :=
  le_iff_subset s₁.2

theorem Subset.antisymm_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
  le_antisymm_iffₓ

theorem not_subset (s t : Finset α) : ¬s ⊆ t ↔ ∃ x ∈ s, ¬x ∈ t := by
  simp only [Finset.coe_subset, ← Set.not_subset, ← exists_prop, ← Finset.mem_coe]

@[simp]
theorem le_eq_subset : ((· ≤ ·) : Finset α → Finset α → Prop) = (· ⊆ ·) :=
  rfl

@[simp]
theorem lt_eq_subset : ((· < ·) : Finset α → Finset α → Prop) = (· ⊂ ·) :=
  rfl

theorem le_iff_subset {s₁ s₂ : Finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ :=
  Iff.rfl

theorem lt_iff_ssubset {s₁ s₂ : Finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_ssubset {s₁ s₂ : Finset α} : (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
  show (s₁ : Set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁ by
    simp only [← Set.ssubset_def, ← Finset.coe_subset]

@[simp]
theorem val_lt_iff {s₁ s₂ : Finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
  and_congr val_le_iff <| not_congr val_le_iff

theorem ssubset_iff_subset_ne {s t : Finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne _ _ s t

theorem ssubset_iff_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
  Set.ssubset_iff_of_subset h

theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  Set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  Set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

theorem exists_of_ssubset {s₁ s₂ : Finset α} (h : s₁ ⊂ s₂) : ∃ x ∈ s₂, x ∉ s₁ :=
  Set.exists_of_ssubset h

end Subset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] subset.trans superset.trans

/-! ### Order embedding from `finset α` to `set α` -/


/-- Coercion to `set α` as an `order_embedding`. -/
def coeEmb : Finset α ↪o Set α :=
  ⟨⟨coe, coe_injective⟩, fun s t => coe_subset⟩

@[simp]
theorem coe_coe_emb : ⇑(coeEmb : Finset α ↪o Set α) = coe :=
  rfl

/-! ### Nonempty -/


/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Finset α) : Prop :=
  ∃ x : α, x ∈ s

instance decidableNonempty {s : Finset α} : Decidable s.Nonempty :=
  decidableOfIff (∃ a ∈ s, True) <| by
    simp_rw [exists_prop, and_trueₓ, Finset.Nonempty]

@[simp, norm_cast]
theorem coe_nonempty {s : Finset α} : (s : Set α).Nonempty ↔ s.Nonempty :=
  Iff.rfl

@[simp]
theorem nonempty_coe_sort {s : Finset α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype

alias coe_nonempty ↔ _ nonempty.to_set

theorem Nonempty.bex {s : Finset α} (h : s.Nonempty) : ∃ x : α, x ∈ s :=
  h

theorem Nonempty.mono {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  Set.Nonempty.mono hst hs

theorem Nonempty.forall_const {s : Finset α} (h : s.Nonempty) {p : Prop} : (∀, ∀ x ∈ s, ∀, p) ↔ p :=
  let ⟨x, hx⟩ := h
  ⟨fun h => h x hx, fun h x hx => h⟩

/-! ### empty -/


/-- The empty finset -/
protected def empty : Finset α :=
  ⟨0, nodup_zero⟩

instance : HasEmptyc (Finset α) :=
  ⟨Finset.empty⟩

instance inhabitedFinset : Inhabited (Finset α) :=
  ⟨∅⟩

@[simp]
theorem empty_val : (∅ : Finset α).1 = 0 :=
  rfl

@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : Finset α) :=
  id

@[simp]
theorem not_nonempty_empty : ¬(∅ : Finset α).Nonempty := fun ⟨x, hx⟩ => not_mem_empty x hx

@[simp]
theorem mk_zero : (⟨0, nodup_zero⟩ : Finset α) = ∅ :=
  rfl

theorem ne_empty_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ≠ ∅ := fun e => not_mem_empty a <| e ▸ h

theorem Nonempty.ne_empty {s : Finset α} (h : s.Nonempty) : s ≠ ∅ :=
  (Exists.elim h) fun a => ne_empty_of_mem

@[simp]
theorem empty_subset (s : Finset α) : ∅ ⊆ s :=
  zero_subset _

theorem eq_empty_of_forall_not_mem {s : Finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
  eq_of_veq (eq_zero_of_forall_not_mem H)

theorem eq_empty_iff_forall_not_mem {s : Finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
  ⟨by
    rintro rfl x <;> exact id, fun h => eq_empty_of_forall_not_mem h⟩

@[simp]
theorem val_eq_zero {s : Finset α} : s.1 = 0 ↔ s = ∅ :=
  @val_inj _ s ∅

theorem subset_empty {s : Finset α} : s ⊆ ∅ ↔ s = ∅ :=
  subset_zero.trans val_eq_zero

@[simp]
theorem not_ssubset_empty (s : Finset α) : ¬s ⊂ ∅ := fun h =>
  let ⟨x, he, hs⟩ := exists_of_ssubset h
  he

theorem nonempty_of_ne_empty {s : Finset α} (h : s ≠ ∅) : s.Nonempty :=
  exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : Finset α} : s.Nonempty ↔ s ≠ ∅ :=
  ⟨Nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp]
theorem not_nonempty_iff_eq_empty {s : Finset α} : ¬s.Nonempty ↔ s = ∅ :=
  nonempty_iff_ne_empty.Not.trans not_not

theorem eq_empty_or_nonempty (s : Finset α) : s = ∅ ∨ s.Nonempty :=
  Classical.by_cases Or.inl fun h => Or.inr (nonempty_of_ne_empty h)

@[simp, norm_cast]
theorem coe_empty : ((∅ : Finset α) : Set α) = ∅ :=
  rfl

@[simp, norm_cast]
theorem coe_eq_empty {s : Finset α} : (s : Set α) = ∅ ↔ s = ∅ := by
  rw [← coe_empty, coe_inj]

@[simp]
theorem is_empty_coe_sort {s : Finset α} : IsEmpty ↥s ↔ s = ∅ := by
  simpa using @Set.is_empty_coe_sort α s

/-- A `finset` for an empty type is empty. -/
theorem eq_empty_of_is_empty [IsEmpty α] (s : Finset α) : s = ∅ :=
  Finset.eq_empty_of_forall_not_mem isEmptyElim

/-! ### singleton -/


/-- `{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : HasSingleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  mem_singleton

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h

theorem not_mem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  Or.inl rfl

theorem singleton_injective : Injective (singleton : α → Finset α) := fun a b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

theorem singleton_inj {a b : α} : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff

@[simp]
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty

@[simp, norm_cast]
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} := by
  ext
  simp

@[simp, norm_cast]
theorem coe_eq_singleton {α : Type _} {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by
  rw [← Finset.coe_singleton, Finset.coe_inj]

theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀, ∀ x ∈ s, ∀, x = a := by
  constructor <;> intro t
  rw [t]
  refine' ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
  ext
  rw [Finset.mem_singleton]
  refine' ⟨t.right _, fun r => r.symm ▸ t.left⟩

theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} : s = {a} ↔ s.Nonempty ∧ ∀, ∀ x ∈ s, ∀, x = a := by
  constructor
  · rintro rfl
    simp
    
  · rintro ⟨hne, h_uniq⟩
    rw [eq_singleton_iff_unique_mem]
    refine' ⟨_, h_uniq⟩
    rw [← h_uniq hne.some hne.some_spec]
    exact hne.some_spec
    

theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [← eq_singleton_iff_unique_mem, ← ExistsUnique]

theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  rw [coe_singleton, Set.singleton_subset_iff]

@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff

@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  rw [← coe_subset, coe_singleton, Set.subset_singleton_iff_eq, coe_eq_empty, coe_eq_singleton]

protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff.trans <| or_iff_right h.ne_empty

theorem subset_singleton_iff' {s : Finset α} {a : α} : s ⊆ {a} ↔ ∀, ∀ b ∈ s, ∀, b = a :=
  forall₂_congrₓ fun _ _ => mem_singleton

@[simp]
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by
  rw [← coe_ssubset, coe_singleton, Set.ssubset_singleton_iff, coe_eq_empty]

theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp]
theorem mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s :=
  mem_cons

@[simp]
theorem mem_cons_self (a : α) (s : Finset α) {h} : a ∈ cons a s h :=
  mem_cons_self _ _

@[simp]
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl

theorem forall_mem_cons (h : a ∉ s) (p : α → Prop) : (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [← mem_cons, ← or_imp_distrib, ← forall_and_distrib, ← forall_eq]

@[simp]
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl

@[simp]
theorem nonempty_cons (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩

@[simp]
theorem nonempty_mk_coe : ∀ {l : List α} {hl}, (⟨↑l, hl⟩ : Finset α).Nonempty ↔ l ≠ []
  | [], hl => by
    simp
  | a :: l, hl => by
    simp [Multiset.cons_coe]

@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a s := by
  ext
  simp

theorem subset_cons (h : a ∉ s) : s ⊆ s.cons a h :=
  subset_cons _ _

theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  ssubset_cons h

theorem cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  cons_subset

@[simp]
theorem cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _)(h : a ∉ s), s.cons a h ⊆ t := by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩
  obtain ⟨a, hs, ht⟩ := (not_subset _ _).1 h.2
  exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩

end Cons

/-! ### disjoint union -/


/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disjUnion (s t : Finset α) (h : ∀, ∀ a ∈ s, ∀, a ∉ t) : Finset α :=
  ⟨s.1 + t.1, Multiset.nodup_add.2 ⟨s.2, t.2, h⟩⟩

@[simp]
theorem mem_disj_union {α s t h a} : a ∈ @disjUnion α s t h ↔ a ∈ s ∨ a ∈ t := by
  rcases s with ⟨⟨s⟩⟩ <;> rcases t with ⟨⟨t⟩⟩ <;> apply List.mem_appendₓ

theorem disj_union_comm (s t : Finset α) (h : ∀, ∀ a ∈ s, ∀, a ∉ t) :
    disjUnion s t h = disjUnion t s fun a ht hs => h _ hs ht :=
  eq_of_veq <| add_commₓ _ _

@[simp]
theorem empty_disj_union (t : Finset α) (h : ∀, ∀ a' ∈ ∅, ∀, a' ∉ t := fun a h _ => not_mem_empty _ h) :
    disjUnion ∅ t h = t :=
  eq_of_veq <| zero_addₓ _

@[simp]
theorem disj_union_empty (s : Finset α) (h : ∀, ∀ a' ∈ s, ∀, a' ∉ ∅ := fun a h => not_mem_empty _) :
    disjUnion s ∅ h = s :=
  eq_of_veq <| add_zeroₓ _

theorem singleton_disj_union (a : α) (t : Finset α) (h : ∀, ∀ a' ∈ {a}, ∀, a' ∉ t) :
    disjUnion {a} t h = cons a t (h _ <| mem_singleton_self _) :=
  eq_of_veq <| Multiset.singleton_add _ _

theorem disj_union_singleton (s : Finset α) (a : α) (h : ∀, ∀ a' ∈ s, ∀, a' ∉ {a}) :
    disjUnion s {a} h = cons a s fun ha => h _ ha <| mem_singleton_self _ := by
  rw [disj_union_comm, singleton_disj_union]

/-! ### insert -/


section DecidableEq

variable [DecidableEq α] {s t u v : Finset α} {a b : α}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : HasInsert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl

@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl

theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self] <;> rfl

theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_not_mem h]

@[simp]
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert

theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1

theorem mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h

theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left

theorem eq_of_not_mem_of_mem_insert (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb

@[simp]
theorem cons_eq_insert {α} [DecidableEq α] (a s h) : @cons α a s h = insert a s :=
  ext fun a => by
    simp

@[simp, norm_cast]
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) :=
  Set.ext fun x => by
    simp only [← mem_coe, ← mem_insert, ← Set.mem_insert_iff]

theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp

instance : IsLawfulSingleton α (Finset α) :=
  ⟨fun a => by
    ext
    simp ⟩

@[simp]
theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
  eq_of_veq <| ndinsert_of_mem h

@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _

theorem Insert.comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => by
    simp only [← mem_insert, ← Or.left_comm]

theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  Insert.comm a b ∅

@[simp]
theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext fun x => by
    simp only [← mem_insert, ← or.assoc.symm, ← or_selfₓ]

@[simp]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩

@[simp]
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/


instance {α : Type u} [DecidableEq α] (i : α) (s : Finset α) : Nonempty.{u + 1} ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

theorem ne_insert_of_not_mem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t := by
  contrapose! h
  simp [← h]

theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [← subset_iff, ← mem_insert, ← forall_eq, ← or_imp_distrib, ← forall_and_distrib]

theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun b => mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset.2 ⟨mem_insert_self _ _, Subset.trans h (subset_insert _ _)⟩

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert_self _ _) ha, congr_arg _⟩

theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) (sᶜ) := fun a h b _ => (insert_inj h).1

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∉ » s)
theorem ssubset_iff : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t := by
  exact_mod_cast @Set.ssubset_iff_insert α s t

theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_eliminator]
theorem cons_induction {α : Type _} {p : Finset α → Prop} (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
  | ⟨s, nd⟩ =>
    Multiset.induction_on s (fun _ => h₁)
      (fun a s IH nd => by
        cases' nodup_cons.1 nd with m nd'
        rw [← (eq_of_veq _ : cons a (Finset.mk s _) m = ⟨a ::ₘ s, nd⟩)]
        · exact h₂ m (IH nd')
          
        · rw [cons_val]
          )
      nd

@[elab_as_eliminator]
theorem cons_induction_on {α : Type _} {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
  cons_induction h₁ h₂ s

@[elab_as_eliminator]
protected theorem induction {α : Type _} {p : Finset α → Prop} [DecidableEq α] (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
  (cons_induction h₁) fun a s ha => (s.cons_eq_insert a ha).symm ▸ h₂ ha

/-- To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type _} {p : Finset α → Prop} [DecidableEq α] (s : Finset α) (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
  Finset.induction h₁ h₂ s

/-- To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_eliminator]
theorem induction_on' {α : Type _} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
  @Finset.induction_on α (fun T => T ⊆ S → p T) _ S (fun _ => h₁)
    (fun a s has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset.1 hs
      h₂ hS sS has (hqs sS))
    (Finset.Subset.refl S)

/-- To prove a proposition about a nonempty `s : finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : finset α`, then it also holds for the `finset`
obtained by inserting an element in `t`. -/
@[elab_as_eliminator]
theorem Nonempty.cons_induction {α : Type _} {p : ∀ s : Finset α, s.Nonempty → Prop}
    (h₀ : ∀ a, p {a} (singleton_nonempty _))
    (h₁ : ∀ ⦃a⦄ (s) (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (nonempty_cons h)) {s : Finset α}
    (hs : s.Nonempty) : p s hs := by
  induction' s using Finset.cons_induction with a t ha h
  · exact (not_nonempty_empty hs).elim
    
  obtain rfl | ht := t.eq_empty_or_nonempty
  · exact h₀ a
    
  · exact h₁ t ha ht (h ht)
    

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) : { i // i ∈ insert x t } ≃ Option { i // i ∈ t } := by
  refine'
    { toFun := fun y => if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩,
      invFun := fun y => (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩.. }
  · intro y
    by_cases' h : ↑y = x
    simp only [← Subtype.ext_iff, ← h, ← Option.elimₓ, ← dif_pos, ← Subtype.coe_mk]
    simp only [← h, ← Option.elimₓ, ← dif_neg, ← not_false_iff, ← Subtype.coe_eta, ← Subtype.coe_mk]
    
  · rintro (_ | y)
    simp only [← Option.elimₓ, ← dif_pos, ← Subtype.coe_mk]
    have : ↑y ≠ x := by
      rintro ⟨⟩
      exact h y.2
    simp only [← this, ← Option.elimₓ, ← Subtype.eta, ← dif_neg, ← not_false_iff, ← Subtype.coe_eta, ← Subtype.coe_mk]
    

/-! ### Lattice structure -/


/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : HasUnion (Finset α) :=
  ⟨fun s t => ⟨_, t.2.ndunion s.1⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : HasInter (Finset α) :=
  ⟨fun s t => ⟨_, s.2.ndinter t.1⟩⟩

instance : Lattice (Finset α) :=
  { Finset.partialOrder with sup := (· ∪ ·),
    sup_le := fun s t u hs ht a ha => (mem_ndunion.1 ha).elim (fun h => hs h) fun h => ht h,
    le_sup_left := fun s t a h => mem_ndunion.2 <| Or.inl h, le_sup_right := fun s t a h => mem_ndunion.2 <| Or.inr h,
    inf := (· ∩ ·), le_inf := fun s t u ht hu a h => mem_ndinter.2 ⟨ht h, hu h⟩,
    inf_le_left := fun s t a h => (mem_ndinter.1 h).1, inf_le_right := fun s t a h => (mem_ndinter.1 h).2 }

/-! #### union -/


@[simp]
theorem sup_eq_union : ((·⊔·) : Finset α → Finset α → Finset α) = (· ∪ ·) :=
  rfl

@[simp]
theorem inf_eq_inter : ((·⊓·) : Finset α → Finset α → Finset α) = (· ∩ ·) :=
  rfl

theorem union_val_nd (s t : Finset α) : (s ∪ t).1 = ndunion s.1 t.1 :=
  rfl

@[simp]
theorem union_val (s t : Finset α) : (s ∪ t).1 = s.1 ∪ t.1 :=
  ndunion_eq_union s.2

@[simp]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  mem_ndunion

@[simp]
theorem disj_union_eq_union (s t h) : @disjUnion α s t h = s ∪ t :=
  ext fun a => by
    simp

theorem mem_union_left (t : Finset α) (h : a ∈ s) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inl h

theorem mem_union_right (s : Finset α) (h : a ∈ t) : a ∈ s ∪ t :=
  mem_union.2 <| Or.inr h

theorem forall_mem_union {p : α → Prop} : (∀, ∀ a ∈ s ∪ t, ∀, p a) ↔ (∀, ∀ a ∈ s, ∀, p a) ∧ ∀, ∀ a ∈ t, ∀, p a :=
  ⟨fun h => ⟨fun a => h a ∘ mem_union_left _, fun b => h b ∘ mem_union_right _⟩, fun h ab hab =>
    (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩

theorem not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by
  rw [mem_union, not_or_distrib]

@[simp, norm_cast]
theorem coe_union (s₁ s₂ : Finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : Set α) :=
  Set.ext fun x => mem_union

theorem union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u :=
  sup_le <| le_iff_subset.2 hs

theorem subset_union_left (s₁ s₂ : Finset α) : s₁ ⊆ s₁ ∪ s₂ := fun x => mem_union_left _

theorem subset_union_right (s₁ s₂ : Finset α) : s₂ ⊆ s₁ ∪ s₂ := fun x => mem_union_right _

theorem union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
  sup_le_sup (le_iff_subset.2 hsu) htv

theorem union_comm (s₁ s₂ : Finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ :=
  sup_comm

instance : IsCommutative (Finset α) (· ∪ ·) :=
  ⟨union_comm⟩

@[simp]
theorem union_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  sup_assoc

instance : IsAssociative (Finset α) (· ∪ ·) :=
  ⟨union_assoc⟩

@[simp]
theorem union_idempotent (s : Finset α) : s ∪ s = s :=
  sup_idem

instance : IsIdempotent (Finset α) (· ∪ ·) :=
  ⟨union_idempotent⟩

theorem union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u :=
  (subset_union_left _ _).trans h

theorem union_subset_right {s t u : Finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
  Subset.trans (subset_union_right _ _) h

theorem union_left_comm (s t u : Finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
  ext fun _ => by
    simp only [← mem_union, ← Or.left_comm]

theorem union_right_comm (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ t :=
  ext fun x => by
    simp only [← mem_union, ← or_assoc, ← or_comm (x ∈ t)]

theorem union_self (s : Finset α) : s ∪ s = s :=
  union_idempotent s

@[simp]
theorem union_empty (s : Finset α) : s ∪ ∅ = s :=
  ext fun x => mem_union.trans <| or_falseₓ _

@[simp]
theorem empty_union (s : Finset α) : ∅ ∪ s = s :=
  ext fun x => mem_union.trans <| false_orₓ _

theorem insert_eq (a : α) (s : Finset α) : insert a s = {a} ∪ s :=
  rfl

@[simp]
theorem insert_union (a : α) (s t : Finset α) : insert a s ∪ t = insert a (s ∪ t) := by
  simp only [← insert_eq, ← union_assoc]

@[simp]
theorem union_insert (a : α) (s t : Finset α) : s ∪ insert a t = insert a (s ∪ t) := by
  simp only [← insert_eq, ← union_left_comm]

theorem insert_union_distrib (a : α) (s t : Finset α) : insert a (s ∪ t) = insert a s ∪ insert a t := by
  simp only [← insert_union, ← union_insert, ← insert_idem]

@[simp]
theorem union_eq_left_iff_subset {s t : Finset α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left

@[simp]
theorem left_eq_union_iff_subset {s t : Finset α} : s = s ∪ t ↔ t ⊆ s := by
  rw [← union_eq_left_iff_subset, eq_comm]

@[simp]
theorem union_eq_right_iff_subset {s t : Finset α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right

@[simp]
theorem right_eq_union_iff_subset {s t : Finset α} : s = t ∪ s ↔ t ⊆ s := by
  rw [← union_eq_right_iff_subset, eq_comm]

theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s⊔u :=
  sup_congr_left ht hu

theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht

theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left

theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right

/-- To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
theorem induction_on_union (P : Finset α → Finset α → Prop) (symm : ∀ {a b}, P a b → P b a) (empty_right : ∀ {a}, P a ∅)
    (singletons : ∀ {a b}, P {a} {b}) (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) : ∀ a b, P a b := by
  intro a b
  refine' Finset.induction_on b empty_right fun x s xs hi => symm _
  rw [Finset.insert_eq]
  apply union_of _ (symm hi)
  refine' Finset.induction_on a empty_right fun a t ta hi => symm _
  rw [Finset.insert_eq]
  exact union_of singletons (symm hi)

theorem _root_.directed.exists_mem_subset_of_finset_subset_bUnion {α ι : Type _} [hn : Nonempty ι] {f : ι → Set α}
    (h : Directed (· ⊆ ·) f) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i, f i) : ∃ i, (s : Set α) ⊆ f i := by
  classical
  revert hs
  apply s.induction_on
  · refine' fun _ => ⟨hn.some, _⟩
    simp only [← coe_empty, ← Set.empty_subset]
    
  · intro b t hbt htc hbtc
    obtain ⟨i : ι, hti : (t : Set α) ⊆ f i⟩ := htc (Set.Subset.trans (t.subset_insert b) hbtc)
    obtain ⟨j, hbj⟩ : ∃ j, b ∈ f j := by
      simpa [← Set.mem_Union₂] using hbtc (t.mem_insert_self b)
    rcases h j i with ⟨k, hk, hk'⟩
    use k
    rw [coe_insert, Set.insert_subset]
    exact ⟨hk hbj, trans hti hk'⟩
    

theorem _root_.directed_on.exists_mem_subset_of_finset_subset_bUnion {α ι : Type _} {f : ι → Set α} {c : Set ι}
    (hn : c.Nonempty) (hc : DirectedOn (fun i j => f i ⊆ f j) c) {s : Finset α} (hs : (s : Set α) ⊆ ⋃ i ∈ c, f i) :
    ∃ i ∈ c, (s : Set α) ⊆ f i := by
  rw [Set.bUnion_eq_Union] at hs
  have := Set.nonempty_coe_sort.2 hn
  obtain ⟨⟨i, hic⟩, hi⟩ := (directed_comp.2 hc.directed_coe).exists_mem_subset_of_finset_subset_bUnion hs
  exact ⟨i, hic, hi⟩

/-! #### inter -/


theorem inter_val_nd (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 :=
  rfl

@[simp]
theorem inter_val (s₁ s₂ : Finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 :=
  ndinter_eq_inter s₁.2

@[simp]
theorem mem_inter {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ :=
  mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₁ :=
  (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : Finset α} (h : a ∈ s₁ ∩ s₂) : a ∈ s₂ :=
  (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
  and_imp.1 mem_inter.2

theorem inter_subset_left (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₁ := fun a => mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : Finset α) : s₁ ∩ s₂ ⊆ s₂ := fun a => mem_of_mem_inter_right

theorem subset_inter {s₁ s₂ u : Finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u := by
  simp (config := { contextual := true })only [← subset_iff, ← mem_inter] <;> intros <;> constructor <;> trivial

@[simp, norm_cast]
theorem coe_inter (s₁ s₂ : Finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : Set α) :=
  Set.ext fun _ => mem_inter

@[simp]
theorem union_inter_cancel_left {s t : Finset α} : (s ∪ t) ∩ s = s := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_left]

@[simp]
theorem union_inter_cancel_right {s t : Finset α} : (s ∪ t) ∩ t = t := by
  rw [← coe_inj, coe_inter, coe_union, Set.union_inter_cancel_right]

theorem inter_comm (s₁ s₂ : Finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
  ext fun _ => by
    simp only [← mem_inter, ← and_comm]

@[simp]
theorem inter_assoc (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
  ext fun _ => by
    simp only [← mem_inter, ← and_assoc]

theorem inter_left_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun _ => by
    simp only [← mem_inter, ← And.left_comm]

theorem inter_right_comm (s₁ s₂ s₃ : Finset α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun _ => by
    simp only [← mem_inter, ← And.right_comm]

@[simp]
theorem inter_self (s : Finset α) : s ∩ s = s :=
  ext fun _ => mem_inter.trans <| and_selfₓ _

@[simp]
theorem inter_empty (s : Finset α) : s ∩ ∅ = ∅ :=
  ext fun _ => mem_inter.trans <| and_falseₓ _

@[simp]
theorem empty_inter (s : Finset α) : ∅ ∩ s = ∅ :=
  ext fun _ => mem_inter.trans <| false_andₓ _

@[simp]
theorem inter_union_self (s t : Finset α) : s ∩ (t ∪ s) = s := by
  rw [inter_comm, union_inter_cancel_right]

@[simp]
theorem insert_inter_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₂) : insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
  ext fun x => by
    have : x = a ∨ x ∈ s₂ ↔ x ∈ s₂ :=
      or_iff_right_of_imp <| by
        rintro rfl <;> exact h
    simp only [← mem_inter, ← mem_insert, ← or_and_distrib_left, ← this]

@[simp]
theorem inter_insert_of_mem {s₁ s₂ : Finset α} {a : α} (h : a ∈ s₁) : s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) := by
  rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp]
theorem insert_inter_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₂) : insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
  ext fun x => by
    have : ¬(x = a ∧ x ∈ s₂) := by
      rintro ⟨rfl, H⟩ <;> exact h H
    simp only [← mem_inter, ← mem_insert, ← or_and_distrib_right, ← this, ← false_orₓ]

@[simp]
theorem inter_insert_of_not_mem {s₁ s₂ : Finset α} {a : α} (h : a ∉ s₁) : s₁ ∩ insert a s₂ = s₁ ∩ s₂ := by
  rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp]
theorem singleton_inter_of_mem {a : α} {s : Finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
  show insert a ∅ ∩ s = insert a ∅ by
    rw [insert_inter_of_mem H, empty_inter]

@[simp]
theorem singleton_inter_of_not_mem {a : α} {s : Finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [← mem_inter, ← mem_singleton] <;> rintro x ⟨rfl, h⟩ <;> exact H h

@[simp]
theorem inter_singleton_of_mem {a : α} {s : Finset α} (h : a ∈ s) : s ∩ {a} = {a} := by
  rw [inter_comm, singleton_inter_of_mem h]

@[simp]
theorem inter_singleton_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : s ∩ {a} = ∅ := by
  rw [inter_comm, singleton_inter_of_not_mem h]

@[mono]
theorem inter_subset_inter {x y s t : Finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t := by
  intro a a_in
  rw [Finset.mem_inter] at a_in⊢
  exact ⟨h a_in.1, h' a_in.2⟩

theorem inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u :=
  inter_subset_inter Subset.rfl h

theorem inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter h Subset.rfl

instance {α : Type u} : OrderBot (Finset α) where
  bot := ∅
  bot_le := empty_subset

@[simp]
theorem bot_eq_empty {α : Type u} : (⊥ : Finset α) = ∅ :=
  rfl

instance : DistribLattice (Finset α) :=
  { Finset.lattice with
    le_sup_inf := fun a b c =>
      show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c by
        simp (config := { contextual := true })only [← subset_iff, ← mem_inter, ← mem_union, ← and_imp, ←
            or_imp_distrib] <;>
          simp only [← true_orₓ, ← imp_true_iff, ← true_andₓ, ← or_trueₓ] }

@[simp]
theorem union_left_idem (s t : Finset α) : s ∪ (s ∪ t) = s ∪ t :=
  sup_left_idem

@[simp]
theorem union_right_idem (s t : Finset α) : s ∪ t ∪ t = s ∪ t :=
  sup_right_idem

@[simp]
theorem inter_left_idem (s t : Finset α) : s ∩ (s ∩ t) = s ∩ t :=
  inf_left_idem

@[simp]
theorem inter_right_idem (s t : Finset α) : s ∩ t ∩ t = s ∩ t :=
  inf_right_idem

theorem inter_distrib_left (s t u : Finset α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left

theorem inter_distrib_right (s t u : Finset α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right

theorem union_distrib_left (s t u : Finset α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left

theorem union_distrib_right (s t u : Finset α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right

theorem union_union_distrib_left (s t u : Finset α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _

theorem union_union_distrib_right (s t u : Finset α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _

theorem inter_inter_distrib_left (s t u : Finset α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _

theorem inter_inter_distrib_right (s t u : Finset α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _

theorem union_union_union_comm (s t u v : Finset α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _

theorem inter_inter_inter_comm (s t u v : Finset α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _

theorem union_eq_empty_iff (A B : Finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ :=
  sup_eq_bot_iff

theorem union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (sup_le_iff : s⊔t ≤ u ↔ s ≤ u ∧ t ≤ u)

theorem subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u :=
  (le_inf_iff : s ≤ t⊓u ↔ s ≤ t ∧ s ≤ u)

theorem inter_eq_left_iff_subset (s t : Finset α) : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left

theorem inter_eq_right_iff_subset (s t : Finset α) : t ∩ s = s ↔ s ⊆ t :=
  inf_eq_right

theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu

theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht

theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left

theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right

theorem ite_subset_union (s s' : Finset α) (P : Prop) [Decidable P] : ite P s s' ⊆ s ∪ s' :=
  ite_le_sup s s' P

theorem inter_subset_ite (s s' : Finset α) (P : Prop) [Decidable P] : s ∩ s' ⊆ ite P s s' :=
  inf_le_ite s s' P

/-! ### erase -/


/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : Finset α) (a : α) : Finset α :=
  ⟨_, s.2.erase a⟩

@[simp]
theorem erase_val (s : Finset α) (a : α) : (erase s a).1 = s.1.erase a :=
  rfl

@[simp]
theorem mem_erase {a b : α} {s : Finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
  s.2.mem_erase_iff

theorem not_mem_erase (a : α) (s : Finset α) : a ∉ erase s a :=
  s.2.not_mem_erase

-- While this can be solved by `simp`, this lemma is eligible for `dsimp`
@[nolint simp_nf, simp]
theorem erase_empty (a : α) : erase ∅ a = ∅ :=
  rfl

@[simp]
theorem erase_singleton (a : α) : ({a} : Finset α).erase a = ∅ := by
  ext x
  rw [mem_erase, mem_singleton, not_and_selfₓ]
  rfl

theorem ne_of_mem_erase : b ∈ erase s a → b ≠ a := fun h => (mem_erase.1 h).1

theorem mem_of_mem_erase : b ∈ erase s a → b ∈ s :=
  mem_of_mem_erase

theorem mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b := by
  simp only [← mem_erase] <;> exact And.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
theorem eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a := by
  rw [mem_erase, not_and] at hsa
  exact not_imp_not.mp hsa hs

theorem erase_insert {a : α} {s : Finset α} (h : a ∉ s) : erase (insert a s) a = s :=
  ext fun x => by
    simp only [← mem_erase, ← mem_insert, ← and_or_distrib_left, ← not_and_selfₓ, ← false_orₓ] <;>
      apply and_iff_right_of_imp <;> rintro H rfl <;> exact h H

theorem insert_erase {a : α} {s : Finset α} (h : a ∈ s) : insert a (erase s a) = s :=
  ext fun x => by
    simp only [← mem_insert, ← mem_erase, ← or_and_distrib_left, ← dec_em, ← true_andₓ] <;>
      apply or_iff_right_of_imp <;> rintro rfl <;> exact h

theorem erase_subset_erase (a : α) {s t : Finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
  val_le_iff.1 <| erase_le_erase _ <| val_le_iff.2 h

theorem erase_subset (a : α) (s : Finset α) : erase s a ⊆ s :=
  erase_subset _ _

theorem subset_erase {a : α} {s t : Finset α} : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s :=
  ⟨fun h => ⟨h.trans (erase_subset _ _), fun ha => not_mem_erase _ _ (h ha)⟩, fun h b hb =>
    mem_erase.2 ⟨ne_of_mem_of_not_mem hb h.2, h.1 hb⟩⟩

@[simp, norm_cast]
theorem coe_erase (a : α) (s : Finset α) : ↑(erase s a) = (s \ {a} : Set α) :=
  Set.ext fun _ =>
    mem_erase.trans <| by
      rw [and_comm, Set.mem_diff, Set.mem_singleton_iff] <;> rfl

theorem erase_ssubset {a : α} {s : Finset α} (h : a ∈ s) : s.erase a ⊂ s :=
  calc
    s.erase a ⊂ insert a (s.erase a) := ssubset_insert <| not_mem_erase _ _
    _ = _ := insert_erase h
    

theorem ssubset_iff_exists_subset_erase {s t : Finset α} : s ⊂ t ↔ ∃ a ∈ t, s ⊆ t.erase a := by
  refine' ⟨fun h => _, fun ⟨a, ha, h⟩ => ssubset_of_subset_of_ssubset h <| erase_ssubset ha⟩
  obtain ⟨a, ht, hs⟩ := (not_subset _ _).1 h.2
  exact ⟨a, ht, subset_erase.2 ⟨h.1, hs⟩⟩

theorem erase_ssubset_insert (s : Finset α) (a : α) : s.erase a ⊂ insert a s :=
  ssubset_iff_exists_subset_erase.2 ⟨a, mem_insert_self _ _, erase_subset_erase _ <| subset_insert _ _⟩

@[simp]
theorem erase_eq_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : erase s a = s :=
  eq_of_veq <| erase_of_not_mem h

@[simp]
theorem erase_insert_eq_erase (s : Finset α) (a : α) : (insert a s).erase a = s.erase a := by
  by_cases' ha : a ∈ s <;>
    · simp [← ha, ← erase_insert]
      

theorem erase_cons {s : Finset α} {a : α} (h : a ∉ s) : (s.cons a h).erase a = s := by
  rw [cons_eq_insert, erase_insert_eq_erase, erase_eq_of_not_mem h]

theorem erase_idem {a : α} {s : Finset α} : erase (erase s a) a = erase s a := by
  simp

theorem erase_right_comm {a b : α} {s : Finset α} : erase (erase s a) b = erase (erase s b) a := by
  ext x
  simp only [← mem_erase, and_assoc]
  rw [and_comm (x ≠ a)]

theorem subset_insert_iff {a : α} {s t : Finset α} : s ⊆ insert a t ↔ erase s a ⊆ t := by
  simp only [← subset_iff, ← or_iff_not_imp_left, ← mem_erase, ← mem_insert, ← and_imp] <;>
    exact forall_congrₓ fun x => forall_swap

theorem erase_insert_subset (a : α) (s : Finset α) : erase (insert a s) a ⊆ s :=
  subset_insert_iff.1 <| subset.rfl

theorem insert_erase_subset (a : α) (s : Finset α) : s ⊆ insert a (erase s a) :=
  subset_insert_iff.2 <| subset.rfl

theorem subset_insert_iff_of_not_mem (h : a ∉ s) : s ⊆ insert a t ↔ s ⊆ t := by
  rw [subset_insert_iff, erase_eq_of_not_mem h]

theorem erase_subset_iff_of_mem (h : a ∈ t) : s.erase a ⊆ t ↔ s ⊆ t := by
  rw [← subset_insert_iff, insert_eq_of_mem h]

theorem erase_inj {x y : α} (s : Finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y := by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [eq_of_mem_of_not_mem_erase hx]
  rw [← h]
  simp

theorem erase_inj_on (s : Finset α) : Set.InjOn s.erase s := fun _ _ _ _ => (erase_inj s ‹_›).mp

theorem erase_inj_on' (a : α) : { s : Finset α | a ∈ s }.InjOn fun s => erase s a :=
  fun s hs t ht (h : s.erase a = _) => by
  rw [← insert_erase hs, ← insert_erase ht, h]

/-! ### sdiff -/


/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : HasSdiff (Finset α) :=
  ⟨fun s₁ s₂ => ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

@[simp]
theorem sdiff_val (s₁ s₂ : Finset α) : (s₁ \ s₂).val = s₁.val - s₂.val :=
  rfl

@[simp]
theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t :=
  mem_sub_of_nodup s.2

@[simp]
theorem inter_sdiff_self (s₁ s₂ : Finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
  eq_empty_of_forall_not_mem <| by
    simp only [← mem_inter, ← mem_sdiff] <;> rintro x ⟨h, _, hn⟩ <;> exact hn h

instance : GeneralizedBooleanAlgebra (Finset α) :=
  { Finset.hasSdiff, Finset.distribLattice, Finset.orderBot with
    sup_inf_sdiff := fun x y => by
      simp only [← ext_iff, ← mem_union, ← mem_sdiff, ← inf_eq_inter, ← sup_eq_union, ← mem_inter]
      tauto,
    inf_inf_sdiff := fun x y => by
      simp only [← ext_iff, ← inter_sdiff_self, ← inter_empty, ← inter_assoc, ← false_iffₓ, ← inf_eq_inter, ←
        not_mem_empty]
      tauto }

theorem not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t := by
  simp only [← mem_sdiff, ← h, ← not_true, ← not_false_iff, ← and_falseₓ]

theorem not_mem_sdiff_of_not_mem_left (h : a ∉ s) : a ∉ s \ t := by
  simpa

theorem union_sdiff_of_subset (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h

theorem sdiff_union_of_subset {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₂ \ s₁ ∪ s₁ = s₂ :=
  (union_comm _ _).trans (union_sdiff_of_subset h)

theorem inter_sdiff (s t u : Finset α) : s ∩ (t \ u) = (s ∩ t) \ u := by
  ext x
  simp [← and_assoc]

@[simp]
theorem sdiff_inter_self (s₁ s₂ : Finset α) : s₂ \ s₁ ∩ s₁ = ∅ :=
  inf_sdiff_self_left

@[simp]
theorem sdiff_self (s₁ : Finset α) : s₁ \ s₁ = ∅ :=
  sdiff_self

theorem sdiff_inter_distrib_right (s t u : Finset α) : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf

@[simp]
theorem sdiff_inter_self_left (s t : Finset α) : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left

@[simp]
theorem sdiff_inter_self_right (s t : Finset α) : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right

@[simp]
theorem sdiff_empty : s \ ∅ = s :=
  sdiff_bot

@[mono]
theorem sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
  sdiff_le_sdiff ‹s ≤ t› ‹v ≤ u›

@[simp, norm_cast]
theorem coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : Set α) :=
  Set.ext fun _ => mem_sdiff

@[simp]
theorem union_sdiff_self_eq_union : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self_right

@[simp]
theorem sdiff_union_self_eq_union : s \ t ∪ t = s ∪ t :=
  sup_sdiff_self_left

theorem union_sdiff_symm : s ∪ t \ s = t ∪ s \ t :=
  sup_sdiff_symm

theorem sdiff_union_inter (s t : Finset α) : s \ t ∪ s ∩ t = s :=
  sup_sdiff_inf _ _

@[simp]
theorem sdiff_idem (s t : Finset α) : (s \ t) \ t = s \ t :=
  sdiff_idem

theorem sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff

theorem sdiff_nonempty : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  nonempty_iff_ne_empty.trans sdiff_eq_empty_iff_subset.Not

@[simp]
theorem empty_sdiff (s : Finset α) : ∅ \ s = ∅ :=
  bot_sdiff

theorem insert_sdiff_of_not_mem (s : Finset α) {t : Finset α} {x : α} (h : x ∉ t) : insert x s \ t = insert x (s \ t) :=
  by
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert]
  exact Set.insert_diff_of_not_mem s h

theorem insert_sdiff_of_mem (s : Finset α) {x : α} (h : x ∈ t) : insert x s \ t = s \ t := by
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert]
  exact Set.insert_diff_of_mem s h

@[simp]
theorem insert_sdiff_insert (s t : Finset α) (x : α) : insert x s \ insert x t = s \ insert x t :=
  insert_sdiff_of_mem _ (mem_insert_self _ _)

theorem sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : Finset α) : s \ insert x t = s \ t := by
  refine' subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) fun y hy => _
  simp only [← mem_sdiff, ← mem_insert, ← not_or_distrib] at hy⊢
  exact ⟨hy.1, fun hxy => h <| hxy ▸ hy.1, hy.2⟩

@[simp]
theorem sdiff_subset (s t : Finset α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le

theorem sdiff_ssubset (h : t ⊆ s) (ht : t.Nonempty) : s \ t ⊂ s :=
  sdiff_lt ‹t ≤ s› ht.ne_empty

theorem union_sdiff_distrib (s₁ s₂ t : Finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t :=
  sup_sdiff

theorem sdiff_union_distrib (s t₁ t₂ : Finset α) : s \ (t₁ ∪ t₂) = s \ t₁ ∩ (s \ t₂) :=
  sdiff_sup

theorem union_sdiff_self (s t : Finset α) : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self

theorem sdiff_singleton_eq_erase (a : α) (s : Finset α) : s \ singleton a = erase s a := by
  ext
  rw [mem_erase, mem_sdiff, mem_singleton]
  tauto

@[simp]
theorem sdiff_singleton_not_mem_eq_self (s : Finset α) {a : α} (ha : a ∉ s) : s \ {a} = s := by
  simp only [← sdiff_singleton_eq_erase, ← ha, ← erase_eq_of_not_mem, ← not_false_iff]

theorem sdiff_erase {x : α} (hx : x ∈ s) : s \ s.erase x = {x} := by
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_right_self]
  exact inf_eq_right.2 (singleton_subset_iff.2 hx)

theorem sdiff_sdiff_self_left (s t : Finset α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self

theorem sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t :=
  sdiff_sdiff_eq_self h

theorem sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : Finset α} : s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
  sdiff_eq_sdiff_iff_inf_eq_inf

theorem union_eq_sdiff_union_sdiff_union_inter (s t : Finset α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf

theorem erase_eq_empty_iff (s : Finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} := by
  rw [← sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]

end DecidableEq

/-! ### attach -/


/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : Finset α) : Finset { x // x ∈ s } :=
  ⟨attach s.1, nodup_attach.2 s.2⟩

theorem sizeof_lt_sizeof_of_mem [SizeOf α] {x : α} {s : Finset α} (hx : x ∈ s) : sizeof x < sizeof s := by
  cases s
  dsimp' [← sizeof, ← SizeOf.sizeof, ← Finset.sizeof]
  apply lt_add_left
  exact Multiset.sizeof_lt_sizeof_of_mem hx

@[simp]
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl

@[simp]
theorem mem_attach (s : Finset α) : ∀ x, x ∈ s.attach :=
  mem_attach _

@[simp]
theorem attach_empty : attach (∅ : Finset α) = ∅ :=
  rfl

@[simp]
theorem attach_nonempty_iff (s : Finset α) : s.attach.Nonempty ↔ s.Nonempty := by
  simp [← Finset.Nonempty]

@[simp]
theorem attach_eq_empty_iff (s : Finset α) : s.attach = ∅ ↔ s = ∅ := by
  simpa [← eq_empty_iff_forall_not_mem]

/-! ### piecewise -/


section Piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type _} {δ : α → Sort _} (s : Finset α) (f g : ∀ i, δ i) [∀ j, Decidable (j ∈ s)] : ∀ i, δ i :=
  fun i => if i ∈ s then f i else g i

variable {δ : α → Sort _} (s : Finset α) (f g : ∀ i, δ i)

@[simp]
theorem piecewise_insert_self [DecidableEq α] {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by
  simp [← piecewise]

@[simp]
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Finset α))] : piecewise ∅ f g = g := by
  ext i
  simp [← piecewise]

variable [∀ j, Decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move]
theorem piecewise_coe [∀ j, Decidable (j ∈ (s : Set α))] : (s : Set α).piecewise f g = s.piecewise f g := by
  ext
  congr

@[simp]
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := by
  simp [← piecewise, ← hi]

@[simp]
theorem piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [← piecewise, ← hi]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » s)
theorem piecewise_congr {f f' g g' : ∀ i, δ i} (hf : ∀, ∀ i ∈ s, ∀, f i = f' i) (hg : ∀ (i) (_ : i ∉ s), g i = g' i) :
    s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)

@[simp]
theorem piecewise_insert_of_ne [DecidableEq α] {i j : α} [∀ i, Decidable (i ∈ insert j s)] (h : i ≠ j) :
    (insert j s).piecewise f g i = s.piecewise f g i := by
  simp [← piecewise, ← h]

theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  classical
  simp only [piecewise_coe, ← coe_insert, Set.piecewise_insert]

theorem piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) : p (s.piecewise f g i) := by
  by_cases' hi : i ∈ s <;> simpa [← hi]

theorem piecewise_mem_set_pi {δ : α → Type _} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ Set.Pi t t')
    (hg : g ∈ Set.Pi t t') : s.piecewise f g ∈ Set.Pi t t' := by
  classical
  rw [← piecewise_coe]
  exact Set.piecewise_mem_pi (↑s) hf hg

theorem piecewise_singleton [DecidableEq α] (i : α) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]

theorem piecewise_piecewise_of_subset_left {s t : Finset α} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : s ⊆ t) (f₁ f₂ g : ∀ a, δ a) : s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl

@[simp]
theorem piecewise_idem_left (f₁ f₂ g : ∀ a, δ a) : s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _

theorem piecewise_piecewise_of_subset_right {s t : Finset α} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : t ⊆ s) (f g₁ g₂ : ∀ a, δ a) : s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun i hi => t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi)

@[simp]
theorem piecewise_idem_right (f g₁ g₂ : ∀ a, δ a) : s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂

theorem update_eq_piecewise {β : Type _} [DecidableEq α] (f : α → β) (i : α) (v : β) :
    update f i v = piecewise (singleton i) (fun j => v) f :=
  (piecewise_singleton _ _ _).symm

theorem update_piecewise [DecidableEq α] (i : α) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) := by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases' hs : j ∈ s <;> simp [*]

theorem update_piecewise_of_mem [DecidableEq α] {i : α} (hi : i ∈ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g := by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun _ _ => rfl) fun j hj => update_noteq _ _ _
  exact fun h => hj (h.symm ▸ hi)

theorem update_piecewise_of_not_mem [DecidableEq α] {i : α} (hi : i ∉ s) (v : δ i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) := by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun j hj => update_noteq _ _ _) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)

theorem piecewise_le_of_le_of_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g h : ∀ i, δ i} (Hf : f ≤ h) (Hg : g ≤ h) :
    s.piecewise f g ≤ h := fun x => piecewise_cases s f g (· ≤ h x) (Hf x) (Hg x)

theorem le_piecewise_of_le_of_le {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g h : ∀ i, δ i} (Hf : h ≤ f) (Hg : h ≤ g) :
    h ≤ s.piecewise f g := fun x => piecewise_cases s f g (fun y => h x ≤ y) (Hf x) (Hg x)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
theorem piecewise_le_piecewise' {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g f' g' : ∀ i, δ i}
    (Hf : ∀, ∀ x ∈ s, ∀, f x ≤ f' x) (Hg : ∀ (x) (_ : x ∉ s), g x ≤ g' x) : s.piecewise f g ≤ s.piecewise f' g' :=
  fun x => by
  by_cases' hx : x ∈ s <;> simp [← hx, *]

theorem piecewise_le_piecewise {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g f' g' : ∀ i, δ i} (Hf : f ≤ f')
    (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => Hf x) fun x _ => Hg x

theorem piecewise_mem_Icc_of_mem_of_mem {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f f₁ g g₁ : ∀ i, δ i}
    (hf : f ∈ Set.Icc f₁ g₁) (hg : g ∈ Set.Icc f₁ g₁) : s.piecewise f g ∈ Set.Icc f₁ g₁ :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

theorem piecewise_mem_Icc {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g : ∀ i, δ i} (h : f ≤ g) :
    s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)

theorem piecewise_mem_Icc' {δ : α → Type _} [∀ i, Preorderₓ (δ i)] {f g : ∀ i, δ i} (h : g ≤ f) :
    s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)

end Piecewise

section DecidablePiExists

variable {s : Finset α}

instance decidableDforallFinset {p : ∀, ∀ a ∈ s, ∀, Prop} [hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ s), p a h) :=
  Multiset.decidableDforallMultiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidableEqPiFinset {β : α → Type _} [h : ∀ a, DecidableEq (β a)] : DecidableEq (∀, ∀ a ∈ s, ∀, β a) :=
  Multiset.decidableEqPiMultiset

instance decidableDexistsFinset {p : ∀, ∀ a ∈ s, ∀, Prop} [hp : ∀ (a) (h : a ∈ s), Decidable (p a h)] :
    Decidable (∃ (a : _)(h : a ∈ s), p a h) :=
  Multiset.decidableDexistsMultiset

end DecidablePiExists

/-! ### filter -/


section Filter

variable (p q : α → Prop) [DecidablePred p] [DecidablePred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : Finset α) : Finset α :=
  ⟨_, s.2.filter p⟩

@[simp]
theorem filter_val (s : Finset α) : (filter p s).1 = s.1.filter p :=
  rfl

@[simp]
theorem filter_subset (s : Finset α) : s.filter p ⊆ s :=
  filter_subset _ _

variable {p}

@[simp]
theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a :=
  mem_filter

theorem mem_of_mem_filter {s : Finset α} (x : α) (h : x ∈ s.filter p) : x ∈ s :=
  mem_of_mem_filter h

theorem filter_ssubset {s : Finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬p x :=
  ⟨fun h =>
    let ⟨x, hs, hp⟩ := Set.exists_of_ssubset h
    ⟨x, hs, mt (fun hp => mem_filter.2 ⟨hs, hp⟩) hp⟩,
    fun ⟨x, hs, hp⟩ => ⟨s.filter_subset _, fun h => hp (mem_filter.1 (h hs)).2⟩⟩

variable (p)

theorem filter_filter (s : Finset α) : (s.filter p).filter q = s.filter fun a => p a ∧ q a :=
  ext fun a => by
    simp only [← mem_filter, ← and_comm, ← And.left_comm]

theorem filter_true {s : Finset α} [h : DecidablePred fun _ => True] : @Finset.filter α (fun _ => True) h s = s := by
  ext <;> simp

@[simp]
theorem filter_false {h} (s : Finset α) : @filter α (fun a => False) h s = ∅ :=
  ext fun a => by
    simp only [← mem_filter, ← and_falseₓ] <;> rfl

variable {p q}

theorem filter_eq_self (s : Finset α) : s.filter p = s ↔ ∀, ∀ x ∈ s, ∀, p x := by
  simp [← Finset.ext_iff]

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp]
theorem filter_true_of_mem {s : Finset α} (h : ∀, ∀ x ∈ s, ∀, p x) : s.filter p = s :=
  (filter_eq_self s).mpr h

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
theorem filter_false_of_mem {s : Finset α} (h : ∀, ∀ x ∈ s, ∀, ¬p x) : s.filter p = ∅ :=
  eq_empty_of_forall_not_mem
    (by
      simpa)

theorem filter_eq_empty_iff (s : Finset α) : s.filter p = ∅ ↔ ∀, ∀ x ∈ s, ∀, ¬p x := by
  refine' ⟨_, filter_false_of_mem⟩
  intro hs
  injection hs with hs'
  rwa [filter_eq_nil] at hs'

theorem filter_nonempty_iff {s : Finset α} : (s.filter p).Nonempty ↔ ∃ a ∈ s, p a := by
  simp only [← nonempty_iff_ne_empty, ← Ne.def, ← filter_eq_empty_iff, ← not_not, ← not_forall]

theorem filter_congr {s : Finset α} (H : ∀, ∀ x ∈ s, ∀, p x ↔ q x) : filter p s = filter q s :=
  eq_of_veq <| filter_congr H

variable (p q)

theorem filter_empty : filter p ∅ = ∅ :=
  subset_empty.1 <| filter_subset _ _

theorem filter_subset_filter {s t : Finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p := fun a ha =>
  mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

theorem monotone_filter_left : Monotone (filter p) := fun _ _ => filter_subset_filter p

theorem monotone_filter_right (s : Finset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q] (h : p ≤ q) :
    s.filter p ≤ s.filter q :=
  Multiset.subset_of_le (Multiset.monotone_filter_right s.val h)

@[simp, norm_cast]
theorem coe_filter (s : Finset α) : ↑(s.filter p) = ({ x ∈ ↑s | p x } : Set α) :=
  Set.ext fun _ => mem_filter

theorem subset_coe_filter_of_subset_forall (s : Finset α) {t : Set α} (h₁ : t ⊆ s) (h₂ : ∀, ∀ x ∈ t, ∀, p x) :
    t ⊆ s.filter p := fun x hx => (s.coe_filter p).symm ▸ ⟨h₁ hx, h₂ x hx⟩

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ := by
  classical
  ext x
  simp
  split_ifs with h <;> by_cases' h' : x = a <;> simp [← h, ← h']

theorem filter_cons_of_pos (a : α) (s : Finset α) (ha : a ∉ s) (hp : p a) :
    filter p (cons a s ha) = cons a (filter p s) (mem_filter.Not.mpr <| mt And.left ha) :=
  eq_of_veq <| Multiset.filter_cons_of_pos s.val hp

theorem filter_cons_of_neg (a : α) (s : Finset α) (ha : a ∉ s) (hp : ¬p a) : filter p (cons a s ha) = filter p s :=
  eq_of_veq <| Multiset.filter_cons_of_neg s.val hp

theorem filter_disj_union (s : Finset α) (t : Finset α) (h : ∀ a : α, a ∈ s → a ∉ t) :
    filter p (disjUnion s t h) =
      (filter p s).disjUnion (filter p t) fun a hs ht => h a (mem_of_mem_filter _ hs) (mem_of_mem_filter _ ht) :=
  eq_of_veq <| Multiset.filter_add _ _ _

theorem filter_cons {a : α} (s : Finset α) (ha : a ∉ s) :
    filter p (cons a s ha) =
      (if p a then {a} else ∅ : Finset α).disjUnion (filter p s) fun b hb => by
        split_ifs  at hb
        · rw [finset.mem_singleton.mp hb]
          exact mem_filter.not.mpr <| mt And.left ha
          
        · cases hb
           :=
  by
  split_ifs with h
  · rw [filter_cons_of_pos _ _ _ ha h, singleton_disj_union]
    
  · rw [filter_cons_of_neg _ _ _ ha h, empty_disj_union]
    

variable [DecidableEq α]

theorem filter_union (s₁ s₂ : Finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
  ext fun _ => by
    simp only [← mem_filter, ← mem_union, ← or_and_distrib_right]

theorem filter_union_right (s : Finset α) : s.filter p ∪ s.filter q = s.filter fun x => p x ∨ q x :=
  ext fun x => by
    simp only [← mem_filter, ← mem_union, ← and_or_distrib_left.symm]

theorem filter_mem_eq_inter {s t : Finset α} [∀ i, Decidable (i ∈ t)] : (s.filter fun i => i ∈ t) = s ∩ t :=
  ext fun i => by
    rw [mem_filter, mem_inter]

theorem filter_inter_distrib (s t : Finset α) : (s ∩ t).filter p = s.filter p ∩ t.filter p := by
  ext
  simp only [← mem_filter, ← mem_inter]
  exact and_and_distrib_right _ _ _

theorem filter_inter (s t : Finset α) : filter p s ∩ t = filter p (s ∩ t) := by
  ext
  simp only [← mem_inter, ← mem_filter, ← And.right_comm]

theorem inter_filter (s t : Finset α) : s ∩ filter p t = filter p (s ∩ t) := by
  rw [inter_comm, filter_inter, inter_comm]

theorem filter_insert (a : α) (s : Finset α) :
    filter p (insert a s) = if p a then insert a (filter p s) else filter p s := by
  ext x
  simp
  split_ifs with h <;> by_cases' h' : x = a <;> simp [← h, ← h']

theorem filter_erase (a : α) (s : Finset α) : filter p (erase s a) = erase (filter p s) a := by
  ext x
  simp only [← and_assoc, ← mem_filter, ← iff_selfₓ, ← mem_erase]

theorem filter_or [DecidablePred fun a => p a ∨ q a] (s : Finset α) :
    (s.filter fun a => p a ∨ q a) = s.filter p ∪ s.filter q :=
  ext fun _ => by
    simp only [← mem_filter, ← mem_union, ← and_or_distrib_left]

theorem filter_and [DecidablePred fun a => p a ∧ q a] (s : Finset α) :
    (s.filter fun a => p a ∧ q a) = s.filter p ∩ s.filter q :=
  ext fun _ => by
    simp only [← mem_filter, ← mem_inter, ← and_comm, ← And.left_comm, ← and_selfₓ]

theorem filter_not [DecidablePred fun a => ¬p a] (s : Finset α) : (s.filter fun a => ¬p a) = s \ s.filter p :=
  ext <| by
    simpa only [← mem_filter, ← mem_sdiff, ← and_comm, ← not_and] using fun a =>
      and_congr_right fun h : a ∈ s => (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = filter (· ∉ s₂) s₁ :=
  ext fun _ => by
    simp only [← mem_sdiff, ← mem_filter]

theorem sdiff_eq_self (s₁ s₂ : Finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ := by
  simp [← subset.antisymm_iff]
  constructor <;> intro h
  · trans' s₁ \ s₂ ∩ s₂
    mono
    simp
    
  · calc s₁ \ s₂ ⊇ s₁ \ (s₁ ∩ s₂) := by
        simp [← (· ⊇ ·)]_ ⊇ s₁ \ ∅ := by
        mono using ← (· ⊇ ·)_ ⊇ s₁ := by
        simp [← (· ⊇ ·)]
    

theorem filter_union_filter_neg_eq [DecidablePred fun a => ¬p a] (s : Finset α) :
    (s.filter p ∪ s.filter fun a => ¬p a) = s := by
  simp only [← filter_not, ← union_sdiff_of_subset (filter_subset p s)]

theorem filter_inter_filter_neg_eq [DecidablePred fun a => ¬p a] (s : Finset α) :
    (s.filter p ∩ s.filter fun a => ¬p a) = ∅ := by
  simp only [← filter_not, ← inter_sdiff_self]

theorem subset_union_elim {s : Finset α} {t₁ t₂ : Set α} (h : ↑s ⊆ t₁ ∪ t₂) :
    ∃ s₁ s₂ : Finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ := by
  classical
  refine' ⟨s.filter (· ∈ t₁), s.filter (· ∉ t₁), _, _, _⟩
  · simp [← filter_union_right, ← em]
    
  · intro x
    simp
    
  · intro x
    simp
    intro hx hx₂
    refine' ⟨Or.resolve_left (h hx) hx₂, hx₂⟩
    

-- We can simplify an application of filter where the decidability is inferred in "the wrong way"
@[simp]
theorem filter_congr_decidable {α} (s : Finset α) (p : α → Prop) (h : DecidablePred p) [DecidablePred p] :
    @filter α p h s = s.filter p := by
  congr

section Classical

open Classical

/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
  simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
  instance for decidability.
-/
noncomputable instance {α : Type _} : HasSep α (Finset α) :=
  ⟨fun p x => x.filter p⟩

@[simp]
theorem sep_def {α : Type _} (s : Finset α) (p : α → Prop) : { x ∈ s | p x } = s.filter p :=
  rfl

end Classical

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter(eq b)`.
theorem filter_eq [DecidableEq β] (s : Finset β) (b : β) : s.filter (Eq b) = ite (b ∈ s) {b} ∅ := by
  split_ifs
  · ext
    simp only [← mem_filter, ← mem_singleton]
    exact
      ⟨fun h => h.2.symm, by
        rintro ⟨h⟩
        exact ⟨h, rfl⟩⟩
    
  · ext
    simp only [← mem_filter, ← not_and, ← iff_falseₓ, ← not_mem_empty]
    rintro m ⟨e⟩
    exact h m
    

/-- After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
theorem filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a = b) = ite (b ∈ s) {b} ∅ :=
  trans (filter_congr fun _ _ => ⟨Eq.symm, Eq.symm⟩) (filter_eq s b)

theorem filter_ne [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => b ≠ a) = s.erase b := by
  ext
  simp only [← mem_filter, ← mem_erase, ← Ne.def]
  tauto

theorem filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (s.filter fun a => a ≠ b) = s.erase b :=
  trans (filter_congr fun _ _ => ⟨Ne.symm, Ne.symm⟩) (filter_ne s b)

end Filter

/-! ### range -/


section Range

variable {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : Finset ℕ :=
  ⟨_, nodup_range n⟩

@[simp]
theorem range_coe (n : ℕ) : (range n).1 = Multiset.range n :=
  rfl

@[simp]
theorem mem_range : m ∈ range n ↔ m < n :=
  mem_range

@[simp]
theorem range_zero : range 0 = ∅ :=
  rfl

@[simp]
theorem range_one : range 1 = {0} :=
  rfl

theorem range_succ : range (succ n) = insert n (range n) :=
  eq_of_veq <| (range_succ n).trans <| (ndinsert_of_not_mem not_mem_range_self).symm

theorem range_add_one : range (n + 1) = insert n (range n) :=
  range_succ

@[simp]
theorem not_mem_range_self : n ∉ range n :=
  not_mem_range_self

@[simp]
theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
  Multiset.self_mem_range_succ n

@[simp]
theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m :=
  range_subset

theorem range_mono : Monotone range := fun _ _ => range_subset.2

theorem mem_range_succ_iff {a b : ℕ} : a ∈ Finset.range b.succ ↔ a ≤ b :=
  Finset.mem_range.trans Nat.lt_succ_iffₓ

theorem mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n :=
  (mem_range.1 hx).le

theorem mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
  ne_of_gtₓ <| tsub_pos_of_lt <| mem_range.1 hx

@[simp]
theorem nonempty_range_iff : (range n).Nonempty ↔ n ≠ 0 :=
  ⟨fun ⟨k, hk⟩ => ((zero_le k).trans_lt <| mem_range.1 hk).ne', fun h => ⟨0, mem_range.2 <| pos_iff_ne_zero.2 h⟩⟩

@[simp]
theorem range_eq_empty_iff : range n = ∅ ↔ n = 0 := by
  rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]

theorem nonempty_range_succ : (range <| n + 1).Nonempty :=
  nonempty_range_iff.2 n.succ_ne_zero

end Range

-- useful rules for calculations with quantifiers
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : Finset α) ∧ p x) ↔ False := by
  simp only [← not_mem_empty, ← false_andₓ, ← exists_false]

theorem exists_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by
  simp only [← mem_insert, ← or_and_distrib_right, ← exists_or_distrib, ← exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : Finset α) → p x) ↔ True :=
  iff_true_intro fun _ => False.elim

theorem forall_mem_insert [DecidableEq α] (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [← mem_insert, ← or_imp_distrib, ← forall_and_distrib, ← forall_eq]

end Finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def notMemRangeEquiv (k : ℕ) : { n // n ∉ range k } ≃ ℕ where
  toFun := fun i => i.1 - k
  invFun := fun j =>
    ⟨j + k, by
      simp ⟩
  left_inv := fun j => by
    rw [Subtype.ext_iff_val]
    apply tsub_add_cancel_of_le
    simpa using j.2
  right_inv := fun j => add_tsub_cancel_right _ _

@[simp]
theorem coe_not_mem_range_equiv (k : ℕ) : (notMemRangeEquiv k : { n // n ∉ range k } → ℕ) = fun i => i - k :=
  rfl

@[simp]
theorem coe_not_mem_range_equiv_symm (k : ℕ) :
    ((notMemRangeEquiv k).symm : ℕ → { n // n ∉ range k }) = fun j =>
      ⟨j + k, by
        simp ⟩ :=
  rfl

/-! ### dedup on list and multiset -/


namespace Multiset

variable [DecidableEq α]

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def toFinset (s : Multiset α) : Finset α :=
  ⟨_, nodup_dedup s⟩

@[simp]
theorem to_finset_val (s : Multiset α) : s.toFinset.1 = s.dedup :=
  rfl

theorem to_finset_eq {s : Multiset α} (n : Nodup s) : Finset.mk s n = s.toFinset :=
  Finset.val_inj.1 n.dedup.symm

theorem Nodup.to_finset_inj {l l' : Multiset α} (hl : Nodup l) (hl' : Nodup l') (h : l.toFinset = l'.toFinset) :
    l = l' := by
  simpa [to_finset_eq hl, to_finset_eq hl'] using h

@[simp]
theorem mem_to_finset {a : α} {s : Multiset α} : a ∈ s.toFinset ↔ a ∈ s :=
  mem_dedup

@[simp]
theorem to_finset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl

@[simp]
theorem to_finset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons

@[simp]
theorem to_finset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [singleton_eq_cons, to_finset_cons, to_finset_zero, IsLawfulSingleton.insert_emptyc_eq]

@[simp]
theorem to_finset_add (s t : Multiset α) : toFinset (s + t) = toFinset s ∪ toFinset t :=
  Finset.ext <| by
    simp

@[simp]
theorem to_finset_nsmul (s : Multiset α) : ∀ (n : ℕ) (hn : n ≠ 0), (n • s).toFinset = s.toFinset
  | 0, h => by
    contradiction
  | n + 1, h => by
    by_cases' n = 0
    · rw [h, zero_addₓ, one_nsmul]
      
    · rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, Finset.union_idempotent]
      

@[simp]
theorem to_finset_inter (s t : Multiset α) : toFinset (s ∩ t) = toFinset s ∩ toFinset t :=
  Finset.ext <| by
    simp

@[simp]
theorem to_finset_union (s t : Multiset α) : (s ∪ t).toFinset = s.toFinset ∪ t.toFinset := by
  ext <;> simp

@[simp]
theorem to_finset_eq_empty {m : Multiset α} : m.toFinset = ∅ ↔ m = 0 :=
  Finset.val_inj.symm.trans Multiset.dedup_eq_zero

@[simp]
theorem to_finset_subset (s t : Multiset α) : s.toFinset ⊆ t.toFinset ↔ s ⊆ t := by
  simp only [← Finset.subset_iff, ← Multiset.subset_iff, ← Multiset.mem_to_finset]

end Multiset

namespace Finset

@[simp]
theorem val_to_finset [DecidableEq α] (s : Finset α) : s.val.toFinset = s := by
  ext
  rw [Multiset.mem_to_finset, ← mem_def]

theorem val_le_iff_val_subset {a : Finset α} {b : Multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
  Multiset.le_iff_subset a.Nodup

end Finset

namespace List

variable [DecidableEq α] {l l' : List α} {a : α}

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def toFinset (l : List α) : Finset α :=
  Multiset.toFinset l

@[simp]
theorem to_finset_val (l : List α) : l.toFinset.1 = (l.dedup : Multiset α) :=
  rfl

theorem to_finset_eq (n : Nodupₓ l) : @Finset.mk α l n = l.toFinset :=
  Multiset.to_finset_eq n

@[simp]
theorem mem_to_finset : a ∈ l.toFinset ↔ a ∈ l :=
  mem_dedup

@[simp]
theorem to_finset_nil : toFinset (@nil α) = ∅ :=
  rfl

@[simp]
theorem to_finset_cons : toFinset (a :: l) = insert a (toFinset l) :=
  Finset.eq_of_veq <| by
    by_cases' h : a ∈ l <;> simp [← Finset.insert_val', ← Multiset.dedup_cons, ← h]

theorem to_finset_surj_on : Set.SurjOn toFinset { l : List α | l.Nodup } Set.Univ := by
  rintro ⟨⟨l⟩, hl⟩ _
  exact ⟨l, hl, (to_finset_eq hl).symm⟩

theorem to_finset_surjective : Surjective (toFinset : List α → Finset α) := fun s =>
  let ⟨l, _, hls⟩ := to_finset_surj_on (Set.mem_univ s)
  ⟨l, hls⟩

theorem to_finset_eq_iff_perm_dedup : l.toFinset = l'.toFinset ↔ l.dedup ~ l'.dedup := by
  simp [← Finset.ext_iff, ← perm_ext (nodup_dedup _) (nodup_dedup _)]

theorem toFinset.ext_iff {a b : List α} : a.toFinset = b.toFinset ↔ ∀ x, x ∈ a ↔ x ∈ b := by
  simp only [← Finset.ext_iff, ← mem_to_finset]

theorem toFinset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset :=
  toFinset.ext_iff.mpr

theorem to_finset_eq_of_perm (l l' : List α) (h : l ~ l') : l.toFinset = l'.toFinset :=
  to_finset_eq_iff_perm_dedup.mpr h.dedup

theorem perm_of_nodup_nodup_to_finset_eq (hl : Nodupₓ l) (hl' : Nodupₓ l') (h : l.toFinset = l'.toFinset) : l ~ l' := by
  rw [← Multiset.coe_eq_coe]
  exact Multiset.Nodup.to_finset_inj hl hl' h

@[simp]
theorem to_finset_append : toFinset (l ++ l') = l.toFinset ∪ l'.toFinset := by
  induction' l with hd tl hl
  · simp
    
  · simp [← hl]
    

@[simp]
theorem to_finset_reverse {l : List α} : toFinset l.reverse = l.toFinset :=
  to_finset_eq_of_perm _ _ (reverse_perm l)

theorem to_finset_repeat_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (List.repeat a n).toFinset = {a} := by
  ext x
  simp [← hn, ← List.mem_repeat]

@[simp]
theorem to_finset_union (l l' : List α) : (l ∪ l').toFinset = l.toFinset ∪ l'.toFinset := by
  ext
  simp

@[simp]
theorem to_finset_inter (l l' : List α) : (l ∩ l').toFinset = l.toFinset ∩ l'.toFinset := by
  ext
  simp

@[simp]
theorem to_finset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp

end List

namespace Finset

/-! ### map -/


section Map

open Function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩

@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl

@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl

variable {f : α ↪ β} {s : Finset α}

@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  mem_map.trans <| by
    simp only [← exists_prop] <;> rfl

@[simp]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s := by
  rw [mem_map]
  exact
    ⟨by
      rintro ⟨a, H, rfl⟩
      simpa, fun h =>
      ⟨_, h, by
        simp ⟩⟩

theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2

theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2

theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀, ∀ y ∈ s.map f, ∀, p y H) ↔ ∀, ∀ x ∈ s, ∀, p (f x) (mem_map_of_mem _ H) :=
  ⟨fun h y hy => h (f y) (mem_map_of_mem _ hy), fun h x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact h _ hy⟩

theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.Prop

@[simp, norm_cast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext fun x => mem_map.trans Set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.Range f :=
  calc
    ↑(s.map f) = f '' s := coe_map f s
    _ ⊆ Set.Range f := Set.image_subset_range f ↑s
    

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem map_perm {σ : Equivₓ.Perm α} (hs : { a | σ a ≠ a } ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs

theorem map_to_finset [DecidableEq α] [DecidableEq β] {s : Multiset α} : s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by
    simp only [← mem_map, ← Multiset.mem_map, ← exists_prop, ← Multiset.mem_to_finset]

@[simp]
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by
    simpa only [← mem_map, ← exists_prop] using exists_eq_right

@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) : HEq (s.map (Equivₓ.cast h).toEmbedding) s := by
  subst h
  simp

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by
    simp only [← map_val, ← Multiset.map_map] <;> rfl

theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, embedding.trans, Function.comp, h_comm]

theorem _root_.function.semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β} (h : Function.Semiconj f ga gb) :
    Function.Semiconj (map f) (map ga) (map gb) := fun s => map_comm h

theorem _root_.function.commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.finset_map

@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h x xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs, fun h => by
    simp [← subset_def, ← map_subset_map h]⟩

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLeIff (map f) fun _ _ => map_subset_map

@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).Injective.eq_iff

theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).Injective

@[simp]
theorem map_embedding_apply : mapEmbedding f s = map f s :=
  rfl

theorem map_filter {p : β → Prop} [DecidablePred p] : (s.map f).filter p = (s.filter (p ∘ f)).map f :=
  eq_of_veq (map_filter _ _ _)

/-- A helper lemma to produce a default proof for `finset.map_disj_union`. -/
theorem map_disj_union_aux {f : α ↪ β} {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ → a ∉ s₂) ↔ ∀ a, a ∈ map f s₁ → a ∉ map f s₂ :=
  by
  simp_rw [forall_mem_map, mem_map']

theorem map_disj_union {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := map_disj_union_aux.1 h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _

/-- A version of `finset.map_disj_union` for writing in the other direction. -/
theorem map_disj_union' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := map_disj_union_aux.2 h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disj_union _ _ _

theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  coe_injective <| by
    simp only [← coe_map, ← coe_union, ← Set.image_union]

theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  coe_injective <| by
    simp only [← coe_map, ← coe_inter, ← Set.image_inter f.injective]

@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by
    simp only [← coe_map, ← coe_singleton, ← Set.image_singleton]

@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [← insert_eq, ← map_union, ← map_singleton]

@[simp]
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f =
      cons (f a) (s.map f)
        (by
          simpa using ha) :=
  eq_of_veq <| Multiset.map_cons f a s.val

@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun a m => ne_empty_of_mem (mem_map_of_mem _ m) h, fun e => e.symm ▸ rfl⟩

@[simp]
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne.def, map_eq_empty]

alias map_nonempty ↔ _ Nonempty.map

theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by
    rw [map_val, attach_val] <;> exact attach_map_val _

theorem disjoint_range_add_left_embedding (a b : ℕ) : Disjoint (range a) (map (addLeftEmbedding a) (range b)) := by
  intro k hk
  simp only [← exists_prop, ← mem_range, ← inf_eq_inter, ← mem_map, ← add_left_embedding_apply, ← mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [ha] using hk.1

theorem disjoint_range_add_right_embedding (a b : ℕ) : Disjoint (range a) (map (addRightEmbedding a) (range b)) := by
  intro k hk
  simp only [← exists_prop, ← mem_range, ← inf_eq_inter, ← mem_map, ← add_left_embedding_apply, ← mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [ha] using hk.1

end Map

theorem range_add_one' (n : ℕ) : range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => Nat.succ.injₓ⟩) :=
  by
  ext (⟨⟩ | ⟨n⟩) <;> simp [← Nat.succ_eq_add_one, ← Nat.zero_lt_succₓ n]

/-! ### image -/


section Image

variable [DecidableEq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset

@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl

@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).Image f = ∅ :=
  rfl

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

@[simp]
theorem mem_image : b ∈ s.Image f ↔ ∃ a ∈ s, f a = b := by
  simp only [← mem_def, ← image_val, ← mem_dedup, ← Multiset.mem_map, ← exists_prop]

theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.Image f :=
  mem_image.2 ⟨_, h, rfl⟩

@[simp]
theorem mem_image_const : c ∈ s.Image (const α b) ↔ s.Nonempty ∧ b = c := by
  rw [mem_image]
  simp only [← exists_prop, ← const_apply, ← exists_and_distrib_right]
  rfl

theorem mem_image_const_self : b ∈ s.Image (const α b) ↔ s.Nonempty :=
  mem_image_const.trans <| and_iff_left rfl

instance [CanLift β α] : CanLift (Finset β) (Finset α) where
  cond := fun s => ∀, ∀ x ∈ s, ∀, CanLift.Cond α x
  coe := image CanLift.coe
  prf := by
    rintro ⟨⟨l⟩, hd : l.nodup⟩ hl
    lift l to List α using hl
    exact
      ⟨⟨l, hd.of_map _⟩,
        ext fun a => by
          simp ⟩

theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by
  ext
  simp_rw [mem_image]
  exact
    bex_congr fun x hx => by
      rw [h hx]

theorem _root_.function.injective.mem_finset_image (hf : Injective f) : f a ∈ s.Image f ↔ a ∈ s := by
  refine' ⟨fun h => _, Finset.mem_image_of_mem f⟩
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  exact hf HEq ▸ hy

theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀, ∀ x ∈ s, ∀, f x ∈ t) :
    (t.filter fun y => y ∈ s.Image f) = s.Image f := by
  ext
  rw [mem_filter, mem_image]
  simp only [← and_imp, ← exists_prop, ← and_iff_right_iff_imp, ← exists_imp_distrib]
  rintro x xel rfl
  exact h _ xel

theorem fiber_nonempty_iff_mem_image (f : α → β) (s : Finset α) (y : β) :
    (s.filter fun x => f x = y).Nonempty ↔ y ∈ s.Image f := by
  simp [← Finset.Nonempty]

@[simp, norm_cast]
theorem coe_image {f : α → β} : ↑(s.Image f) = f '' ↑s :=
  Set.ext fun _ => mem_image.trans Set.mem_image_iff_bex.symm

protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.Image f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, mem_image_of_mem f ha⟩

@[simp]
theorem Nonempty.image_iff (f : α → β) : (s.Image f).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx, _⟩ := mem_image.mp hy
    ⟨x, hx⟩,
    fun h => h.Image f⟩

theorem image_to_finset [DecidableEq α] {s : Multiset α} : s.toFinset.Image f = (s.map f).toFinset :=
  ext fun _ => by
    simp only [← mem_image, ← Multiset.mem_to_finset, ← exists_prop, ← Multiset.mem_map]

theorem image_val_of_inj_on (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_on H).dedup

@[simp]
theorem image_id [DecidableEq α] : s.Image id = s :=
  ext fun _ => by
    simp only [← mem_image, ← exists_prop, ← id, ← exists_eq_right]

@[simp]
theorem image_id' [DecidableEq α] : (s.Image fun x => x) = s :=
  image_id

theorem image_image [DecidableEq γ] {g : β → γ} : (s.Image f).Image g = s.Image (g ∘ f) :=
  eq_of_veq <| by
    simp only [← image_val, ← dedup_map_dedup_eq, ← Multiset.map_map]

theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.Image g).Image f = (s.Image f').Image g' := by
  simp_rw [image_image, comp, h_comm]

theorem _root_.function.semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s => image_comm h

theorem _root_.function.commute.finset_image [DecidableEq α] {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  h.finset_image

theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.Image f ⊆ s₂.Image f := by
  simp only [← subset_def, ← image_val, ← subset_dedup', ← dedup_subset', ← Multiset.map_subset_map h]

theorem image_subset_iff : s.Image f ⊆ t ↔ ∀, ∀ x ∈ s, ∀, f x ∈ t :=
  calc
    s.Image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by
      norm_cast
    _ ↔ _ := Set.image_subset_iff
    

theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image

theorem image_subset_image_iff {t : Finset α} (hf : Injective f) : s.Image f ⊆ t.Image f ↔ s ⊆ t := by
  simp_rw [← coe_subset]
  push_cast
  exact Set.image_subset_image_iff hf

theorem coe_image_subset_range : ↑(s.Image f) ⊆ Set.Range f :=
  calc
    ↑(s.Image f) = f '' ↑s := coe_image
    _ ⊆ Set.Range f := Set.image_subset_range f ↑s
    

theorem image_filter {p : β → Prop} [DecidablePred p] : (s.Image f).filter p = (s.filter (p ∘ f)).Image f :=
  ext fun b => by
    simp only [← mem_filter, ← mem_image, ← exists_prop] <;>
      exact
        ⟨by
          rintro ⟨⟨x, h1, rfl⟩, h2⟩ <;> exact ⟨x, ⟨h1, h2⟩, rfl⟩, by
          rintro ⟨x, ⟨h1, h2⟩, rfl⟩ <;> exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) : (s₁ ∪ s₂).Image f = s₁.Image f ∪ s₂.Image f :=
  ext fun _ => by
    simp only [← mem_image, ← mem_union, ← exists_prop, ← or_and_distrib_right, ← exists_or_distrib]

theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) : (s ∩ t).Image f ⊆ s.Image f ∩ t.Image f :=
  subset_inter (image_subset_image <| inter_subset_left _ _) <| image_subset_image <| inter_subset_right _ _

theorem image_inter_of_inj_on [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Set.InjOn f (s ∪ t)) :
    (s ∩ t).Image f = s.Image f ∩ t.Image f :=
  (image_inter_subset _ _ _).antisymm fun x => by
    simp only [← mem_inter, ← mem_image]
    rintro ⟨⟨a, ha, rfl⟩, b, hb, h⟩
    exact
      ⟨a,
        ⟨ha, by
          rwa [← hf (Or.inr hb) (Or.inl ha) h]⟩,
        rfl⟩

theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).Image f = s₁.Image f ∩ s₂.Image f :=
  image_inter_of_inj_on _ _ <| hf.InjOn _

@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext fun x => by
    simpa only [← mem_image, ← exists_prop, ← mem_singleton, ← exists_eq_left] using eq_comm

@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).Image f = insert (f a) (s.Image f) := by
  simp only [← insert_eq, ← image_singleton, ← image_union]

theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.Image f).erase (f a) ⊆ (s.erase a).Image f := by
  simp only [← subset_iff, ← and_imp, ← exists_prop, ← mem_image, ← exists_imp_distrib, ← mem_erase]
  rintro b hb x hx rfl
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩

@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.erase a).Image f = (s.Image f).erase (f a) := by
  refine' (erase_image_subset_image_erase _ _ _).antisymm' fun b => _
  simp only [← mem_image, ← exists_prop, ← mem_erase]
  rintro ⟨a', ⟨haa', ha'⟩, rfl⟩
  exact ⟨hf.ne haa', a', ha', rfl⟩

@[simp]
theorem image_eq_empty : s.Image f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun a m => ne_empty_of_mem (mem_image_of_mem _ m) h, fun e => e.symm ▸ rfl⟩

theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ} (hn : 0 < n)
    (h : ∀ i, f (i % n) = f i) : a ∈ Set.Range f ↔ a ∈ (Finset.range n).Image fun i => f i := by
  constructor
  · rintro ⟨i, hi⟩
    simp only [← mem_image, ← exists_prop, ← mem_range]
    exact ⟨i % n, Nat.mod_ltₓ i hn, (rfl.congr hi).mp (h i)⟩
    
  · rintro h
    simp only [← mem_image, ← exists_prop, ← Set.mem_range, ← mem_range] at *
    rcases h with ⟨i, hi, ha⟩
    exact ⟨i, ha⟩
    

theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ} (hn : 0 < n)
    (h : ∀ i, f (i % n) = f i) : a ∈ Set.Range f ↔ a ∈ (Finset.range n).Image fun i => f i :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by
    simpa [← h]
  have hn' : 0 < (n : ℤ) := Int.coe_nat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.mod_nonneg _ (ne_of_gtₓ hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.coe_nat_lt, Int.to_nat_of_nonneg this] <;> exact ⟨Int.mod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by
      rw [Int.mod_eq_of_lt (Int.coe_zero_le _) (Int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩

theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b

@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.Image Subtype.val = s :=
  eq_of_veq <| by
    rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]

@[simp]
theorem attach_image_coe [DecidableEq α] {s : Finset α} : s.attach.Image coe = s :=
  Finset.attach_image_val

@[simp]
theorem attach_insert [DecidableEq α] {a : α} {s : Finset α} :
    attach (insert a s) =
      insert (⟨a, mem_insert_self a s⟩ : { x // x ∈ insert a s })
        ((attach s).Image fun x => ⟨x.1, mem_insert_of_mem x.2⟩) :=
  ext fun ⟨x, hx⟩ =>
    ⟨Or.cases_on (mem_insert.1 hx) (fun h : x = a => fun _ => mem_insert.2 <| Or.inl <| Subtype.eq h) fun h : x ∈ s =>
        fun _ => mem_insert_of_mem <| mem_image.2 <| ⟨⟨x, h⟩, mem_attach _ _, Subtype.eq rfl⟩,
      fun _ => Finset.mem_attach _ _⟩

theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.Image f :=
  eq_of_veq (s.map f).2.dedup.symm

theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.Image fun a => b) = singleton b :=
  ext fun b' => by
    simp only [← mem_image, ← exists_prop, ← exists_and_distrib_right, ← h.bex, ← true_andₓ, ← mem_singleton, ← eq_comm]

@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) : (s.erase a).map f = (s.map f).erase (f a) := by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a

/-! ### Subtype -/


/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filter p).attach.map ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩, fun x y H => Subtype.eq <| Subtype.mk.injₓ H⟩

@[simp]
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} : ∀ {a : Subtype p}, a ∈ s.Subtype p ↔ (a : α) ∈ s
  | ⟨a, ha⟩ => by
    simp [← Finset.subtype, ← ha]

theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} : s.Subtype p = ∅ ↔ ∀ x, p x → x ∉ s := by
  simp [← ext_iff, ← Subtype.forall, ← Subtype.coe_mk] <;> rfl

@[mono]
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) := fun s t h x hx =>
  mem_subtype.2 <| h <| mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp]
theorem subtype_map (p : α → Prop) [DecidablePred p] : (s.Subtype p).map (Embedding.subtype _) = s.filter p := by
  ext x
  simp [← and_comm _ (_ = _), ← @And.left_comm _ (_ = _), ← and_comm (p x) (x ∈ s)]

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] (h : ∀, ∀ x ∈ s, ∀, p x) :
    (s.Subtype p).map (Embedding.subtype _) = s := by
  rw [subtype_map, filter_true_of_mem h]

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : a ∈ s.map (Embedding.subtype _)) : p a := by
  rcases mem_map.1 h with ⟨x, hx, rfl⟩
  exact x.2

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α} (h : ¬p a) :
    a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) ⊆ t := by
  intro a ha
  rw [mem_coe] at ha
  convert property_of_mem_map_subtype s ha

theorem subset_image_iff {s : Set α} : ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.Image f = t := by
  constructor
  swap
  · rintro ⟨t, ht, rfl⟩
    rw [coe_image]
    exact Set.image_subset f ht
    
  intro h
  let this : CanLift β s := ⟨f ∘ coe, fun y => y ∈ f '' s, fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
  lift t to Finset s using h
  refine' ⟨t.map (embedding.subtype _), map_subtype_subset _, _⟩
  ext y
  simp

theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).Image Nat.succ := by
  induction' n with k hk
  · simp
    
  nth_rw 1[range_succ]
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  simp

end Image

theorem _root_.multiset.to_finset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.Image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm

section ToList

/-- Produce a list of the elements in the finite set using choice. -/
@[reducible]
noncomputable def toList (s : Finset α) : List α :=
  s.1.toList

theorem nodup_to_list (s : Finset α) : s.toList.Nodup := by
  rw [to_list, ← Multiset.coe_nodup, Multiset.coe_to_list]
  exact s.nodup

@[simp]
theorem mem_to_list {a : α} (s : Finset α) : a ∈ s.toList ↔ a ∈ s := by
  rw [to_list, ← Multiset.mem_coe, Multiset.coe_to_list]
  exact Iff.rfl

@[simp]
theorem to_list_empty : (∅ : Finset α).toList = [] := by
  simp [← to_list]

@[simp, norm_cast]
theorem coe_to_list (s : Finset α) : (s.toList : Multiset α) = s.val := by
  classical
  ext
  simp

@[simp]
theorem to_list_to_finset [DecidableEq α] (s : Finset α) : s.toList.toFinset = s := by
  ext
  simp

theorem exists_list_nodup_eq [DecidableEq α] (s : Finset α) : ∃ l : List α, l.Nodup ∧ l.toFinset = s :=
  ⟨s.toList, s.nodup_to_list, s.to_list_to_finset⟩

theorem to_list_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext (nodup_to_list _)
        (by
          simp [← h, ← nodup_to_list s])).2
    fun x => by
    simp only [← List.mem_cons_iff, ← Finset.mem_to_list, ← Finset.mem_cons]

theorem to_list_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ to_list_cons _

end ToList

section BUnion

/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/


variable [DecidableEq β] {s s₁ s₂ : Finset α} {t t₁ t₂ : α → Finset β}

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion (s : Finset α) (t : α → Finset β) : Finset β :=
  (s.1.bind fun a => (t a).1).toFinset

@[simp]
theorem bUnion_val (s : Finset α) (t : α → Finset β) : (s.bUnion t).1 = (s.1.bind fun a => (t a).1).dedup :=
  rfl

@[simp]
theorem bUnion_empty : Finset.bUnion ∅ t = ∅ :=
  rfl

@[simp]
theorem mem_bUnion {b : β} : b ∈ s.bUnion t ↔ ∃ a ∈ s, b ∈ t a := by
  simp only [← mem_def, ← bUnion_val, ← mem_dedup, ← mem_bind, ← exists_prop]

@[simp, norm_cast]
theorem coe_bUnion : (s.bUnion t : Set β) = ⋃ x ∈ (s : Set α), t x := by
  simp only [← Set.ext_iff, ← mem_bUnion, ← Set.mem_Union, ← iff_selfₓ, ← mem_coe, ← implies_true_iff]

@[simp]
theorem bUnion_insert [DecidableEq α] {a : α} : (insert a s).bUnion t = t a ∪ s.bUnion t :=
  ext fun x => by
    simp only [← mem_bUnion, ← exists_prop, ← mem_union, ← mem_insert, ← or_and_distrib_right, ← exists_or_distrib, ←
      exists_eq_left]

-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]
theorem bUnion_congr (hs : s₁ = s₂) (ht : ∀, ∀ a ∈ s₁, ∀, t₁ a = t₂ a) : s₁.bUnion t₁ = s₂.bUnion t₂ :=
  ext fun x => by
    simp (config := { contextual := true })[← hs, ← ht]

theorem bUnion_subset {s' : Finset β} : s.bUnion t ⊆ s' ↔ ∀, ∀ x ∈ s, ∀, t x ⊆ s' := by
  simp only [← subset_iff, ← mem_bUnion] <;> exact ⟨fun H a ha b hb => H ⟨a, ha, hb⟩, fun H b ⟨a, ha, hb⟩ => H a ha hb⟩

@[simp]
theorem singleton_bUnion {a : α} : Finset.bUnion {a} t = t a := by
  classical
  rw [← insert_emptyc_eq, bUnion_insert, bUnion_empty, union_empty]

theorem bUnion_inter (s : Finset α) (f : α → Finset β) (t : Finset β) : s.bUnion f ∩ t = s.bUnion fun x => f x ∩ t := by
  ext x
  simp only [← mem_bUnion, ← mem_inter]
  tauto

theorem inter_bUnion (t : Finset β) (s : Finset α) (f : α → Finset β) : t ∩ s.bUnion f = s.bUnion fun x => t ∩ f x := by
  rw [inter_comm, bUnion_inter] <;> simp [← inter_comm]

theorem image_bUnion [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.Image f).bUnion t = s.bUnion fun a => t (f a) :=
  have := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by
    simp only [← image_insert, ← bUnion_insert, ← ih]

theorem bUnion_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.bUnion t).Image f = s.bUnion fun a => (t a).Image f :=
  have := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by
    simp only [← bUnion_insert, ← image_union, ← ih]

theorem bUnion_bUnion [DecidableEq γ] (s : Finset α) (f : α → Finset β) (g : β → Finset γ) :
    (s.bUnion f).bUnion g = s.bUnion fun a => (f a).bUnion g := by
  ext
  simp only [← Finset.mem_bUnion, ← exists_prop]
  simp_rw [← exists_and_distrib_right, ← exists_and_distrib_left, and_assoc]
  rw [exists_comm]

theorem bind_to_finset [DecidableEq α] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).toFinset = s.toFinset.bUnion fun a => (t a).toFinset :=
  ext fun x => by
    simp only [← Multiset.mem_to_finset, ← mem_bUnion, ← Multiset.mem_bind, ← exists_prop]

theorem bUnion_mono (h : ∀, ∀ a ∈ s, ∀, t₁ a ⊆ t₂ a) : s.bUnion t₁ ⊆ s.bUnion t₂ := by
  have : ∀ b a, a ∈ s → b ∈ t₁ a → ∃ a : α, a ∈ s ∧ b ∈ t₂ a := fun b a ha hb =>
    ⟨a, ha, Finset.mem_of_subset (h a ha) hb⟩
  simpa only [← subset_iff, ← mem_bUnion, ← exists_imp_distrib, ← and_imp, ← exists_prop]

theorem bUnion_subset_bUnion_of_subset_left (t : α → Finset β) (h : s₁ ⊆ s₂) : s₁.bUnion t ⊆ s₂.bUnion t := by
  intro x
  simp only [← and_imp, ← mem_bUnion, ← exists_prop]
  exact Exists.imp fun a ha => ⟨h ha.1, ha.2⟩

theorem subset_bUnion_of_mem (u : α → Finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.bUnion u :=
  singleton_bUnion.Superset.trans <| bUnion_subset_bUnion_of_subset_left u <| singleton_subset_iff.2 xs

@[simp]
theorem bUnion_subset_iff_forall_subset {α β : Type _} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → Finset β} : s.bUnion f ⊆ t ↔ ∀, ∀ x ∈ s, ∀, f x ⊆ t :=
  ⟨fun h x hx => (subset_bUnion_of_mem f hx).trans h, fun h x hx =>
    let ⟨a, ha₁, ha₂⟩ := mem_bUnion.mp hx
    h _ ha₁ ha₂⟩

theorem bUnion_singleton {f : α → β} : (s.bUnion fun a => {f a}) = s.Image f :=
  ext fun x => by
    simp only [← mem_bUnion, ← mem_image, ← mem_singleton, ← eq_comm]

@[simp]
theorem bUnion_singleton_eq_self [DecidableEq α] : s.bUnion (singleton : α → Finset α) = s := by
  rw [bUnion_singleton]
  exact image_id

theorem filter_bUnion (s : Finset α) (f : α → Finset β) (p : β → Prop) [DecidablePred p] :
    (s.bUnion f).filter p = s.bUnion fun a => (f a).filter p := by
  ext b
  simp only [← mem_bUnion, ← exists_prop, ← mem_filter]
  constructor
  · rintro ⟨⟨a, ha, hba⟩, hb⟩
    exact ⟨a, ha, hba, hb⟩
    
  · rintro ⟨a, ha, hba, hb⟩
    exact ⟨⟨a, ha, hba⟩, hb⟩
    

theorem bUnion_filter_eq_of_maps_to [DecidableEq α] {s : Finset α} {t : Finset β} {f : α → β}
    (h : ∀, ∀ x ∈ s, ∀, f x ∈ t) : (t.bUnion fun a => s.filter fun c => f c = a) = s :=
  ext fun b => by
    simpa using h b

theorem image_bUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.Image g).bUnion fun a => s.filter fun c => g c = a) = s :=
  bUnion_filter_eq_of_maps_to fun x => mem_image_of_mem g

theorem erase_bUnion (f : α → Finset β) (s : Finset α) (b : β) :
    (s.bUnion f).erase b = s.bUnion fun x => (f x).erase b := by
  ext
  simp only [← Finset.mem_bUnion, ← iff_selfₓ, ← exists_and_distrib_left, ← Finset.mem_erase]

@[simp]
theorem bUnion_nonempty : (s.bUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty := by
  simp [← Finset.Nonempty, exists_and_distrib_left, ← @exists_swap α]

theorem Nonempty.bUnion (hs : s.Nonempty) (ht : ∀, ∀ x ∈ s, ∀, (t x).Nonempty) : (s.bUnion t).Nonempty :=
  bUnion_nonempty.2 <| hs.imp fun x hx => ⟨hx, ht x hx⟩

end BUnion

/-! ### disjoint -/


--TODO@Yaël: Kill lemmas duplicate with `boolean_algebra`
section Disjoint

variable [DecidableEq α] [DecidableEq β] {f : α → β} {s t u : Finset α} {a b : α}

theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t := by
  simp only [← _root_.disjoint, ← inf_eq_inter, ← le_iff_subset, ← subset_iff, ← mem_inter, ← not_and, ← and_imp] <;>
    rfl

theorem disjoint_val : Disjoint s t ↔ s.1.Disjoint t.1 :=
  disjoint_left

theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff

instance decidableDisjoint (U V : Finset α) : Decidable (Disjoint U V) :=
  decidableOfDecidableOfIff
    (by
      infer_instance)
    eq_bot_iff

theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by
  rw [Disjoint.comm, disjoint_left]

theorem disjoint_iff_ne : Disjoint s t ↔ ∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ t, ∀, a ≠ b := by
  simp only [← disjoint_left, ← imp_not_comm, ← forall_eq']

theorem _root_.disjoint.forall_ne_finset (h : Disjoint s t) (ha : a ∈ s) (hb : b ∈ t) : a ≠ b :=
  disjoint_iff_ne.1 h _ ha _ hb

theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
  not_forall.trans <| exists_congr fun a => not_not.trans mem_inter

theorem disjoint_of_subset_left (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t :=
  disjoint_left.2 fun x m₁ => (disjoint_left.1 d) (h m₁)

theorem disjoint_of_subset_right (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t :=
  disjoint_right.2 fun x m₁ => (disjoint_right.1 d) (h m₁)

@[simp]
theorem disjoint_empty_left (s : Finset α) : Disjoint ∅ s :=
  disjoint_bot_left

@[simp]
theorem disjoint_empty_right (s : Finset α) : Disjoint s ∅ :=
  disjoint_bot_right

@[simp]
theorem disjoint_singleton_left : Disjoint (singleton a) s ↔ a ∉ s := by
  simp only [← disjoint_left, ← mem_singleton, ← forall_eq]

@[simp]
theorem disjoint_singleton_right : Disjoint s (singleton a) ↔ a ∉ s :=
  Disjoint.comm.trans disjoint_singleton_left

@[simp]
theorem disjoint_singleton : Disjoint ({a} : Finset α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton]

@[simp]
theorem disjoint_insert_left : Disjoint (insert a s) t ↔ a ∉ t ∧ Disjoint s t := by
  simp only [← disjoint_left, ← mem_insert, ← or_imp_distrib, ← forall_and_distrib, ← forall_eq]

@[simp]
theorem disjoint_insert_right : Disjoint s (insert a t) ↔ a ∉ s ∧ Disjoint s t :=
  Disjoint.comm.trans <| by
    rw [disjoint_insert_left, Disjoint.comm]

@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp only [← disjoint_left, ← mem_union, ← or_imp_distrib, ← forall_and_distrib]

@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := by
  simp only [← disjoint_right, ← mem_union, ← or_imp_distrib, ← forall_and_distrib]

theorem sdiff_disjoint : Disjoint (t \ s) s :=
  disjoint_left.2 fun a ha => (mem_sdiff.1 ha).2

theorem disjoint_sdiff : Disjoint s (t \ s) :=
  sdiff_disjoint.symm

theorem disjoint_sdiff_inter (s t : Finset α) : Disjoint (s \ t) (s ∩ t) :=
  disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

theorem sdiff_eq_self_iff_disjoint : s \ t = s ↔ Disjoint s t :=
  sdiff_eq_self_iff_disjoint'

theorem sdiff_eq_self_of_disjoint (h : Disjoint s t) : s \ t = s :=
  sdiff_eq_self_iff_disjoint.2 h

theorem disjoint_self_iff_empty (s : Finset α) : Disjoint s s ↔ s = ∅ :=
  disjoint_self

theorem disjoint_bUnion_left {ι : Type _} (s : Finset ι) (f : ι → Finset α) (t : Finset α) :
    Disjoint (s.bUnion f) t ↔ ∀, ∀ i ∈ s, ∀, Disjoint (f i) t := by
  classical
  refine' s.induction _ _
  · simp only [← forall_mem_empty_iff, ← bUnion_empty, ← disjoint_empty_left]
    
  · intro i s his ih
    simp only [← disjoint_union_left, ← bUnion_insert, ← his, ← forall_mem_insert, ← ih]
    

theorem disjoint_bUnion_right {ι : Type _} (s : Finset α) (t : Finset ι) (f : ι → Finset α) :
    Disjoint s (t.bUnion f) ↔ ∀, ∀ i ∈ t, ∀, Disjoint s (f i) := by
  simpa only [← Disjoint.comm] using disjoint_bUnion_left t f s

theorem disjoint_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint (s.filter p) (s.filter q) ↔ ∀, ∀ x ∈ s, ∀, p x → ¬q x := by
  constructor <;> simp (config := { contextual := true })[← disjoint_left]

theorem disjoint_filter_filter {p q : α → Prop} [DecidablePred p] [DecidablePred q] :
    Disjoint s t → Disjoint (s.filter p) (t.filter q) :=
  Disjoint.mono (filter_subset _ _) (filter_subset _ _)

theorem disjoint_filter_filter_neg (s : Finset α) (p : α → Prop) [DecidablePred p] :
    Disjoint (s.filter p) (s.filter fun a => ¬p a) :=
  (disjoint_filter.2 fun a _ => id).symm

@[simp, norm_cast]
theorem disjoint_coe : Disjoint (s : Set α) t ↔ Disjoint s t := by
  rw [Finset.disjoint_left, Set.disjoint_left]
  rfl

@[simp, norm_cast]
theorem pairwise_disjoint_coe {ι : Type _} {s : Set ι} {f : ι → Finset α} :
    s.PairwiseDisjoint (fun i => f i : ι → Set α) ↔ s.PairwiseDisjoint f :=
  forall₅_congr fun _ _ _ _ _ => disjoint_coe

@[simp]
theorem _root_.disjoint.of_image_finset (h : Disjoint (s.Image f) (t.Image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun a ha b hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)

@[simp]
theorem disjoint_image {f : α → β} (hf : Injective f) : Disjoint (s.Image f) (t.Image f) ↔ Disjoint s t := by
  simp only [← disjoint_iff_ne, ← mem_image, ← exists_prop, ← exists_imp_distrib, ← and_imp]
  refine' ⟨fun h a ha b hb hab => h _ _ ha rfl _ _ hb rfl <| congr_arg _ hab, _⟩
  rintro h _ a ha rfl _ b hb rfl
  exact hf.ne (h _ ha _ hb)

@[simp]
theorem disjoint_map {f : α ↪ β} : Disjoint (s.map f) (t.map f) ↔ Disjoint s t := by
  simp_rw [map_eq_image]
  exact disjoint_image f.injective

end Disjoint

/-! ### choose -/


section Choose

variable (p : α → Prop) [DecidablePred p] (l : Finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def chooseX (hp : ∃! a, a ∈ l ∧ p a) : { a // a ∈ l ∧ p a } :=
  Multiset.chooseX p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

section Pairwise

variable {s : Finset α}

theorem pairwise_subtype_iff_pairwise_finset' (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun x : s => f x) ↔ (s : Set α).Pairwise (r on f) := by
  refine'
    ⟨fun h x hx y hy hxy =>
      h ⟨x, hx⟩ ⟨y, hy⟩
        (by
          simpa only [← Subtype.mk_eq_mk, ← Ne.def] ),
      _⟩
  rintro h ⟨x, hx⟩ ⟨y, hy⟩ hxy
  exact h hx hy (subtype.mk_eq_mk.not.mp hxy)

theorem pairwise_subtype_iff_pairwise_finset (r : α → α → Prop) :
    Pairwise (r on fun x : s => x) ↔ (s : Set α).Pairwise r :=
  pairwise_subtype_iff_pairwise_finset' r id

theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
      Pairwise (r on fun a : s => f a) ∧ ∀, ∀ b ∈ s, ∀, r (f a) (f b) ∧ r (f b) (f a) :=
  by
  simp only [← pairwise_subtype_iff_pairwise_finset', ← Finset.coe_cons, ← Set.pairwise_insert, ← Finset.mem_coe, ←
    And.congr_right_iff]
  exact fun hsr =>
    ⟨fun h b hb =>
      h b hb <| by
        rintro rfl
        contradiction,
      fun h b hb _ => h b hb⟩

theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔ Pairwise (r on fun a : s => a) ∧ ∀, ∀ b ∈ s, ∀, r a b ∧ r b a :=
  pairwise_cons' ha r id

end Pairwise

end Finset

namespace Equivₓ

/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β where
  toFun := fun s => s.map e.toEmbedding
  invFun := fun s => s.map e.symm.toEmbedding
  left_inv := fun s => by
    simp [← Finset.map_map]
  right_inv := fun s => by
    simp [← Finset.map_map]

@[simp]
theorem finset_congr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl

@[simp]
theorem finset_congr_refl : (Equivₓ.refl α).finsetCongr = Equivₓ.refl _ := by
  ext
  simp

@[simp]
theorem finset_congr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl

@[simp]
theorem finset_congr_trans (e : α ≃ β) (e' : β ≃ γ) : e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr :=
  by
  ext
  simp [-Finset.mem_map, -Equivₓ.trans_to_embedding]

theorem finset_congr_to_embedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl

/-- Inhabited types are equivalent to `option β` for some `β` by identifying `default α` with `none`.
-/
def sigmaEquivOptionOfInhabited (α : Type u) [Inhabited α] [DecidableEq α] : Σβ : Type u, α ≃ Option β :=
  ⟨{ x : α // x ≠ default },
    { toFun := fun x : α => if h : x = default then none else some ⟨x, h⟩, invFun := Option.elimₓ default coe,
      left_inv := fun x => by
        dsimp' only
        split_ifs <;> simp [*],
      right_inv := by
        rintro (_ | ⟨x, h⟩)
        · simp
          
        · dsimp' only
          split_ifs with hi
          · simpa [← h] using hi
            
          · simp
            
           }⟩

end Equivₓ

namespace Multiset

variable [DecidableEq α]

theorem disjoint_to_finset {m1 m2 : Multiset α} : Disjoint m1.toFinset m2.toFinset ↔ m1.Disjoint m2 := by
  rw [Finset.disjoint_iff_ne]
  refine' ⟨fun h a ha1 ha2 => _, _⟩
  · rw [← Multiset.mem_to_finset] at ha1 ha2
    exact h _ ha1 _ ha2 rfl
    
  · rintro h a ha b hb rfl
    rw [Multiset.mem_to_finset] at ha hb
    exact h ha hb
    

end Multiset

namespace List

variable [DecidableEq α] {l l' : List α}

theorem disjoint_to_finset_iff_disjoint : Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l' :=
  Multiset.disjoint_to_finset

end List

