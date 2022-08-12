/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov
-/
import Mathbin.Data.Set.Finite
import Mathbin.Data.Nat.Modeq
import Mathbin.Algebra.BigOperators.Order

/-!
# Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons.

There are a few variations on this statement, and the conclusion can
be made stronger depending on how many pigeons you know you might
have.

The basic statements of the pigeonhole principle appear in the
following locations:

* `data.finset.basic` has `finset.exists_ne_map_eq_of_card_lt_of_maps_to`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_card_lt`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_infinite`
* `data.fintype.basic` has `fintype.exists_infinite_fiber`
* `data.set.finite` has `set.infinite.exists_ne_map_eq_of_maps_to`

This module gives access to these pigeonhole principles along with 20 more.
The versions vary by:

* using a function between `fintype`s or a function between possibly infinite types restricted to
  `finset`s;
* counting pigeons by a general weight function (`∑ x in s, w x`) or by heads (`finset.card s`);
* using strict or non-strict inequalities;
* establishing upper or lower estimate on the number (or the total weight) of the pigeons in one
  pigeonhole;
* in case when we count pigeons by some weight function `w` and consider a function `f` between
  `finset`s `s` and `t`, we can either assume that each pigeon is in one of the pigeonholes
  (`∀ x ∈ s, f x ∈ t`), or assume that for `y ∉ t`, the total weight of the pigeons in this
  pigeonhole `∑ x in s.filter (λ x, f x = y), w x` is nonpositive or nonnegative depending on
  the inequality we are proving.

Lemma names follow `mathlib` convention (e.g.,
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`); "pigeonhole principle" is mentioned in the
docstrings instead of the names.

## See also

* `ordinal.infinite_pigeonhole`: pigeonhole principle for cardinals, formulated using cofinality;

* `measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure`,
  `measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`: pigeonhole principle in a
  measure space.

## TODO

The `_nsmul` lemmas could be generalized from `linear_ordered_comm_ring` to
`linear_ordered_comm_semiring` if the latter existed (or some combination of
`covariant`/`contravariant` classes once the refactor has gone deep enough). This would allow
deriving the `_mul` lemmas from the `_nsmul` ones.

## Tags

pigeonhole principle
-/


universe u v w

variable {α : Type u} {β : Type v} {M : Type w} [DecidableEq β]

open Nat

open BigOperators

namespace Finset

variable {s : Finset α} {t : Finset β} {f : α → β} {w : α → M} {b : M} {n : ℕ}

/-!
### The pigeonhole principles on `finset`s, pigeons counted by weight

In this section we prove the following version of the pigeonhole principle: if the total weight of a
finite set of pigeons is greater than `n • b`, and they are sorted into `n` pigeonholes, then for
some pigeonhole, the total weight of the pigeons in this pigeonhole is greater than `b`, and a few
variations of this theorem.

The principle is formalized in the following way, see
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`: if `f : α → β` is a function which maps all
elements of `s : finset α` to `t : finset β` and `card t • b < ∑ x in s, w x`, where `w : α → M` is
a weight function taking values in a `linear_ordered_cancel_add_comm_monoid`, then for
some `y ∈ t`, the sum of the weights of all `x ∈ s` such that `f x = y` is greater than `b`.

There are a few bits we can change in this theorem:

* reverse all inequalities, with obvious adjustments to the name;
* replace the assumption `∀ a ∈ s, f a ∈ t` with
  `∀ y ∉ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ 0`,
  and replace `of_maps_to` with `of_sum_fiber_nonpos` in the name;
* use non-strict inequalities assuming `t` is nonempty.

We can do all these variations independently, so we have eight versions of the theorem.
-/


section

variable [LinearOrderedCancelAddCommMonoid M]

/-!
#### Strict inequality versions
-/


/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n • b`, and they are sorted into
`n` pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is
greater than `b`. -/
theorem exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (hb : t.card • b < ∑ x in s, w x) :
    ∃ y ∈ t, b < ∑ x in s.filter fun x => f x = y, w x :=
  exists_lt_of_sum_lt <| by
    simpa only [← sum_fiberwise_of_maps_to hf, ← sum_const]

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n • b`, and they are sorted into `n`
pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is less
than `b`. -/
theorem exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t)
    (hb : (∑ x in s, w x) < t.card • b) : ∃ y ∈ t, (∑ x in s.filter fun x => f x = y, w x) < b :=
  @exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum α β Mᵒᵈ _ _ _ _ _ _ _ hf hb

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ∉ » t)
/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n • b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonpositive,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is greater than `b`. -/
theorem exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
    (ht : ∀ (y) (_ : y ∉ t), (∑ x in s.filter fun x => f x = y, w x) ≤ 0) (hb : t.card • b < ∑ x in s, w x) :
    ∃ y ∈ t, b < ∑ x in s.filter fun x => f x = y, w x :=
  exists_lt_of_sum_lt <|
    calc
      (∑ y in t, b) < ∑ x in s, w x := by
        simpa
      _ ≤ ∑ y in t, ∑ x in s.filter fun x => f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos ht
      

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ∉ » t)
/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n • b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonnegative,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is less than `b`. -/
theorem exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
    (ht : ∀ (y) (_ : y ∉ t), (0 : M) ≤ ∑ x in s.filter fun x => f x = y, w x) (hb : (∑ x in s, w x) < t.card • b) :
    ∃ y ∈ t, (∑ x in s.filter fun x => f x = y, w x) < b :=
  @exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum α β Mᵒᵈ _ _ _ _ _ _ _ ht hb

/-!
#### Non-strict inequality versions
-/


/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n • b`, and
they are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons
in this pigeonhole is greater than or equal to `b`. -/
theorem exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (ht : t.Nonempty)
    (hb : t.card • b ≤ ∑ x in s, w x) : ∃ y ∈ t, b ≤ ∑ x in s.filter fun x => f x = y, w x :=
  exists_le_of_sum_le ht <| by
    simpa only [← sum_fiberwise_of_maps_to hf, ← sum_const]

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n • b`, and they
are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons in
this pigeonhole is less than or equal to `b`. -/
theorem exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (ht : t.Nonempty)
    (hb : (∑ x in s, w x) ≤ t.card • b) : ∃ y ∈ t, (∑ x in s.filter fun x => f x = y, w x) ≤ b :=
  @exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum α β Mᵒᵈ _ _ _ _ _ _ _ hf ht hb

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ∉ » t)
/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n • b`, they
are sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the
pigeons there is nonpositive, then for at least one of these `n` pigeonholes, the total weight of
the pigeons in this pigeonhole is greater than or equal to `b`. -/
theorem exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
    (hf : ∀ (y) (_ : y ∉ t), (∑ x in s.filter fun x => f x = y, w x) ≤ 0) (ht : t.Nonempty)
    (hb : t.card • b ≤ ∑ x in s, w x) : ∃ y ∈ t, b ≤ ∑ x in s.filter fun x => f x = y, w x :=
  exists_le_of_sum_le ht <|
    calc
      (∑ y in t, b) ≤ ∑ x in s, w x := by
        simpa
      _ ≤ ∑ y in t, ∑ x in s.filter fun x => f x = y, w x := sum_le_sum_fiberwise_of_sum_fiber_nonpos hf
      

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (y «expr ∉ » t)
/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n • b`, they are
sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the pigeons
there is nonnegative, then for at least one of these `n` pigeonholes, the total weight of the
pigeons in this pigeonhole is less than or equal to `b`. -/
theorem exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
    (hf : ∀ (y) (_ : y ∉ t), (0 : M) ≤ ∑ x in s.filter fun x => f x = y, w x) (ht : t.Nonempty)
    (hb : (∑ x in s, w x) ≤ t.card • b) : ∃ y ∈ t, (∑ x in s.filter fun x => f x = y, w x) ≤ b :=
  @exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum α β Mᵒᵈ _ _ _ _ _ _ _ hf ht hb

end

variable [LinearOrderedCommRing M]

/-!
### The pigeonhole principles on `finset`s, pigeons counted by heads

In this section we formalize a few versions of the following pigeonhole principle: there is a
pigeonhole with at least as many pigeons as the ceiling of the average number of pigeons across all
pigeonholes.

First, we can use strict or non-strict inequalities. While the versions with non-strict inequalities
are weaker than those with strict inequalities, sometimes it might be more convenient to apply the
weaker version. Second, we can either state that there exists a pigeonhole with at least `n`
pigeons, or state that there exists a pigeonhole with at most `n` pigeons. In the latter case we do
not need the assumption `∀ a ∈ s, f a ∈ t`.

So, we prove four theorems: `finset.exists_lt_card_fiber_of_maps_to_of_mul_lt_card`,
`finset.exists_le_card_fiber_of_maps_to_of_mul_le_card`,
`finset.exists_card_fiber_lt_of_card_lt_mul`, and `finset.exists_card_fiber_le_of_card_le_mul`. -/


/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at least as many pigeons as the ceiling of the average number of pigeons across all pigeonholes. -/
theorem exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (ht : t.card • b < s.card) :
    ∃ y ∈ t, b < (s.filter fun x => f x = y).card := by
  simp_rw [cast_card] at ht⊢
  exact exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf ht

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at least as many pigeons as the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite sets `s` and `t` and a natural number `n` such that
`card t * n < card s`, there exists `y ∈ t` such that its preimage in `s` has more than `n`
elements. -/
theorem exists_lt_card_fiber_of_mul_lt_card_of_maps_to (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (hn : t.card * n < s.card) :
    ∃ y ∈ t, n < (s.filter fun x => f x = y).card := by
  simp only [← card_eq_sum_ones]
  apply exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf
  simpa

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at most as many pigeons as the floor of the average number of pigeons across all pigeonholes. -/
theorem exists_card_fiber_lt_of_card_lt_nsmul (ht : ↑s.card < t.card • b) :
    ∃ y ∈ t, ↑(s.filter fun x => f x = y).card < b := by
  simp_rw [cast_card] at ht⊢
  exact exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at most as many pigeons as the floor of the average number of pigeons across all pigeonholes.  ("The
minimum is at most the mean" specialized to integers.)

More formally, given a function `f`, a finite sets `s` in its domain, a finite set `t` in its
codomain, and a natural number `n` such that `card s < card t * n`, there exists `y ∈ t` such that
its preimage in `s` has less than `n` elements. -/
theorem exists_card_fiber_lt_of_card_lt_mul (hn : s.card < t.card * n) :
    ∃ y ∈ t, (s.filter fun x => f x = y).card < n := by
  simp only [← card_eq_sum_ones]
  apply exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul fun _ _ => Nat.zero_leₓ _
  simpa

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function between
finite sets `s` and `t` and a number `b` such that `card t • b ≤ card s`, there exists `y ∈ t` such
that its preimage in `s` has at least `b` elements.
See also `finset.exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to` for a stronger statement. -/
theorem exists_le_card_fiber_of_nsmul_le_card_of_maps_to (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (ht : t.Nonempty)
    (hb : t.card • b ≤ s.card) : ∃ y ∈ t, b ≤ (s.filter fun x => f x = y).card := by
  simp_rw [cast_card] at hb⊢
  exact exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht hb

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function between
finite sets `s` and `t` and a natural number `b` such that `card t * n ≤ card s`, there exists `y ∈
t` such that its preimage in `s` has at least `n` elements. See also
`finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` for a stronger statement. -/
theorem exists_le_card_fiber_of_mul_le_card_of_maps_to (hf : ∀, ∀ a ∈ s, ∀, f a ∈ t) (ht : t.Nonempty)
    (hn : t.card * n ≤ s.card) : ∃ y ∈ t, n ≤ (s.filter fun x => f x = y).card := by
  simp only [← card_eq_sum_ones]
  apply exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht
  simpa

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function `f`, a
finite sets `s` and `t`, and a number `b` such that `card s ≤ card t • b`, there exists `y ∈ t` such
that its preimage in `s` has no more than `b` elements.
See also `finset.exists_card_fiber_lt_of_card_lt_nsmul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_nsmul (ht : t.Nonempty) (hb : ↑s.card ≤ t.card • b) :
    ∃ y ∈ t, ↑(s.filter fun x => f x = y).card ≤ b := by
  simp_rw [cast_card] at hb⊢
  refine' exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul (fun _ _ => sum_nonneg fun _ _ => zero_le_one) ht hb

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function `f`, a
finite sets `s` in its domain, a finite set `t` in its codomain, and a natural number `n` such that
`card s ≤ card t * n`, there exists `y ∈ t` such that its preimage in `s` has no more than `n`
elements. See also `finset.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_mul (ht : t.Nonempty) (hn : s.card ≤ t.card * n) :
    ∃ y ∈ t, (s.filter fun x => f x = y).card ≤ n := by
  simp only [← card_eq_sum_ones]
  apply exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul (fun _ _ => Nat.zero_leₓ _) ht
  simpa

end Finset

namespace Fintype

open Finset

variable [Fintype α] [Fintype β] (f : α → β) {w : α → M} {b : M} {n : ℕ}

section

variable [LinearOrderedCancelAddCommMonoid M]

/-!
### The pigeonhole principles on `fintypes`s, pigeons counted by weight

In this section we specialize theorems from the previous section to the special case of functions
between `fintype`s and `s = univ`, `t = univ`. In this case the assumption `∀ x ∈ s, f x ∈ t` always
holds, so we have four theorems instead of eight. -/


/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than `b` provided that
the total number of pigeonholes times `b` is less than the total weight of all pigeons. -/
theorem exists_lt_sum_fiber_of_nsmul_lt_sum (hb : card β • b < ∑ x, w x) :
    ∃ y, b < ∑ x in univ.filter fun x => f x = y, w x :=
  let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (fun _ _ => mem_univ _) hb
  ⟨y, hy⟩

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than or equal to `b`
provided that the total number of pigeonholes times `b` is less than or equal to the total weight of
all pigeons. -/
theorem exists_le_sum_fiber_of_nsmul_le_sum [Nonempty β] (hb : card β • b ≤ ∑ x, w x) :
    ∃ y, b ≤ ∑ x in univ.filter fun x => f x = y, w x :=
  let ⟨y, _, hy⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, hy⟩

/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than `b` provided that
the total number of pigeonholes times `b` is greater than the total weight of all pigeons. -/
theorem exists_sum_fiber_lt_of_sum_lt_nsmul (hb : (∑ x, w x) < card β • b) :
    ∃ y, (∑ x in univ.filter fun x => f x = y, w x) < b :=
  @exists_lt_sum_fiber_of_nsmul_lt_sum α β Mᵒᵈ _ _ _ _ _ _ _ hb

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than or equal to `b`
provided that the total number of pigeonholes times `b` is greater than or equal to the total weight
of all pigeons. -/
theorem exists_sum_fiber_le_of_sum_le_nsmul [Nonempty β] (hb : (∑ x, w x) ≤ card β • b) :
    ∃ y, (∑ x in univ.filter fun x => f x = y, w x) ≤ b :=
  @exists_le_sum_fiber_of_nsmul_le_sum α β Mᵒᵈ _ _ _ _ _ _ _ _ hb

end

variable [LinearOrderedCommRing M]

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes. There is a pigeonhole
with at least as many pigeons as the ceiling of the average number of pigeons across all
pigeonholes. -/
theorem exists_lt_card_fiber_of_nsmul_lt_card (hb : card β • b < card α) :
    ∃ y : β, b < (univ.filter fun x => f x = y).card :=
  let ⟨y, _, h⟩ := exists_lt_card_fiber_of_nsmul_lt_card_of_maps_to (fun _ _ => mem_univ _) hb
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card β * n < card α`, there exists an element `y : β` such that its preimage has more than `n`
elements. -/
theorem exists_lt_card_fiber_of_mul_lt_card (hn : card β * n < card α) :
    ∃ y : β, n < (univ.filter fun x => f x = y).card :=
  let ⟨y, _, h⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (fun _ _ => mem_univ _) hn
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes. There is a pigeonhole
with at most as many pigeons as the floor of the average number of pigeons across all pigeonholes.
-/
theorem exists_card_fiber_lt_of_card_lt_nsmul (hb : ↑(card α) < card β • b) :
    ∃ y : β, ↑(univ.filter fun x => f x = y).card < b :=
  let ⟨y, _, h⟩ := exists_card_fiber_lt_of_card_lt_nsmul hb
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at most as many pigeons as
the floor of the average number of pigeons across all pigeonholes.
("The minimum is at most the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card α < card β * n`, there exists an element `y : β` such that its preimage has less than `n`
elements. -/
theorem exists_card_fiber_lt_of_card_lt_mul (hn : card α < card β * n) :
    ∃ y : β, (univ.filter fun x => f x = y).card < n :=
  let ⟨y, _, h⟩ := exists_card_fiber_lt_of_card_lt_mul hn
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `b` such that `card β • b ≤ card α`, there exists an
element `y : β` such that its preimage has at least `b` elements.
See also `fintype.exists_lt_card_fiber_of_nsmul_lt_card` for a stronger statement. -/
theorem exists_le_card_fiber_of_nsmul_le_card [Nonempty β] (hb : card β • b ≤ card α) :
    ∃ y : β, b ≤ (univ.filter fun x => f x = y).card :=
  let ⟨y, _, h⟩ := exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hb
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card β * n ≤ card α`, there exists an
element `y : β` such that its preimage has at least `n` elements. See also
`fintype.exists_lt_card_fiber_of_mul_lt_card` for a stronger statement. -/
theorem exists_le_card_fiber_of_mul_le_card [Nonempty β] (hn : card β * n ≤ card α) :
    ∃ y : β, n ≤ (univ.filter fun x => f x = y).card :=
  let ⟨y, _, h⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (fun _ _ => mem_univ _) univ_nonempty hn
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `b` such that `card α ≤ card β • b`, there exists an
element `y : β` such that its preimage has at most `b` elements.
See also `fintype.exists_card_fiber_lt_of_card_lt_nsmul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_nsmul [Nonempty β] (hb : ↑(card α) ≤ card β • b) :
    ∃ y : β, ↑(univ.filter fun x => f x = y).card ≤ b :=
  let ⟨y, _, h⟩ := exists_card_fiber_le_of_card_le_nsmul univ_nonempty hb
  ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card α ≤ card β * n`, there exists an
element `y : β` such that its preimage has at most `n` elements. See also
`fintype.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
theorem exists_card_fiber_le_of_card_le_mul [Nonempty β] (hn : card α ≤ card β * n) :
    ∃ y : β, (univ.filter fun x => f x = y).card ≤ n :=
  let ⟨y, _, h⟩ := exists_card_fiber_le_of_card_le_mul univ_nonempty hn
  ⟨y, h⟩

end Fintype

namespace Nat

open Set

/-- If `s` is an infinite set of natural numbers and `k > 0`, then `s` contains two elements `m < n`
that are equal mod `k`. -/
theorem exists_lt_modeq_of_infinite {s : Set ℕ} (hs : s.Infinite) {k : ℕ} (hk : 0 < k) :
    ∃ m ∈ s, ∃ n ∈ s, m < n ∧ m ≡ n [MOD k] :=
  (hs.exists_lt_map_eq_of_maps_to fun n _ => show n % k ∈ Iio k from Nat.mod_ltₓ n hk) <| finite_lt_nat k

end Nat

