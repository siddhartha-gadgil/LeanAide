/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import Mathbin.Data.Set.Finite

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/


variable {α : Type _} [Preorderₓ α]

/-- A nonempty preorder with no maximal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strict_mono α
  Infinite.of_injective f hf.Injective

/-- A nonempty preorder with no minimal element is infinite. This is not an instance to avoid
a cycle with `infinite α → nontrivial α → nonempty α`. -/
theorem NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)

theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _

theorem Ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h

theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self

theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h

theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self

theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h

theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self

theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h

end DenselyOrdered

instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite

theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 Iio.infinite

instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite

theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 Iic.infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite

theorem Ioi_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 Iio.infinite

instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite

theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 Ici.infinite

end Set

