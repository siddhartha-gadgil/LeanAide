/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Order.Bounds

/-!
# Intervals in Lattices

In this file, we provide instances of lattice structures on intervals within lattices.
Some of them depend on the order of the endpoints of the interval, and thus are not made
global instances. These are probably not all of the lattice instances that could be placed on these
intervals, but more can be added easily along the same lines when needed.

## Main definitions
In the following, `*` can represent either `c`, `o`, or `i`.
  * `set.Ic*.order_bot`
  * `set.Ii*.semillatice_inf`
  * `set.I*c.order_top`
  * `set.I*c.semillatice_inf`
  * `set.I**.lattice`
  * `set.Iic.bounded_order`, within an `order_bot`
  * `set.Ici.bounded_order`, within an `order_top`

-/


variable {α : Type _}

namespace Set

namespace Ico

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Ico a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, lt_of_le_of_ltₓ inf_le_left hx.2⟩

/-- `Ico a b` has a bottom element whenever `a < b`. -/
@[reducible]
protected def orderBot [PartialOrderₓ α] {a b : α} (h : a < b) : OrderBot (Ico a b) :=
  (is_least_Ico h).OrderBot

end Ico

namespace Iio

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iio a) :=
  Subtype.semilatticeInf fun x y hx hy => lt_of_le_of_ltₓ inf_le_left hx

end Iio

namespace Ioc

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Ioc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨lt_of_lt_of_leₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

/-- `Ioc a b` has a top element whenever `a < b`. -/
@[reducible]
protected def orderTop [PartialOrderₓ α] {a b : α} (h : a < b) : OrderTop (Ioc a b) :=
  (is_greatest_Ioc h).OrderTop

end Ioc

namespace Ioi

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ioi a) :=
  Subtype.semilatticeSup fun x y hx hy => lt_of_lt_of_leₓ hx le_sup_left

end Ioi

namespace Iic

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Iic a) :=
  Subtype.semilatticeInf fun x y hx hy => le_transₓ inf_le_left hx

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Iic a) :=
  Subtype.semilatticeSup fun x y hx hy => sup_le hx hy

instance [Lattice α] {a : α} : Lattice (Iic a) :=
  { Iic.semilatticeInf, Iic.semilatticeSup with }

instance [Preorderₓ α] {a : α} : OrderTop (Iic a) where
  top := ⟨a, le_reflₓ a⟩
  le_top := fun x => x.Prop

@[simp]
theorem coe_top [Preorderₓ α] {a : α} : ↑(⊤ : Iic a) = a :=
  rfl

instance [Preorderₓ α] [OrderBot α] {a : α} : OrderBot (Iic a) where
  bot := ⟨⊥, bot_le⟩
  bot_le := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 bot_le

@[simp]
theorem coe_bot [Preorderₓ α] [OrderBot α] {a : α} : ↑(⊥ : Iic a) = (⊥ : α) :=
  rfl

instance [Preorderₓ α] [OrderBot α] {a : α} : BoundedOrder (Iic a) :=
  { Iic.orderTop, Iic.orderBot with }

end Iic

namespace Ici

instance [SemilatticeInf α] {a : α} : SemilatticeInf (Ici a) :=
  Subtype.semilatticeInf fun x y hx hy => le_inf hx hy

instance [SemilatticeSup α] {a : α} : SemilatticeSup (Ici a) :=
  Subtype.semilatticeSup fun x y hx hy => le_transₓ hx le_sup_left

instance [Lattice α] {a : α} : Lattice (Ici a) :=
  { Ici.semilatticeInf, Ici.semilatticeSup with }

instance [Preorderₓ α] {a : α} : OrderBot (Ici a) where
  bot := ⟨a, le_reflₓ a⟩
  bot_le := fun x => x.Prop

@[simp]
theorem coe_bot [Preorderₓ α] {a : α} : ↑(⊥ : Ici a) = a :=
  rfl

instance [Preorderₓ α] [OrderTop α] {a : α} : OrderTop (Ici a) where
  top := ⟨⊤, le_top⟩
  le_top := fun ⟨_, _⟩ => Subtype.mk_le_mk.2 le_top

@[simp]
theorem coe_top [Preorderₓ α] [OrderTop α] {a : α} : ↑(⊤ : Ici a) = (⊤ : α) :=
  rfl

instance [Preorderₓ α] [OrderTop α] {a : α} : BoundedOrder (Ici a) :=
  { Ici.orderTop, Ici.orderBot with }

end Ici

namespace Icc

instance [SemilatticeInf α] {a b : α} : SemilatticeInf (Icc a b) :=
  Subtype.semilatticeInf fun x y hx hy => ⟨le_inf hx.1 hy.1, le_transₓ inf_le_left hx.2⟩

instance [SemilatticeSup α] {a b : α} : SemilatticeSup (Icc a b) :=
  Subtype.semilatticeSup fun x y hx hy => ⟨le_transₓ hx.1 le_sup_left, sup_le hx.2 hy.2⟩

instance [Lattice α] {a b : α} : Lattice (Icc a b) :=
  { Icc.semilatticeInf, Icc.semilatticeSup with }

/-- `Icc a b` has a bottom element whenever `a ≤ b`. -/
@[reducible]
protected def orderBot [Preorderₓ α] {a b : α} (h : a ≤ b) : OrderBot (Icc a b) :=
  (is_least_Icc h).OrderBot

/-- `Icc a b` has a top element whenever `a ≤ b`. -/
@[reducible]
protected def orderTop [Preorderₓ α] {a b : α} (h : a ≤ b) : OrderTop (Icc a b) :=
  (is_greatest_Icc h).OrderTop

/-- `Icc a b` is a `bounded_order` whenever `a ≤ b`. -/
@[reducible]
protected def boundedOrder [Preorderₓ α] {a b : α} (h : a ≤ b) : BoundedOrder (Icc a b) :=
  { Icc.orderTop h, Icc.orderBot h with }

end Icc

end Set

