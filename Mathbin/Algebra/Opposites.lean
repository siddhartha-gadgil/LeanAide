/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Equiv.Basic
import Mathbin.Logic.Nontrivial

/-!
# Multiplicative opposite and algebraic operations on it

In this file we define `mul_opposite α = αᵐᵒᵖ` to be the multiplicative opposite of `α`. It inherits
all additive algebraic structures on `α` (in other files), and reverses the order of multipliers in
multiplicative structures, i.e., `op (x * y) = op y * op x`, where `mul_opposite.op` is the
canonical map from `α` to `αᵐᵒᵖ`.

We also define `add_opposite α = αᵃᵒᵖ` to be the additive opposite of `α`. It inherits all
multiplicative algebraic structures on `α` (in other files), and reverses the order of summands in
additive structures, i.e. `op (x + y) = op y + op x`, where `add_opposite.op` is the canonical map
from `α` to `αᵃᵒᵖ`.

## Notation

* `αᵐᵒᵖ = mul_opposite α`
* `αᵃᵒᵖ = add_opposite α`

## Tags

multiplicative opposite, additive opposite
-/


universe u v

open Function

/-- Multiplicative opposite of a type. This type inherits all additive structures on `α` and
reverses left and right in multiplication.-/
@[to_additive
      "Additive opposite of a type. This type inherits all multiplicative structures on\n`α` and reverses left and right in addition."]
def MulOpposite (α : Type u) : Type u :=
  α

-- mathport name: «expr ᵐᵒᵖ»
postfix:max "ᵐᵒᵖ" => MulOpposite

-- mathport name: «expr ᵃᵒᵖ»
postfix:max "ᵃᵒᵖ" => AddOpposite

variable {α : Type u}

namespace MulOpposite

/-- The element of `mul_opposite α` that represents `x : α`. -/
@[pp_nodot, to_additive "The element of `αᵃᵒᵖ` that represents `x : α`."]
def op : α → αᵐᵒᵖ :=
  id

/-- The element of `α` represented by `x : αᵐᵒᵖ`. -/
@[pp_nodot, to_additive "The element of `α` represented by `x : αᵃᵒᵖ`."]
def unop : αᵐᵒᵖ → α :=
  id

attribute [pp_nodot] AddOpposite.op AddOpposite.unop

@[simp, to_additive]
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

@[simp, to_additive]
theorem op_unop (x : αᵐᵒᵖ) : op (unop x) = x :=
  rfl

@[simp, to_additive]
theorem op_comp_unop : (op : α → αᵐᵒᵖ) ∘ unop = id :=
  rfl

@[simp, to_additive]
theorem unop_comp_op : (unop : αᵐᵒᵖ → α) ∘ op = id :=
  rfl

/-- A recursor for `mul_opposite`. Use as `induction x using mul_opposite.rec`. -/
@[simp, to_additive "A recursor for `add_opposite`. Use as `induction x using add_opposite.rec`."]
protected def rec {F : ∀ X : αᵐᵒᵖ, Sort v} (h : ∀ X, F (op X)) : ∀ X, F X := fun X => h (unop X)

/-- The canonical bijection between `α` and `αᵐᵒᵖ`. -/
@[to_additive "The canonical bijection between `α` and `αᵃᵒᵖ`.",
  simps (config := { fullyApplied := false }) apply symmApply]
def opEquiv : α ≃ αᵐᵒᵖ :=
  ⟨op, unop, unop_op, op_unop⟩

@[to_additive]
theorem op_bijective : Bijective (op : α → αᵐᵒᵖ) :=
  opEquiv.Bijective

@[to_additive]
theorem unop_bijective : Bijective (unop : αᵐᵒᵖ → α) :=
  opEquiv.symm.Bijective

@[to_additive]
theorem op_injective : Injective (op : α → αᵐᵒᵖ) :=
  op_bijective.Injective

@[to_additive]
theorem op_surjective : Surjective (op : α → αᵐᵒᵖ) :=
  op_bijective.Surjective

@[to_additive]
theorem unop_injective : Injective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Injective

@[to_additive]
theorem unop_surjective : Surjective (unop : αᵐᵒᵖ → α) :=
  unop_bijective.Surjective

@[simp, to_additive]
theorem op_inj {x y : α} : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp, to_additive]
theorem unop_inj {x y : αᵐᵒᵖ} : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

variable (α)

@[to_additive]
instance [Nontrivial α] : Nontrivial αᵐᵒᵖ :=
  op_injective.Nontrivial

@[to_additive]
instance [Inhabited α] : Inhabited αᵐᵒᵖ :=
  ⟨op default⟩

@[to_additive]
instance [Subsingleton α] : Subsingleton αᵐᵒᵖ :=
  unop_injective.Subsingleton

@[to_additive]
instance [Unique α] : Unique αᵐᵒᵖ :=
  Unique.mk' _

@[to_additive]
instance [IsEmpty α] : IsEmpty αᵐᵒᵖ :=
  Function.is_empty unop

instance [Zero α] : Zero αᵐᵒᵖ where zero := op 0

@[to_additive]
instance [One α] : One αᵐᵒᵖ where one := op 1

instance [Add α] : Add αᵐᵒᵖ where add := fun x y => op (unop x + unop y)

instance [Sub α] : Sub αᵐᵒᵖ where sub := fun x y => op (unop x - unop y)

instance [Neg α] : Neg αᵐᵒᵖ where neg := fun x => op <| -unop x

instance [HasInvolutiveNeg α] : HasInvolutiveNeg αᵐᵒᵖ :=
  { MulOpposite.hasNeg α with neg_neg := fun a => unop_injective <| neg_negₓ _ }

@[to_additive]
instance [Mul α] : Mul αᵐᵒᵖ where mul := fun x y => op (unop y * unop x)

@[to_additive]
instance [Inv α] : Inv αᵐᵒᵖ where inv := fun x => op <| (unop x)⁻¹

@[to_additive]
instance [HasInvolutiveInv α] : HasInvolutiveInv αᵐᵒᵖ :=
  { MulOpposite.hasInv α with inv_inv := fun a => unop_injective <| inv_invₓ _ }

@[to_additive]
instance (R : Type _) [HasSmul R α] : HasSmul R αᵐᵒᵖ where smul := fun c x => op (c • unop x)

section

variable (α)

@[simp]
theorem op_zero [Zero α] : op (0 : α) = 0 :=
  rfl

@[simp]
theorem unop_zero [Zero α] : unop (0 : αᵐᵒᵖ) = 0 :=
  rfl

@[simp, to_additive]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl

@[simp, to_additive]
theorem unop_one [One α] : unop (1 : αᵐᵒᵖ) = 1 :=
  rfl

variable {α}

@[simp]
theorem op_add [Add α] (x y : α) : op (x + y) = op x + op y :=
  rfl

@[simp]
theorem unop_add [Add α] (x y : αᵐᵒᵖ) : unop (x + y) = unop x + unop y :=
  rfl

@[simp]
theorem op_neg [Neg α] (x : α) : op (-x) = -op x :=
  rfl

@[simp]
theorem unop_neg [Neg α] (x : αᵐᵒᵖ) : unop (-x) = -unop x :=
  rfl

@[simp, to_additive]
theorem op_mul [Mul α] (x y : α) : op (x * y) = op y * op x :=
  rfl

@[simp, to_additive]
theorem unop_mul [Mul α] (x y : αᵐᵒᵖ) : unop (x * y) = unop y * unop x :=
  rfl

@[simp, to_additive]
theorem op_inv [Inv α] (x : α) : op x⁻¹ = (op x)⁻¹ :=
  rfl

@[simp, to_additive]
theorem unop_inv [Inv α] (x : αᵐᵒᵖ) : unop x⁻¹ = (unop x)⁻¹ :=
  rfl

@[simp]
theorem op_sub [Sub α] (x y : α) : op (x - y) = op x - op y :=
  rfl

@[simp]
theorem unop_sub [Sub α] (x y : αᵐᵒᵖ) : unop (x - y) = unop x - unop y :=
  rfl

@[simp, to_additive]
theorem op_smul {R : Type _} [HasSmul R α] (c : R) (a : α) : op (c • a) = c • op a :=
  rfl

@[simp, to_additive]
theorem unop_smul {R : Type _} [HasSmul R α] (c : R) (a : αᵐᵒᵖ) : unop (c • a) = c • unop a :=
  rfl

end

variable {α}

@[simp]
theorem unop_eq_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop = (0 : α) ↔ a = (0 : αᵐᵒᵖ) :=
  unop_injective.eq_iff' rfl

@[simp]
theorem op_eq_zero_iff [Zero α] (a : α) : op a = (0 : αᵐᵒᵖ) ↔ a = (0 : α) :=
  op_injective.eq_iff' rfl

theorem unop_ne_zero_iff [Zero α] (a : αᵐᵒᵖ) : a.unop ≠ (0 : α) ↔ a ≠ (0 : αᵐᵒᵖ) :=
  not_congr <| unop_eq_zero_iff a

theorem op_ne_zero_iff [Zero α] (a : α) : op a ≠ (0 : αᵐᵒᵖ) ↔ a ≠ (0 : α) :=
  not_congr <| op_eq_zero_iff a

@[simp, to_additive]
theorem unop_eq_one_iff [One α] (a : αᵐᵒᵖ) : a.unop = 1 ↔ a = 1 :=
  unop_injective.eq_iff' rfl

@[simp, to_additive]
theorem op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' rfl

end MulOpposite

namespace AddOpposite

instance [One α] : One αᵃᵒᵖ where one := op 1

@[simp]
theorem op_one [One α] : op (1 : α) = 1 :=
  rfl

@[simp]
theorem unop_one [One α] : unop 1 = (1 : α) :=
  rfl

@[simp]
theorem op_eq_one_iff [One α] {a : α} : op a = 1 ↔ a = 1 :=
  op_injective.eq_iff' op_one

@[simp]
theorem unop_eq_one_iff [One α] {a : αᵃᵒᵖ} : unop a = 1 ↔ a = 1 :=
  unop_injective.eq_iff' unop_one

instance [Mul α] : Mul αᵃᵒᵖ where mul := fun a b => op (unop a * unop b)

@[simp]
theorem op_mul [Mul α] (a b : α) : op (a * b) = op a * op b :=
  rfl

@[simp]
theorem unop_mul [Mul α] (a b : αᵃᵒᵖ) : unop (a * b) = unop a * unop b :=
  rfl

instance [Inv α] : Inv αᵃᵒᵖ where inv := fun a => op (unop a)⁻¹

instance [HasInvolutiveInv α] : HasInvolutiveInv αᵃᵒᵖ :=
  { AddOpposite.hasInv with inv_inv := fun a => unop_injective <| inv_invₓ _ }

@[simp]
theorem op_inv [Inv α] (a : α) : op a⁻¹ = (op a)⁻¹ :=
  rfl

@[simp]
theorem unop_inv [Inv α] (a : αᵃᵒᵖ) : unop a⁻¹ = (unop a)⁻¹ :=
  rfl

instance [Div α] : Div αᵃᵒᵖ where div := fun a b => op (unop a / unop b)

@[simp]
theorem op_div [Div α] (a b : α) : op (a / b) = op a / op b :=
  rfl

@[simp]
theorem unop_div [Div α] (a b : α) : unop (a / b) = unop a / unop b :=
  rfl

end AddOpposite

