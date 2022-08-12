/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Algebra.Group.Commute
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Algebra.Opposites
import Mathbin.Data.Int.Cast.Defs

/-!
# Group structures on the multiplicative and additive opposites
-/


universe u v

variable (α : Type u)

namespace MulOpposite

/-!
### Additive structures on `αᵐᵒᵖ`
-/


instance [AddSemigroupₓ α] : AddSemigroupₓ αᵐᵒᵖ :=
  unop_injective.AddSemigroup _ fun x y => rfl

instance [AddLeftCancelSemigroup α] : AddLeftCancelSemigroup αᵐᵒᵖ :=
  unop_injective.AddLeftCancelSemigroup _ fun x y => rfl

instance [AddRightCancelSemigroup α] : AddRightCancelSemigroup αᵐᵒᵖ :=
  unop_injective.AddRightCancelSemigroup _ fun x y => rfl

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ αᵐᵒᵖ :=
  unop_injective.AddCommSemigroup _ fun x y => rfl

instance [AddZeroClassₓ α] : AddZeroClassₓ αᵐᵒᵖ :=
  unop_injective.AddZeroClass _ rfl fun x y => rfl

instance [AddMonoidₓ α] : AddMonoidₓ αᵐᵒᵖ :=
  unop_injective.AddMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [AddMonoidWithOneₓ α] : AddMonoidWithOneₓ αᵐᵒᵖ :=
  { MulOpposite.addMonoid α, MulOpposite.hasOne α with natCast := fun n => op n,
    nat_cast_zero :=
      show op ((0 : ℕ) : α) = 0 by
        simp ,
    nat_cast_succ :=
      show ∀ n, op ((n + 1 : ℕ) : α) = op (n : ℕ) + 1 by
        simp }

instance [AddCommMonoidₓ α] : AddCommMonoidₓ αᵐᵒᵖ :=
  unop_injective.AddCommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [SubNegMonoidₓ α] : SubNegMonoidₓ αᵐᵒᵖ :=
  unop_injective.SubNegMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroupₓ α] : AddGroupₓ αᵐᵒᵖ :=
  unop_injective.AddGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [AddGroupWithOneₓ α] : AddGroupWithOneₓ αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.addGroup α with intCast := fun n => op n,
    int_cast_of_nat := fun n =>
      show op ((n : ℤ) : α) = op n by
        rw [Int.cast_coe_nat],
    int_cast_neg_succ_of_nat := fun n =>
      show op _ = op (-unop (op ((n + 1 : ℕ) : α))) by
        erw [unop_op, Int.cast_neg_succ_of_nat] <;> rfl }

instance [AddCommGroupₓ α] : AddCommGroupₓ αᵐᵒᵖ :=
  unop_injective.AddCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-!
### Multiplicative structures on `αᵐᵒᵖ`

We also generate additive structures on `αᵃᵒᵖ` using `to_additive`
-/


@[to_additive]
instance [Semigroupₓ α] : Semigroupₓ αᵐᵒᵖ :=
  { MulOpposite.hasMul α with
    mul_assoc := fun x y z => unop_injective <| Eq.symm <| mul_assoc (unop z) (unop y) (unop x) }

@[to_additive]
instance [RightCancelSemigroup α] : LeftCancelSemigroup αᵐᵒᵖ :=
  { MulOpposite.semigroup α with
    mul_left_cancel := fun x y z H => unop_injective <| mul_right_cancelₓ <| op_injective H }

@[to_additive]
instance [LeftCancelSemigroup α] : RightCancelSemigroup αᵐᵒᵖ :=
  { MulOpposite.semigroup α with
    mul_right_cancel := fun x y z H => unop_injective <| mul_left_cancelₓ <| op_injective H }

@[to_additive]
instance [CommSemigroupₓ α] : CommSemigroupₓ αᵐᵒᵖ :=
  { MulOpposite.semigroup α with mul_comm := fun x y => unop_injective <| mul_comm (unop y) (unop x) }

@[to_additive]
instance [MulOneClassₓ α] : MulOneClassₓ αᵐᵒᵖ :=
  { MulOpposite.hasMul α, MulOpposite.hasOne α with one_mul := fun x => unop_injective <| mul_oneₓ <| unop x,
    mul_one := fun x => unop_injective <| one_mulₓ <| unop x }

@[to_additive]
instance [Monoidₓ α] : Monoidₓ αᵐᵒᵖ :=
  { MulOpposite.semigroup α, MulOpposite.mulOneClass α with npow := fun n x => op <| x.unop ^ n,
    npow_zero' := fun x => unop_injective <| Monoidₓ.npow_zero' x.unop,
    npow_succ' := fun n x => unop_injective <| pow_succ'ₓ x.unop n }

@[to_additive]
instance [RightCancelMonoid α] : LeftCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.leftCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance [LeftCancelMonoid α] : RightCancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelSemigroup α, MulOpposite.monoid α with }

@[to_additive]
instance [CancelMonoid α] : CancelMonoid αᵐᵒᵖ :=
  { MulOpposite.rightCancelMonoid α, MulOpposite.leftCancelMonoid α with }

@[to_additive]
instance [CommMonoidₓ α] : CommMonoidₓ αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance [CancelCommMonoid α] : CancelCommMonoid αᵐᵒᵖ :=
  { MulOpposite.cancelMonoid α, MulOpposite.commMonoid α with }

@[to_additive AddOpposite.subNegMonoid]
instance [DivInvMonoidₓ α] : DivInvMonoidₓ αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.hasInv α with zpow := fun n x => op <| x.unop ^ n,
    zpow_zero' := fun x => unop_injective <| DivInvMonoidₓ.zpow_zero' x.unop,
    zpow_succ' := fun n x =>
      unop_injective <| by
        rw [unop_op, zpow_of_nat, zpow_of_nat, pow_succ'ₓ, unop_mul, unop_op],
    zpow_neg' := fun z x => unop_injective <| DivInvMonoidₓ.zpow_neg' z x.unop }

@[to_additive AddOpposite.subtractionMonoid]
instance [DivisionMonoid α] : DivisionMonoid αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α, MulOpposite.hasInvolutiveInv α with
    mul_inv_rev := fun a b => unop_injective <| mul_inv_rev _ _,
    inv_eq_of_mul := fun a b h => unop_injective <| inv_eq_of_mul_eq_one_left <| congr_arg unop h }

@[to_additive AddOpposite.subtractionCommMonoid]
instance [DivisionCommMonoid α] : DivisionCommMonoid αᵐᵒᵖ :=
  { MulOpposite.divisionMonoid α, MulOpposite.commSemigroup α with }

@[to_additive]
instance [Groupₓ α] : Groupₓ αᵐᵒᵖ :=
  { MulOpposite.divInvMonoid α with mul_left_inv := fun x => unop_injective <| mul_inv_selfₓ <| unop x }

@[to_additive]
instance [CommGroupₓ α] : CommGroupₓ αᵐᵒᵖ :=
  { MulOpposite.group α, MulOpposite.commMonoid α with }

variable {α}

@[simp, to_additive]
theorem unop_div [DivInvMonoidₓ α] (x y : αᵐᵒᵖ) : unop (x / y) = (unop y)⁻¹ * unop x :=
  rfl

@[simp, to_additive]
theorem op_div [DivInvMonoidₓ α] (x y : α) : op (x / y) = (op y)⁻¹ * op x := by
  simp [← div_eq_mul_inv]

@[simp, to_additive]
theorem semiconj_by_op [Mul α] {a x y : α} : SemiconjBy (op a) (op y) (op x) ↔ SemiconjBy a x y := by
  simp only [← SemiconjBy, op_mul, ← op_inj, ← eq_comm]

@[simp, to_additive]
theorem semiconj_by_unop [Mul α] {a x y : αᵐᵒᵖ} : SemiconjBy (unop a) (unop y) (unop x) ↔ SemiconjBy a x y := by
  conv_rhs => rw [← op_unop a, ← op_unop x, ← op_unop y, semiconj_by_op]

@[to_additive]
theorem _root_.semiconj_by.op [Mul α] {a x y : α} (h : SemiconjBy a x y) : SemiconjBy (op a) (op y) (op x) :=
  semiconj_by_op.2 h

@[to_additive]
theorem _root_.semiconj_by.unop [Mul α] {a x y : αᵐᵒᵖ} (h : SemiconjBy a x y) : SemiconjBy (unop a) (unop y) (unop x) :=
  semiconj_by_unop.2 h

@[to_additive]
theorem _root_.commute.op [Mul α] {x y : α} (h : Commute x y) : Commute (op x) (op y) :=
  h.op

@[to_additive]
theorem Commute.unop [Mul α] {x y : αᵐᵒᵖ} (h : Commute x y) : Commute (unop x) (unop y) :=
  h.unop

@[simp, to_additive]
theorem commute_op [Mul α] {x y : α} : Commute (op x) (op y) ↔ Commute x y :=
  semiconj_by_op

@[simp, to_additive]
theorem commute_unop [Mul α] {x y : αᵐᵒᵖ} : Commute (unop x) (unop y) ↔ Commute x y :=
  semiconj_by_unop

/-- The function `mul_opposite.op` is an additive equivalence. -/
@[simps (config := { fullyApplied := false, simpRhs := true })]
def opAddEquiv [Add α] : α ≃+ αᵐᵒᵖ :=
  { opEquiv with map_add' := fun a b => rfl }

@[simp]
theorem op_add_equiv_to_equiv [Add α] : (opAddEquiv : α ≃+ αᵐᵒᵖ).toEquiv = op_equiv :=
  rfl

end MulOpposite

/-!
### Multiplicative structures on `αᵃᵒᵖ`
-/


namespace AddOpposite

instance [Semigroupₓ α] : Semigroupₓ αᵃᵒᵖ :=
  unop_injective.Semigroup _ fun x y => rfl

instance [LeftCancelSemigroup α] : LeftCancelSemigroup αᵃᵒᵖ :=
  unop_injective.LeftCancelSemigroup _ fun x y => rfl

instance [RightCancelSemigroup α] : RightCancelSemigroup αᵃᵒᵖ :=
  unop_injective.RightCancelSemigroup _ fun x y => rfl

instance [CommSemigroupₓ α] : CommSemigroupₓ αᵃᵒᵖ :=
  unop_injective.CommSemigroup _ fun x y => rfl

instance [MulOneClassₓ α] : MulOneClassₓ αᵃᵒᵖ :=
  unop_injective.MulOneClass _ rfl fun x y => rfl

instance {β} [Pow α β] : Pow αᵃᵒᵖ β where pow := fun a b => op (unop a ^ b)

@[simp]
theorem op_pow {β} [Pow α β] (a : α) (b : β) : op (a ^ b) = op a ^ b :=
  rfl

@[simp]
theorem unop_pow {β} [Pow α β] (a : αᵃᵒᵖ) (b : β) : unop (a ^ b) = unop a ^ b :=
  rfl

instance [Monoidₓ α] : Monoidₓ αᵃᵒᵖ :=
  unop_injective.Monoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [CommMonoidₓ α] : CommMonoidₓ αᵃᵒᵖ :=
  unop_injective.CommMonoid _ rfl (fun _ _ => rfl) fun _ _ => rfl

instance [DivInvMonoidₓ α] : DivInvMonoidₓ αᵃᵒᵖ :=
  unop_injective.DivInvMonoid _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [Groupₓ α] : Groupₓ αᵃᵒᵖ :=
  unop_injective.Group _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance [CommGroupₓ α] : CommGroupₓ αᵃᵒᵖ :=
  unop_injective.CommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

variable {α}

/-- The function `add_opposite.op` is a multiplicative equivalence. -/
@[simps (config := { fullyApplied := false, simpRhs := true })]
def opMulEquiv [Mul α] : α ≃* αᵃᵒᵖ :=
  { opEquiv with map_mul' := fun a b => rfl }

@[simp]
theorem op_mul_equiv_to_equiv [Mul α] : (opMulEquiv : α ≃* αᵃᵒᵖ).toEquiv = op_equiv :=
  rfl

end AddOpposite

open MulOpposite

/-- Inversion on a group is a `mul_equiv` to the opposite group. When `G` is commutative, there is
`mul_equiv.inv`. -/
@[to_additive
      "Negation on an additive group is an `add_equiv` to the opposite group. When `G`\nis commutative, there is `add_equiv.inv`.",
  simps (config := { fullyApplied := false, simpRhs := true })]
def MulEquiv.inv' (G : Type _) [DivisionMonoid G] : G ≃* Gᵐᵒᵖ :=
  { (Equivₓ.inv G).trans opEquiv with map_mul' := fun x y => unop_injective <| mul_inv_rev x y }

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive
      "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively\ncommutes with `f y` for all `x, y` defines an additive semigroup homomorphism to `Sᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MulHom.toOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N) (hf : ∀ x y, Commute (f x) (f y)) : M →ₙ* Nᵐᵒᵖ where
  toFun := MulOpposite.op ∘ f
  map_mul' := fun x y => by
    simp [← (hf x y).Eq]

/-- A semigroup homomorphism `f : M →ₙ* N` such that `f x` commutes with `f y` for all `x, y`
defines a semigroup homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive
      "An additive semigroup homomorphism `f : add_hom M N` such that `f x` additively\ncommutes with `f y` for all `x`, `y` defines an additive semigroup homomorphism from `Mᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MulHom.fromOpposite {M N : Type _} [Mul M] [Mul N] (f : M →ₙ* N) (hf : ∀ x y, Commute (f x) (f y)) :
    Mᵐᵒᵖ →ₙ* N where
  toFun := f ∘ MulOpposite.unop
  map_mul' := fun x y => (f.map_mul _ _).trans (hf _ _).Eq

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism to `Nᵐᵒᵖ`. -/
@[to_additive
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes\nwith `f y` for all `x, y` defines an additive monoid homomorphism to `Sᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MonoidHom.toOpposite {M N : Type _} [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : M →* Nᵐᵒᵖ where
  toFun := MulOpposite.op ∘ f
  map_one' := congr_arg op f.map_one
  map_mul' := fun x y => by
    simp [← (hf x y).Eq]

/-- A monoid homomorphism `f : M →* N` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Mᵐᵒᵖ`. -/
@[to_additive
      "An additive monoid homomorphism `f : M →+ N` such that `f x` additively commutes\nwith `f y` for all `x`, `y` defines an additive monoid homomorphism from `Mᵃᵒᵖ`.",
  simps (config := { fullyApplied := false })]
def MonoidHom.fromOpposite {M N : Type _} [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N)
    (hf : ∀ x y, Commute (f x) (f y)) : Mᵐᵒᵖ →* N where
  toFun := f ∘ MulOpposite.unop
  map_one' := f.map_one
  map_mul' := fun x y => (f.map_mul _ _).trans (hf _ _).Eq

/-- The units of the opposites are equivalent to the opposites of the units. -/
@[to_additive
      "The additive units of the additive opposites are equivalent to the additive opposites\nof the additive units."]
def Units.opEquiv {M} [Monoidₓ M] : Mᵐᵒᵖˣ ≃* Mˣᵐᵒᵖ where
  toFun := fun u => op ⟨unop u, unop ↑u⁻¹, op_injective u.4, op_injective u.3⟩
  invFun := MulOpposite.rec fun u => ⟨op ↑u, op ↑u⁻¹, unop_injective <| u.4, unop_injective u.3⟩
  map_mul' := fun x y => unop_injective <| Units.ext <| rfl
  left_inv := fun x =>
    Units.ext <| by
      simp
  right_inv := fun x => unop_injective <| Units.ext <| rfl

@[simp, to_additive]
theorem Units.coe_unop_op_equiv {M} [Monoidₓ M] (u : Mᵐᵒᵖˣ) : ((Units.opEquiv u).unop : M) = unop (u : Mᵐᵒᵖ) :=
  rfl

@[simp, to_additive]
theorem Units.coe_op_equiv_symm {M} [Monoidₓ M] (u : Mˣᵐᵒᵖ) : (Units.opEquiv.symm u : Mᵐᵒᵖ) = op (u.unop : M) :=
  rfl

/-- A semigroup homomorphism `M →ₙ* N` can equivalently be viewed as a semigroup homomorphism
`Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive
      "An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an\nadditive semigroup homomorphism `add_hom Mᵃᵒᵖ Nᵃᵒᵖ`. This is the action of the (fully faithful)\n`ᵃᵒᵖ`-functor on morphisms.",
  simps]
def MulHom.op {M N} [Mul M] [Mul N] : (M →ₙ* N) ≃ (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) where
  toFun := fun f => { toFun := op ∘ f ∘ unop, map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun := fun f => { toFun := unop ∘ f ∘ op, map_mul' := fun x y => congr_arg unop (f.map_mul (op y) (op x)) }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext x
    simp

/-- The 'unopposite' of a semigroup homomorphism `Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ`. Inverse to `mul_hom.op`. -/
@[simp, to_additive "The 'unopposite' of an additive semigroup homomorphism `Mᵃᵒᵖ →ₙ+ Nᵃᵒᵖ`. Inverse\nto `add_hom.op`."]
def MulHom.unop {M N} [Mul M] [Mul N] : (Mᵐᵒᵖ →ₙ* Nᵐᵒᵖ) ≃ (M →ₙ* N) :=
  MulHom.op.symm

/-- An additive semigroup homomorphism `add_hom M N` can equivalently be viewed as an additive
homomorphism `add_hom Mᵐᵒᵖ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on
morphisms. -/
@[simps]
def AddHom.mulOp {M N} [Add M] [Add N] : AddHom M N ≃ AddHom Mᵐᵒᵖ Nᵐᵒᵖ where
  toFun := fun f => { toFun := op ∘ f ∘ unop, map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun := fun f => { toFun := unop ∘ f ∘ op, map_add' := fun x y => congr_arg unop (f.map_add (op x) (op y)) }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    simp

/-- The 'unopposite' of an additive semigroup hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_hom.mul_op`. -/
@[simp]
def AddHom.mulUnop {α β} [Add α] [Add β] : AddHom αᵐᵒᵖ βᵐᵒᵖ ≃ AddHom α β :=
  AddHom.mulOp.symm

/-- A monoid homomorphism `M →* N` can equivalently be viewed as a monoid homomorphism
`Mᵐᵒᵖ →* Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[to_additive
      "An additive monoid homomorphism `M →+ N` can equivalently be viewed as an\nadditive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. This is the action of the (fully faithful)\n`ᵃᵒᵖ`-functor on morphisms.",
  simps]
def MonoidHom.op {M N} [MulOneClassₓ M] [MulOneClassₓ N] : (M →* N) ≃ (Mᵐᵒᵖ →* Nᵐᵒᵖ) where
  toFun := fun f =>
    { toFun := op ∘ f ∘ unop, map_one' := congr_arg op f.map_one,
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun := fun f =>
    { toFun := unop ∘ f ∘ op, map_one' := congr_arg unop f.map_one,
      map_mul' := fun x y => congr_arg unop (f.map_mul (op y) (op x)) }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext x
    simp

/-- The 'unopposite' of a monoid homomorphism `Mᵐᵒᵖ →* Nᵐᵒᵖ`. Inverse to `monoid_hom.op`. -/
@[simp,
  to_additive "The 'unopposite' of an additive monoid homomorphism `Mᵃᵒᵖ →+ Nᵃᵒᵖ`. Inverse to\n`add_monoid_hom.op`."]
def MonoidHom.unop {M N} [MulOneClassₓ M] [MulOneClassₓ N] : (Mᵐᵒᵖ →* Nᵐᵒᵖ) ≃ (M →* N) :=
  MonoidHom.op.symm

/-- An additive homomorphism `M →+ N` can equivalently be viewed as an additive homomorphism
`Mᵐᵒᵖ →+ Nᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def AddMonoidHom.mulOp {M N} [AddZeroClassₓ M] [AddZeroClassₓ N] : (M →+ N) ≃ (Mᵐᵒᵖ →+ Nᵐᵒᵖ) where
  toFun := fun f =>
    { toFun := op ∘ f ∘ unop, map_zero' := unop_injective f.map_zero,
      map_add' := fun x y => unop_injective (f.map_add x.unop y.unop) }
  invFun := fun f =>
    { toFun := unop ∘ f ∘ op, map_zero' := congr_arg unop f.map_zero,
      map_add' := fun x y => congr_arg unop (f.map_add (op x) (op y)) }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    simp

/-- The 'unopposite' of an additive monoid hom `αᵐᵒᵖ →+ βᵐᵒᵖ`. Inverse to
`add_monoid_hom.mul_op`. -/
@[simp]
def AddMonoidHom.mulUnop {α β} [AddZeroClassₓ α] [AddZeroClassₓ β] : (αᵐᵒᵖ →+ βᵐᵒᵖ) ≃ (α →+ β) :=
  AddMonoidHom.mulOp.symm

/-- A iso `α ≃+ β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. -/
@[simps]
def AddEquiv.mulOp {α β} [Add α] [Add β] : α ≃+ β ≃ (αᵐᵒᵖ ≃+ βᵐᵒᵖ) where
  toFun := fun f => opAddEquiv.symm.trans (f.trans opAddEquiv)
  invFun := fun f => opAddEquiv.trans (f.trans opAddEquiv.symm)
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    simp

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃+ βᵐᵒᵖ`. Inverse to `add_equiv.mul_op`. -/
@[simp]
def AddEquiv.mulUnop {α β} [Add α] [Add β] : αᵐᵒᵖ ≃+ βᵐᵒᵖ ≃ (α ≃+ β) :=
  AddEquiv.mulOp.symm

/-- A iso `α ≃* β` can equivalently be viewed as an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. -/
@[to_additive "A iso `α ≃+ β` can equivalently be viewed as an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`.", simps]
def MulEquiv.op {α β} [Mul α] [Mul β] : α ≃* β ≃ (αᵐᵒᵖ ≃* βᵐᵒᵖ) where
  toFun := fun f =>
    { toFun := op ∘ f ∘ unop, invFun := op ∘ f.symm ∘ unop,
      left_inv := fun x => unop_injective (f.symm_apply_apply x.unop),
      right_inv := fun x => unop_injective (f.apply_symm_apply x.unop),
      map_mul' := fun x y => unop_injective (f.map_mul y.unop x.unop) }
  invFun := fun f =>
    { toFun := unop ∘ f ∘ op, invFun := unop ∘ f.symm ∘ op,
      left_inv := fun x => by
        simp ,
      right_inv := fun x => by
        simp ,
      map_mul' := fun x y => congr_arg unop (f.map_mul (op y) (op x)) }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    simp

/-- The 'unopposite' of an iso `αᵐᵒᵖ ≃* βᵐᵒᵖ`. Inverse to `mul_equiv.op`. -/
@[simp, to_additive "The 'unopposite' of an iso `αᵃᵒᵖ ≃+ βᵃᵒᵖ`. Inverse to `add_equiv.op`."]
def MulEquiv.unop {α β} [Mul α] [Mul β] : αᵐᵒᵖ ≃* βᵐᵒᵖ ≃ (α ≃* β) :=
  MulEquiv.op.symm

section Ext

/-- This ext lemma change equalities on `αᵐᵒᵖ →+ β` to equalities on `α →+ β`.
This is useful because there are often ext lemmas for specific `α`s that will apply
to an equality of `α →+ β` such as `finsupp.add_hom_ext'`. -/
@[ext]
theorem AddMonoidHom.mul_op_ext {α β} [AddZeroClassₓ α] [AddZeroClassₓ β] (f g : αᵐᵒᵖ →+ β)
    (h : f.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom = g.comp (opAddEquiv : α ≃+ αᵐᵒᵖ).toAddMonoidHom) : f = g :=
  AddMonoidHom.ext <| MulOpposite.rec fun x => (AddMonoidHom.congr_fun h : _) x

end Ext

