/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen, Yaël Dillies
-/
import Mathbin.Algebra.PunitInstances
import Mathbin.Order.Hom.Lattice
import Mathbin.Tactic.Abel
import Mathbin.Tactic.Ring

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: Turn a Boolean ring into a Boolean algebra.
* `boolean_algebra.to_boolean_ring`: Turn a Boolean algebra into a Boolean ring.
* `as_boolalg`: Type-synonym for the Boolean algebra associated to a Boolean ring.
* `as_boolring`: Type-synonym for the Boolean ring associated to a Boolean algebra.

## Implementation notes

We provide two ways of turning a Boolean algebra/ring into a Boolean ring/algebra:
* Instances on the same type accessible in locales `boolean_algebra_of_boolean_ring` and
  `boolean_ring_of_boolean_algebra`.
* Type-synonyms `as_boolalg` and `as_boolring`.

At this point in time, it is not clear the first way is useful, but we keep it for educational
purposes and because it is easier than dealing with
`of_boolalg`/`to_boolalg`/`of_boolring`/`to_boolring` explicitly.

## Tags

boolean ring, boolean algebra
-/


variable {α β γ : Type _}

/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ringₓ α where
  mul_self : ∀ a : α, a * a = a

section BooleanRing

variable [BooleanRing α] (a b : α)

instance : IsIdempotent α (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[simp]
theorem mul_self : a * a = a :=
  BooleanRing.mul_self _

@[simp]
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by
        rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by
        rw [add_mulₓ, mul_addₓ]
      _ = a + a + (a + a) := by
        rw [mul_self]
      
  rwa [self_eq_add_left] at this

@[simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by
      rw [add_zeroₓ]
    _ = -a + -a + a := by
      rw [← neg_add_selfₓ, add_assocₓ]
    _ = a := by
      rw [add_self, zero_addₓ]
    

theorem add_eq_zero : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by
      rw [neg_eq]
    

@[simp]
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by
        rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by
        rw [add_mulₓ, mul_addₓ, mul_addₓ]
      _ = a + a * b + (b * a + b) := by
        simp only [← mul_self]
      _ = a + b + (a * b + b * a) := by
        abel
      
  rwa [self_eq_add_rightₓ] at this

@[simp]
theorem sub_eq_add : a - b = a + b := by
  rw [sub_eq_add_neg, add_right_injₓ, neg_eq]

@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by
  rw [mul_addₓ, mul_oneₓ, mul_self, add_self]

-- Note [lower instance priority]
instance (priority := 100) BooleanRing.toCommRing : CommRingₓ α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by
      rw [← add_eq_zero, mul_add_mul] }

end BooleanRing

instance : BooleanRing PUnit :=
  ⟨fun _ => Subsingleton.elimₓ _ _⟩

/-! ### Turning a Boolean ring into a Boolean algebra -/


section RingToAlgebra

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolalg (α : Type _) :=
  α

/-- The "identity" equivalence between `as_boolalg α` and `α`. -/
def toBoolalg : α ≃ AsBoolalg α :=
  Equivₓ.refl _

/-- The "identity" equivalence between `α` and `as_boolalg α`. -/
def ofBoolalg : AsBoolalg α ≃ α :=
  Equivₓ.refl _

@[simp]
theorem to_boolalg_symm_eq : (@toBoolalg α).symm = ofBoolalg :=
  rfl

@[simp]
theorem of_boolalg_symm_eq : (@ofBoolalg α).symm = toBoolalg :=
  rfl

@[simp]
theorem to_boolalg_of_boolalg (a : AsBoolalg α) : toBoolalg (ofBoolalg a) = a :=
  rfl

@[simp]
theorem of_boolalg_to_boolalg (a : α) : ofBoolalg (toBoolalg a) = a :=
  rfl

@[simp]
theorem to_boolalg_inj {a b : α} : toBoolalg a = toBoolalg b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_boolalg_inj {a b : AsBoolalg α} : ofBoolalg a = ofBoolalg b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolalg α) :=
  ‹Inhabited α›

variable [BooleanRing α] [BooleanRing β] [BooleanRing γ]

namespace BooleanRing

/-- The join operation in a Boolean ring is `x + y + x * y`. -/
def hasSup : HasSup α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
def hasInf : HasInf α :=
  ⟨(· * ·)⟩

localized [-- Note [lower instance priority]
BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasSup

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasInf

theorem sup_comm (a b : α) : a⊔b = b⊔a := by
  dsimp' only [← (·⊔·)]
  ring

theorem inf_comm (a b : α) : a⊓b = b⊓a := by
  dsimp' only [← (·⊓·)]
  ring

theorem sup_assoc (a b c : α) : a⊔b⊔c = a⊔(b⊔c) := by
  dsimp' only [← (·⊔·)]
  ring

theorem inf_assoc (a b c : α) : a⊓b⊓c = a⊓(b⊓c) := by
  dsimp' only [← (·⊓·)]
  ring

theorem sup_inf_self (a b : α) : a⊔a⊓b = a := by
  dsimp' only [← (·⊔·), ← (·⊓·)]
  assoc_rw [mul_self, add_self, add_zeroₓ]

theorem inf_sup_self (a b : α) : a⊓(a⊔b) = a := by
  dsimp' only [← (·⊔·), ← (·⊓·)]
  rw [mul_addₓ, mul_addₓ, mul_self, ← mul_assoc, mul_self, add_assocₓ, add_self, add_zeroₓ]

theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) + (a * b * c + a * a * b * c) :=
      by
      ring
    _ = a + b * c + a * (b * c) := by
      simp only [← mul_self, ← add_self, ← add_zeroₓ]
    

theorem le_sup_inf (a b c : α) : (a⊔b)⊓(a⊔c)⊔(a⊔b⊓c) = a⊔b⊓c := by
  dsimp' only [← (·⊔·), ← (·⊓·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_addₓ]

/-- The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
def toBooleanAlgebra : BooleanAlgebra α :=
  BooleanAlgebra.ofCore
    { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self with le_sup_inf := le_sup_inf,
      top := 1,
      le_top := fun a =>
        show a + 1 + a * 1 = 1 by
          assoc_rw [mul_oneₓ, add_commₓ, add_self, add_zeroₓ],
      bot := 0,
      bot_le := fun a =>
        show 0 + a + 0 * a = a by
          rw [zero_mul, zero_addₓ, add_zeroₓ],
      compl := fun a => 1 + a,
      inf_compl_le_bot := fun a =>
        show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by
          norm_num [← mul_addₓ, ← mul_self, ← add_self],
      top_le_sup_compl := fun a => by
        change 1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) = a + (1 + a) + a * (1 + a)
        norm_num [← mul_addₓ, ← mul_self]
        rw [← add_assocₓ, add_self] }

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.toBooleanAlgebra

end BooleanRing

instance : BooleanAlgebra (AsBoolalg α) :=
  @BooleanRing.toBooleanAlgebra α _

@[simp]
theorem of_boolalg_top : ofBoolalg (⊤ : AsBoolalg α) = 1 :=
  rfl

@[simp]
theorem of_boolalg_bot : ofBoolalg (⊥ : AsBoolalg α) = 0 :=
  rfl

@[simp]
theorem of_boolalg_sup (a b : AsBoolalg α) : ofBoolalg (a⊔b) = ofBoolalg a + ofBoolalg b + ofBoolalg a * ofBoolalg b :=
  rfl

@[simp]
theorem of_boolalg_inf (a b : AsBoolalg α) : ofBoolalg (a⊓b) = ofBoolalg a * ofBoolalg b :=
  rfl

@[simp]
theorem of_boolalg_compl (a : AsBoolalg α) : ofBoolalg (aᶜ) = 1 + ofBoolalg a :=
  rfl

@[simp]
theorem of_boolalg_sdiff (a b : AsBoolalg α) : ofBoolalg (a \ b) = ofBoolalg a * (1 + ofBoolalg b) :=
  rfl

private theorem of_boolalg_symm_diff_aux (a b : α) : (a + b + a * b) * (1 + a * b) = a + b :=
  calc
    (a + b + a * b) * (1 + a * b) = a + b + (a * b + a * b * (a * b)) + (a * (b * b) + a * a * b) := by
      ring
    _ = a + b := by
      simp only [← mul_self, ← add_self, ← add_zeroₓ]
    

@[simp]
theorem of_boolalg_symm_diff (a b : AsBoolalg α) : ofBoolalg (a ∆ b) = ofBoolalg a + ofBoolalg b := by
  rw [symm_diff_eq_sup_sdiff_inf]
  exact of_boolalg_symm_diff_aux _ _

@[simp]
theorem of_boolalg_mul_of_boolalg_eq_left_iff {a b : AsBoolalg α} : ofBoolalg a * ofBoolalg b = ofBoolalg a ↔ a ≤ b :=
  @inf_eq_left (AsBoolalg α) _ _ _

@[simp]
theorem to_boolalg_zero : toBoolalg (0 : α) = ⊥ :=
  rfl

@[simp]
theorem to_boolalg_one : toBoolalg (1 : α) = ⊤ :=
  rfl

@[simp]
theorem to_boolalg_mul (a b : α) : toBoolalg (a * b) = toBoolalg a⊓toBoolalg b :=
  rfl

-- `to_boolalg_add` simplifies the LHS but this lemma is eligible to `dsimp`
@[simp, nolint simp_nf]
theorem to_boolalg_add_add_mul (a b : α) : toBoolalg (a + b + a * b) = toBoolalg a⊔toBoolalg b :=
  rfl

@[simp]
theorem to_boolalg_add (a b : α) : toBoolalg (a + b) = toBoolalg a ∆ toBoolalg b :=
  (of_boolalg_symm_diff _ _).symm

/-- Turn a ring homomorphism from Boolean rings `α` to `β` into a bounded lattice homomorphism
from `α` to `β` considered as Boolean algebras. -/
@[simps]
protected def RingHom.asBoolalg (f : α →+* β) : BoundedLatticeHom (AsBoolalg α) (AsBoolalg β) where
  toFun := toBoolalg ∘ f ∘ ofBoolalg
  map_sup' := fun a b => by
    dsimp'
    simp_rw [map_add f, map_mul f]
    rfl
  map_inf' := f.map_mul'
  map_top' := f.map_one'
  map_bot' := f.map_zero'

@[simp]
theorem RingHom.as_boolalg_id : (RingHom.id α).AsBoolalg = BoundedLatticeHom.id _ :=
  rfl

@[simp]
theorem RingHom.as_boolalg_comp (g : β →+* γ) (f : α →+* β) : (g.comp f).AsBoolalg = g.AsBoolalg.comp f.AsBoolalg :=
  rfl

end RingToAlgebra

/-! ### Turning a Boolean algebra into a Boolean ring -/


section AlgebraToRing

/-- Type synonym to view a Boolean ring as a Boolean algebra. -/
def AsBoolring (α : Type _) :=
  α

/-- The "identity" equivalence between `as_boolring α` and `α`. -/
def toBoolring : α ≃ AsBoolring α :=
  Equivₓ.refl _

/-- The "identity" equivalence between `α` and `as_boolring α`. -/
def ofBoolring : AsBoolring α ≃ α :=
  Equivₓ.refl _

@[simp]
theorem to_boolring_symm_eq : (@toBoolring α).symm = ofBoolring :=
  rfl

@[simp]
theorem of_boolring_symm_eq : (@ofBoolring α).symm = toBoolring :=
  rfl

@[simp]
theorem to_boolring_of_boolring (a : AsBoolring α) : toBoolring (ofBoolring a) = a :=
  rfl

@[simp]
theorem of_boolring_to_boolring (a : α) : ofBoolring (toBoolring a) = a :=
  rfl

@[simp]
theorem to_boolring_inj {a b : α} : toBoolring a = toBoolring b ↔ a = b :=
  Iff.rfl

@[simp]
theorem of_boolring_inj {a b : AsBoolring α} : ofBoolring a = ofBoolring b ↔ a = b :=
  Iff.rfl

instance [Inhabited α] : Inhabited (AsBoolring α) :=
  ‹Inhabited α›

/-- Every generalized Boolean algebra has the structure of a non unital commutative ring with the
following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
-/
-- See note [reducible non-instances]
@[reducible]
def GeneralizedBooleanAlgebra.toNonUnitalCommRing [GeneralizedBooleanAlgebra α] : NonUnitalCommRing α where
  add := (· ∆ ·)
  add_assoc := symm_diff_assoc
  zero := ⊥
  zero_add := bot_symm_diff
  add_zero := symm_diff_bot
  zero_mul := fun _ => bot_inf_eq
  mul_zero := fun _ => inf_bot_eq
  neg := id
  add_left_neg := symm_diff_self
  add_comm := symm_diff_comm
  mul := (·⊓·)
  mul_assoc := fun _ _ _ => inf_assoc
  mul_comm := fun _ _ => inf_comm
  left_distrib := inf_symm_diff_distrib_left
  right_distrib := inf_symm_diff_distrib_right

instance [GeneralizedBooleanAlgebra α] : NonUnitalCommRing (AsBoolring α) :=
  @GeneralizedBooleanAlgebra.toNonUnitalCommRing α _

variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ]

/-- Every Boolean algebra has the structure of a Boolean ring with the following data:

* `a + b` unfolds to `a ∆ b` (symmetric difference)
* `a * b` unfolds to `a ⊓ b`
* `-a` unfolds to `a`
* `0` unfolds to `⊥`
* `1` unfolds to `⊤`
-/
-- See note [reducible non-instances]
@[reducible]
def BooleanAlgebra.toBooleanRing : BooleanRing α :=
  { GeneralizedBooleanAlgebra.toNonUnitalCommRing with one := ⊤, one_mul := fun _ => top_inf_eq,
    mul_one := fun _ => inf_top_eq, mul_self := fun b => inf_idem }

localized [BooleanRingOfBooleanAlgebra]
  attribute [instance] GeneralizedBooleanAlgebra.toNonUnitalCommRing BooleanAlgebra.toBooleanRing

instance : BooleanRing (AsBoolring α) :=
  @BooleanAlgebra.toBooleanRing α _

@[simp]
theorem of_boolring_zero : ofBoolring (0 : AsBoolring α) = ⊥ :=
  rfl

@[simp]
theorem of_boolring_one : ofBoolring (1 : AsBoolring α) = ⊤ :=
  rfl

-- `sub_eq_add` proves this lemma but it is eligible for `dsimp`
@[simp, nolint simp_nf]
theorem of_boolring_neg (a : AsBoolring α) : ofBoolring (-a) = ofBoolring a :=
  rfl

@[simp]
theorem of_boolring_add (a b : AsBoolring α) : ofBoolring (a + b) = ofBoolring a ∆ ofBoolring b :=
  rfl

-- `sub_eq_add` simplifies the LHS but this lemma is eligible for `dsimp`
@[simp, nolint simp_nf]
theorem of_boolring_sub (a b : AsBoolring α) : ofBoolring (a - b) = ofBoolring a ∆ ofBoolring b :=
  rfl

@[simp]
theorem of_boolring_mul (a b : AsBoolring α) : ofBoolring (a * b) = ofBoolring a⊓ofBoolring b :=
  rfl

@[simp]
theorem of_boolring_le_of_boolring_iff {a b : AsBoolring α} : ofBoolring a ≤ ofBoolring b ↔ a * b = a :=
  inf_eq_left.symm

@[simp]
theorem to_boolring_bot : toBoolring (⊥ : α) = 0 :=
  rfl

@[simp]
theorem to_boolring_top : toBoolring (⊤ : α) = 1 :=
  rfl

@[simp]
theorem to_boolring_inf (a b : α) : toBoolring (a⊓b) = toBoolring a * toBoolring b :=
  rfl

@[simp]
theorem to_boolring_symm_diff (a b : α) : toBoolring (a ∆ b) = toBoolring a + toBoolring b :=
  rfl

/-- Turn a bounded lattice homomorphism from Boolean algebras `α` to `β` into a ring homomorphism
from `α` to `β` considered as Boolean rings. -/
@[simps]
protected def BoundedLatticeHom.asBoolring (f : BoundedLatticeHom α β) : AsBoolring α →+* AsBoolring β where
  toFun := toBoolring ∘ f ∘ ofBoolring
  map_zero' := f.map_bot'
  map_one' := f.map_top'
  map_add' := map_symm_diff f
  map_mul' := f.map_inf'

@[simp]
theorem BoundedLatticeHom.as_boolring_id : (BoundedLatticeHom.id α).AsBoolring = RingHom.id _ :=
  rfl

@[simp]
theorem BoundedLatticeHom.as_boolring_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    (g.comp f).AsBoolring = g.AsBoolring.comp f.AsBoolring :=
  rfl

end AlgebraToRing

/-! ### Equivalence between Boolean rings and Boolean algebras -/


/-- Order isomorphism between `α` considered as a Boolean ring considered as a Boolean algebra and
`α`. -/
@[simps]
def OrderIso.asBoolalgAsBoolring (α : Type _) [BooleanAlgebra α] : AsBoolalg (AsBoolring α) ≃o α :=
  ⟨ofBoolalg.trans ofBoolring, fun a b => of_boolring_le_of_boolring_iff.trans of_boolalg_mul_of_boolalg_eq_left_iff⟩

/-- Ring isomorphism between `α` considered as a Boolean algebra considered as a Boolean ring and
`α`. -/
@[simps]
def RingEquiv.asBoolringAsBoolalg (α : Type _) [BooleanRing α] : AsBoolring (AsBoolalg α) ≃+* α :=
  { ofBoolring.trans ofBoolalg with map_mul' := fun a b => rfl, map_add' := of_boolalg_symm_diff }

open Bool

instance : BooleanRing Bool where
  add := bxor
  add_assoc := bxor_assoc
  zero := false
  zero_add := ff_bxor
  add_zero := bxor_ff
  neg := id
  sub := bxor
  sub_eq_add_neg := fun _ _ => rfl
  add_left_neg := bxor_self
  add_comm := bxor_comm
  one := true
  mul := band
  mul_assoc := band_assoc
  one_mul := tt_band
  mul_one := band_tt
  left_distrib := band_bxor_distrib_left
  right_distrib := band_bxor_distrib_right
  mul_self := band_self

