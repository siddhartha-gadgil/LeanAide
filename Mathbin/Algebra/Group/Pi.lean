/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.Hom.GroupInstances
import Mathbin.Data.Pi.Algebra
import Mathbin.Data.Set.Function
import Mathbin.Data.Set.Pairwise
import Mathbin.Tactic.PiInstances

/-!
# Pi instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

@[to_additive]
instance semigroup [∀ i, Semigroupₓ <| f i] : Semigroupₓ (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance semigroupWithZero [∀ i, SemigroupWithZeroₓ <| f i] : SemigroupWithZeroₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance commSemigroup [∀ i, CommSemigroupₓ <| f i] : CommSemigroupₓ (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance mulOneClass [∀ i, MulOneClassₓ <| f i] : MulOneClassₓ (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance monoid [∀ i, Monoidₓ <| f i] : Monoidₓ (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := fun n x i => x i ^ n } <;>
    run_tac
      tactic.pi_instance_derive_field

-- the attributes are intentionally out of order. `smul_apply` proves `nsmul_apply`.
@[to_additive, simp]
theorem pow_apply [∀ i, Monoidₓ <| f i] (n : ℕ) : (x ^ n) i = x i ^ n :=
  rfl

@[to_additive]
instance commMonoid [∀ i, CommMonoidₓ <| f i] : CommMonoidₓ (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive Pi.subNegMonoid]
instance [∀ i, DivInvMonoidₓ <| f i] : DivInvMonoidₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := (· * ·), inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := fun z x i => x i ^ z } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance [∀ i, HasInvolutiveInv <| f i] : HasInvolutiveInv (∀ i, f i) := by
  refine_struct { inv := Inv.inv } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive Pi.subtractionMonoid]
instance [∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := (· * ·), inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := fun z x i => x i ^ z } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive Pi.subtractionCommMonoid]
instance [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i) :=
  { Pi.divisionMonoid, Pi.commSemigroup with }

@[to_additive]
instance group [∀ i, Groupₓ <| f i] : Groupₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := (· * ·), inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := DivInvMonoidₓ.zpow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive]
instance commGroup [∀ i, CommGroupₓ <| f i] : CommGroupₓ (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i), mul := (· * ·), inv := Inv.inv, div := Div.div, npow := Monoidₓ.npow,
        zpow := DivInvMonoidₓ.zpow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] : LeftCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] : RightCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow.. } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddCancelMonoid]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

@[to_additive AddCancelCommMonoid]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i : I, f i) := by
  refine_struct { one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance mulZeroClass [∀ i, MulZeroClassₓ <| f i] : MulZeroClassₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance mulZeroOneClass [∀ i, MulZeroOneClassₓ <| f i] : MulZeroOneClassₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := (· * ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance monoidWithZero [∀ i, MonoidWithZeroₓ <| f i] : MonoidWithZeroₓ (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i : I, f i) := by
  refine_struct { zero := (0 : ∀ i, f i), one := (1 : ∀ i, f i), mul := (· * ·), npow := Monoidₓ.npow } <;>
    run_tac
      tactic.pi_instance_derive_field

end Pi

namespace MulHom

@[to_additive]
theorem coe_mul {M N} {mM : Mul M} {mN : CommSemigroupₓ N} (f g : M →ₙ* N) : (f * g : M → N) = fun x => f x * g x :=
  rfl

end MulHom

section MulHom

variable (f) [∀ i, Mul (f i)]

/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `function.eval i` as a `mul_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive semigroups at a\npoint is an additive semigroup homomorphism.\nThis is `function.eval i` as an `add_hom`.",
  simps]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i where
  toFun := fun g => g i
  map_mul' := fun x y => Pi.mul_apply _ _ i

/-- `function.const` as a `mul_hom`. -/
@[to_additive "`function.const` as an `add_hom`.", simps]
def Pi.constMulHom (α β : Type _) [Mul β] : β →ₙ* α → β where
  toFun := Function.const α
  map_mul' := fun _ _ => rfl

/-- Coercion of a `mul_hom` into a function is itself a `mul_hom`.
See also `mul_hom.eval`. -/
@[to_additive "Coercion of an `add_hom` into a function is itself a `add_hom`.\nSee also `add_hom.eval`. ", simps]
def MulHom.coeFn (α β : Type _) [Mul α] [CommSemigroupₓ β] : (α →ₙ* β) →ₙ* α → β where
  toFun := fun g => g
  map_mul' := fun x y => rfl

/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive semigroup homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive semigroup homomorphism `f` between `α` and `β`",
  simps]
protected def MulHom.compLeft {α β : Type _} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type _) : (I → α) →ₙ* I → β where
  toFun := fun h => f ∘ h
  map_mul' := fun _ _ => by
    ext <;> simp

end MulHom

section MonoidHom

variable (f) [∀ i, MulOneClassₓ (f i)]

/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `function.eval i` as a `monoid_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive monoids at a\npoint is an additive monoid homomorphism.\nThis is `function.eval i` as an `add_monoid_hom`.",
  simps]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i where
  toFun := fun g => g i
  map_one' := Pi.one_apply i
  map_mul' := fun x y => Pi.mul_apply _ _ i

/-- `function.const` as a `monoid_hom`. -/
@[to_additive "`function.const` as an `add_monoid_hom`.", simps]
def Pi.constMonoidHom (α β : Type _) [MulOneClassₓ β] : β →* α → β where
  toFun := Function.const α
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[to_additive
      "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.\n\nSee also `add_monoid_hom.eval`. ",
  simps]
def MonoidHom.coeFn (α β : Type _) [MulOneClassₓ α] [CommMonoidₓ β] : (α →* β) →* α → β where
  toFun := fun g => g
  map_one' := rfl
  map_mul' := fun x y => rfl

/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive monoid homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive monoid homomorphism `f` between `α` and `β`",
  simps]
protected def MonoidHom.compLeft {α β : Type _} [MulOneClassₓ α] [MulOneClassₓ β] (f : α →* β) (I : Type _) :
    (I → α) →* I → β where
  toFun := fun h => f ∘ h
  map_one' := by
    ext <;> simp
  map_mul' := fun _ _ => by
    ext <;> simp

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `one_hom` version of `pi.mul_single`. -/
@[to_additive ZeroHom.single
      "The zero-preserving homomorphism including a single value\ninto a dependent family of values, as functions supported at a point.\n\nThis is the `zero_hom` version of `pi.single`."]
def OneHom.single [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i) where
  toFun := mulSingle i
  map_one' := mul_single_one i

@[simp, to_additive]
theorem OneHom.single_apply [∀ i, One <| f i] (i : I) (x : f i) : OneHom.single f i x = mulSingle i x :=
  rfl

/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `monoid_hom` version of `pi.mul_single`. -/
@[to_additive
      "The additive monoid homomorphism including a single additive\nmonoid into a dependent family of additive monoids, as functions supported at a point.\n\nThis is the `add_monoid_hom` version of `pi.single`."]
def MonoidHom.single [∀ i, MulOneClassₓ <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.single f i with map_mul' := mul_single_op₂ (fun _ => (· * ·)) (fun _ => one_mulₓ _) _ }

@[simp, to_additive]
theorem MonoidHom.single_apply [∀ i, MulOneClassₓ <| f i] (i : I) (x : f i) : MonoidHom.single f i x = mulSingle i x :=
  rfl

/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps]
def MulHom.single [∀ i, MulZeroClassₓ <| f i] (i : I) : f i →ₙ* ∀ i, f i where
  toFun := single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _

variable {f}

@[to_additive]
theorem Pi.mul_single_mul [∀ i, MulOneClassₓ <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.single f i).map_mul x y

@[to_additive]
theorem Pi.mul_single_inv [∀ i, Groupₓ <| f i] (i : I) (x : f i) : mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.single f i).map_inv x

@[to_additive]
theorem Pi.single_div [∀ i, Groupₓ <| f i] (i : I) (x y : f i) : mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.single f i).map_div x y

theorem Pi.single_mul [∀ i, MulZeroClassₓ <| f i] (i : I) (x y : f i) : single i (x * y) = single i x * single i y :=
  (MulHom.single f i).map_mul x y

/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `commute.map` -/
@[to_additive
      "The injection into an additive pi group at different indices commutes.\n\nFor injections of commuting elements at the same index, see `add_commute.map`"]
theorem Pi.mul_single_commute [∀ i, MulOneClassₓ <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) := by
  intro i j hij x y
  ext k
  by_cases' h1 : i = k
  · subst h1
    simp [← hij]
    
  by_cases' h2 : j = k
  · subst h2
    simp [← hij]
    
  simp [← h1, ← h2]

/-- The injection into a pi group with the same values commutes. -/
@[to_additive "The injection into an additive pi group with the same values commutes."]
theorem Pi.mul_single_apply_commute [∀ i, MulOneClassₓ <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) := by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
    
  · exact Pi.mul_single_commute _ _ hij _ _
    

@[to_additive update_eq_sub_add_single]
theorem Pi.update_eq_div_mul_single [∀ i, Groupₓ <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
    
  · simp [← Function.update_noteq h.symm, ← h]
    

@[to_additive Pi.single_add_single_eq_single_add_single]
theorem Pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single {M : Type _} [CommMonoidₓ M] {k l m n : I} {u v : M}
    (hu : u ≠ 1) (hv : v ≠ 1) :
    mulSingle k u * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n :=
  by
  refine' ⟨fun h => _, _⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := (congr_fun h m).symm
    have hn := (congr_fun h n).symm
    simp only [← mul_apply, ← mul_single_apply, ← if_pos rfl] at hk hl hm hn
    rcases eq_or_ne k m with (rfl | hkm)
    · refine' Or.inl ⟨rfl, not_ne_iff.mp fun hln => (hv _).elim⟩
      rcases eq_or_ne k l with (rfl | hkl)
      · rwa [if_neg hln.symm, if_neg hln.symm, one_mulₓ, one_mulₓ] at hn
        
      · rwa [if_neg hkl.symm, if_neg hln, one_mulₓ, one_mulₓ] at hl
        
      
    · rcases eq_or_ne m n with (rfl | hmn)
      · rcases eq_or_ne k l with (rfl | hkl)
        · rw [if_neg hkm.symm, if_neg hkm.symm, one_mulₓ, if_pos rfl] at hm
          exact Or.inr (Or.inr ⟨hm, rfl, rfl⟩)
          
        · simpa only [← if_neg hkm, ← if_neg hkl, ← mul_oneₓ] using hk
          
        
      · rw [if_neg hkm.symm, if_neg hmn, one_mulₓ, mul_oneₓ] at hm
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1
        rw [if_neg hkm, if_neg hkm, one_mulₓ, mul_oneₓ] at hk
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1
        exact Or.inr (Or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩)
        
      
    
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · rfl
      
    · apply mul_comm
      
    · simp_rw [← Pi.mul_single_mul, h, mul_single_one]
      
    

end Single

namespace Function

@[simp, to_additive]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i 1

@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
    update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· * ·)) f₁ f₂ i x₁ x₂ j).symm

@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun i => Inv.inv) f₁ i x₁ j).symm

@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i) (x₂ : f i) :
    update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· / ·)) f₁ f₂ i x₁ x₂ j).symm

end Function

section Piecewise

@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· * ·)

@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹

@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· / ·)

end Piecewise

section Extend

variable {ι : Type u} {η : Type v} (R : Type w) (s : ι → η)

/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive Function.ExtendByZero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def Function.ExtendByOne.hom [MulOneClassₓ R] : (ι → R) →* η → R where
  toFun := fun f => Function.extendₓ s f 1
  map_one' := Function.extend_one s
  map_mul' := fun f g => by
    simpa using Function.extend_mul s f g 1 1

end Extend

