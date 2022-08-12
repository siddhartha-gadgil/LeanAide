/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.GroupTheory.Perm.Basic

/-!
# Multiplicative and additive group automorphisms

This file defines the automorphism group structure on `add_aut R := add_equiv R R` and
`mul_aut R := mul_equiv R R`.

## Implementation notes

The definition of multiplication in the automorphism groups agrees with function composition,
multiplication in `equiv.perm`, and multiplication in `category_theory.End`, but not with
`category_theory.comp`.

This file is kept separate from `data/equiv/mul_add` so that `group_theory.perm` is free to use
equivalences (and other files that use them) before the group structure is defined.

## Tags

mul_aut, add_aut
-/


variable {A : Type _} {M : Type _} {G : Type _}

/-- The group of multiplicative automorphisms. -/
@[reducible, to_additive "The group of additive automorphisms."]
def MulAut (M : Type _) [Mul M] :=
  M ≃* M

namespace MulAut

variable (M) [Mul M]

/-- The group operation on multiplicative automorphisms is defined by
`λ g h, mul_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance : Groupₓ (MulAut M) := by
  refine_struct
      { mul := fun g h => MulEquiv.trans h g, one := MulEquiv.refl M, inv := MulEquiv.symm, div := _,
        npow := @npowRec _ ⟨MulEquiv.refl M⟩ ⟨fun g h => MulEquiv.trans h g⟩,
        zpow := @zpowRec _ ⟨MulEquiv.refl M⟩ ⟨fun g h => MulEquiv.trans h g⟩ ⟨MulEquiv.symm⟩ } <;>
    intros <;>
      ext <;>
        try
            rfl <;>
          apply Equivₓ.left_inv

instance : Inhabited (MulAut M) :=
  ⟨1⟩

@[simp]
theorem coe_mul (e₁ e₂ : MulAut M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : MulAut M) = id :=
  rfl

theorem mul_def (e₁ e₂ : MulAut M) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : MulAut M) = MulEquiv.refl _ :=
  rfl

theorem inv_def (e₁ : MulAut M) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : MulAut M) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[simp]
theorem one_apply (m : M) : (1 : MulAut M) m = m :=
  rfl

@[simp]
theorem apply_inv_self (e : MulAut M) (m : M) : e (e⁻¹ m) = m :=
  MulEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : MulAut M) (m : M) : e⁻¹ (e m) = m :=
  MulEquiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : MulAut M →* Equivₓ.Perm M := by
  refine_struct { toFun := MulEquiv.toEquiv } <;> intros <;> rfl

/-- The tautological action by `mul_aut M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance applyMulDistribMulAction {M} [Monoidₓ M] : MulDistribMulAction (MulAut M) M where
  smul := (· <| ·)
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_one := MulEquiv.map_one
  smul_mul := MulEquiv.map_mul

@[simp]
protected theorem smul_def {M} [Monoidₓ M] (f : MulAut M) (a : M) : f • a = f a :=
  rfl

/-- `mul_aut.apply_mul_action` is faithful. -/
instance apply_has_faithful_smul {M} [Monoidₓ M] : HasFaithfulSmul (MulAut M) M :=
  ⟨fun _ _ => MulEquiv.ext⟩

/-- Group conjugation, `mul_aut.conj g h = g * h * g⁻¹`, as a monoid homomorphism
mapping multiplication in `G` into multiplication in the automorphism group `mul_aut G`.
See also the type `conj_act G` for any group `G`, which has a `mul_action (conj_act G) G` instance
where `conj G` acts on `G` by conjugation. -/
def conj [Groupₓ G] : G →* MulAut G where
  toFun := fun g =>
    { toFun := fun h => g * h * g⁻¹, invFun := fun h => g⁻¹ * h * g,
      left_inv := fun _ => by
        simp [← mul_assoc],
      right_inv := fun _ => by
        simp [← mul_assoc],
      map_mul' := by
        simp [← mul_assoc] }
  map_mul' := fun _ _ => by
    ext <;> simp [← mul_assoc]
  map_one' := by
    ext <;> simp [← mul_assoc]

@[simp]
theorem conj_apply [Groupₓ G] (g h : G) : conj g h = g * h * g⁻¹ :=
  rfl

@[simp]
theorem conj_symm_apply [Groupₓ G] (g h : G) : (conj g).symm h = g⁻¹ * h * g :=
  rfl

@[simp]
theorem conj_inv_apply [Groupₓ G] (g h : G) : (conj g)⁻¹ h = g⁻¹ * h * g :=
  rfl

end MulAut

namespace AddAut

variable (A) [Add A]

/-- The group operation on additive automorphisms is defined by
`λ g h, add_equiv.trans h g`.
This means that multiplication agrees with composition, `(g*h)(x) = g (h x)`.
-/
instance group : Groupₓ (AddAut A) := by
  refine_struct
      { mul := fun g h => AddEquiv.trans h g, one := AddEquiv.refl A, inv := AddEquiv.symm, div := _,
        npow := @npowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩,
        zpow := @zpowRec _ ⟨AddEquiv.refl A⟩ ⟨fun g h => AddEquiv.trans h g⟩ ⟨AddEquiv.symm⟩ } <;>
    intros <;>
      ext <;>
        try
            rfl <;>
          apply Equivₓ.left_inv

instance : Inhabited (AddAut A) :=
  ⟨1⟩

@[simp]
theorem coe_mul (e₁ e₂ : AddAut A) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : AddAut A) = id :=
  rfl

theorem mul_def (e₁ e₂ : AddAut A) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : AddAut A) = AddEquiv.refl _ :=
  rfl

theorem inv_def (e₁ : AddAut A) : e₁⁻¹ = e₁.symm :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : AddAut A) (a : A) : (e₁ * e₂) a = e₁ (e₂ a) :=
  rfl

@[simp]
theorem one_apply (a : A) : (1 : AddAut A) a = a :=
  rfl

@[simp]
theorem apply_inv_self (e : AddAut A) (a : A) : e⁻¹ (e a) = a :=
  AddEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : AddAut A) (a : A) : e (e⁻¹ a) = a :=
  AddEquiv.apply_symm_apply _ _

/-- Monoid hom from the group of multiplicative automorphisms to the group of permutations. -/
def toPerm : AddAut A →* Equivₓ.Perm A := by
  refine_struct { toFun := AddEquiv.toEquiv } <;> intros <;> rfl

/-- The tautological action by `add_aut A` on `A`.

This generalizes `function.End.apply_mul_action`. -/
instance applyDistribMulAction {A} [AddMonoidₓ A] : DistribMulAction (AddAut A) A where
  smul := (· <| ·)
  smul_zero := AddEquiv.map_zero
  smul_add := AddEquiv.map_add
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
protected theorem smul_def {A} [AddMonoidₓ A] (f : AddAut A) (a : A) : f • a = f a :=
  rfl

/-- `add_aut.apply_distrib_mul_action` is faithful. -/
instance apply_has_faithful_smul {A} [AddMonoidₓ A] : HasFaithfulSmul (AddAut A) A :=
  ⟨fun _ _ => AddEquiv.ext⟩

/-- Additive group conjugation, `add_aut.conj g h = g + h - g`, as an additive monoid
homomorphism mapping addition in `G` into multiplication in the automorphism group `add_aut G`
(written additively in order to define the map). -/
def conj [AddGroupₓ G] : G →+ Additive (AddAut G) where
  toFun := fun g =>
    @Additive.ofMul (AddAut G)
      { toFun := fun h => g + h + -g,-- this definition is chosen to match `mul_aut.conj`
        invFun := fun h => -g + h + g,
        left_inv := fun _ => by
          simp [← add_assocₓ],
        right_inv := fun _ => by
          simp [← add_assocₓ],
        map_add' := by
          simp [← add_assocₓ] }
  map_add' := fun _ _ => by
    apply additive.to_mul.injective <;> ext <;> simp [← add_assocₓ]
  map_zero' := by
    ext <;> simpa

@[simp]
theorem conj_apply [AddGroupₓ G] (g h : G) : conj g h = g + h + -g :=
  rfl

@[simp]
theorem conj_symm_apply [AddGroupₓ G] (g h : G) : (conj g).symm h = -g + h + g :=
  rfl

@[simp]
theorem conj_inv_apply [AddGroupₓ G] (g h : G) : (-conj g) h = -g + h + g :=
  rfl

end AddAut

