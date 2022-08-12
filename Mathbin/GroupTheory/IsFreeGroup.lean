/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Eric Wieser, Joachim Breitner
-/
import Mathbin.GroupTheory.FreeGroup

/-!
# Free groups structures on arbitrary types

This file defines a type class for type that are free groups, together with the usual operations.
The type class can be instantiated by providing an isomorphim to the canonical free group, or by
proving that the universal property holds.

For the explicit construction of free groups, see `group_theory/free_group`.

## Main definitions

* `is_free_group G` - a typeclass to indicate that `G` is free over some generators
* `is_free_group.of` - the canonical injection of `G`'s generators into `G`
* `is_free_group.lift` - the universal property of the free group

## Main results

* `is_free_group.to_free_group` - any free group with generators `A` is equivalent to
  `free_group A`.
* `is_free_group.unique_lift` - the universal property of a free group
* `is_free_group.of_unique_lift` - constructing `is_free_group` from the universal property

-/


universe u

-- ./././Mathport/Syntax/Translate/Basic.lean:1440:30: infer kinds are unsupported in Lean 4: #[`MulEquiv] []
/-- `is_free_group G` means that `G` isomorphic to a free group. -/
class IsFreeGroup (G : Type u) [Groupₓ G] where
  Generators : Type u
  MulEquiv : FreeGroup generators ≃* G

instance (X : Type _) : IsFreeGroup (FreeGroup X) where
  Generators := X
  MulEquiv := MulEquiv.refl _

namespace IsFreeGroup

variable (G : Type _) [Groupₓ G] [IsFreeGroup G]

/-- Any free group is isomorphic to "the" free group. -/
@[simps]
def toFreeGroup : G ≃* FreeGroup (Generators G) :=
  (mulEquiv G).symm

variable {G}

/-- The canonical injection of G's generators into G -/
def of : Generators G → G :=
  (mulEquiv G).toFun ∘ FreeGroup.of

@[simp]
theorem of_eq_free_group_of {A : Type u} : @of (FreeGroup A) _ _ = FreeGroup.of :=
  rfl

variable {H : Type _} [Groupₓ H]

/-- The equivalence between functions on the generators and group homomorphisms from a free group
given by those generators. -/
def lift : (Generators G → H) ≃ (G →* H) :=
  FreeGroup.lift.trans
    { toFun := fun f => f.comp (mulEquiv G).symm.toMonoidHom, invFun := fun f => f.comp (mulEquiv G).toMonoidHom,
      left_inv := fun f => by
        ext
        simp ,
      right_inv := fun f => by
        ext
        simp }

@[simp]
theorem lift'_eq_free_group_lift {A : Type u} : @lift (FreeGroup A) _ _ H _ = FreeGroup.lift :=
  rfl

@[simp]
theorem lift_of (f : Generators G → H) (a : Generators G) : lift f (of a) = f a :=
  congr_fun (lift.symm_apply_apply f) a

@[simp]
theorem lift_symm_apply (f : G →* H) (a : Generators G) : (lift.symm f) a = f (of a) :=
  rfl

@[ext]
theorem ext_hom ⦃f g : G →* H⦄ (h : ∀ a : Generators G, f (of a) = g (of a)) : f = g :=
  lift.symm.Injective (funext h)

/-- The universal property of a free group: A functions from the generators of `G` to another
group extends in a unique way to a homomorphism from `G`.

Note that since `is_free_group.lift` is expressed as a bijection, it already
expresses the universal property.  -/
theorem unique_lift (f : Generators G → H) : ∃! F : G →* H, ∀ a, F (of a) = f a := by
  simpa only [← Function.funext_iffₓ] using lift.symm.bijective.exists_unique f

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `is_free_group.lift` and its properties. -/
def ofLift {G : Type u} [Groupₓ G] (X : Type u) (of : X → G) (lift : ∀ {H : Type u} [Groupₓ H], (X → H) ≃ (G →* H))
    (lift_of : ∀ {H : Type u} [Groupₓ H], ∀ (f : X → H) (a), lift f (of a) = f a) : IsFreeGroup G where
  Generators := X
  MulEquiv :=
    MonoidHom.toMulEquiv (FreeGroup.lift of) (lift FreeGroup.of)
      (by
        apply FreeGroup.ext_hom
        intro x
        simp only [← MonoidHom.coe_comp, ← Function.comp_app, ← MonoidHom.id_apply, ← FreeGroup.lift.of, ← lift_of])
      (by
        let lift_symm_of : ∀ {H : Type u} [Groupₓ H], ∀ (f : G →* H) (a), lift.symm f a = f (of a) := by
          intro H _ f a <;> simp [lift_of (lift.symm f)]
        apply lift.symm.injective
        ext x
        simp only [← MonoidHom.coe_comp, ← Function.comp_app, ← MonoidHom.id_apply, ← FreeGroup.lift.of, ← lift_of, ←
          lift_symm_of])

/-- If a group satisfies the universal property of a free group, then it is a free group, where
the universal property is expressed as in `is_free_group.unique_lift`.  -/
noncomputable def ofUniqueLift {G : Type u} [Groupₓ G] (X : Type u) (of : X → G)
    (h : ∀ {H : Type u} [Groupₓ H] (f : X → H), ∃! F : G →* H, ∀ a, F (of a) = f a) : IsFreeGroup G :=
  let lift {H : Type u} [Groupₓ H] : (X → H) ≃ (G →* H) :=
    { toFun := fun f => Classical.some (h f), invFun := fun F => F ∘ of,
      left_inv := fun f => funext (Classical.some_spec (h f)).left,
      right_inv := fun F => ((Classical.some_spec (h (F ∘ of))).right F fun _ => rfl).symm }
  let lift_of {H : Type u} [Groupₓ H] (f : X → H) (a : X) : lift f (of a) = f a := congr_fun (lift.symm_apply_apply f) a
  ofLift X of @lift @lift_of

/-- Being a free group transports across group isomorphisms. -/
def ofMulEquiv {H : Type _} [Groupₓ H] (h : G ≃* H) : IsFreeGroup H where
  Generators := Generators G
  MulEquiv := (mulEquiv G).trans h

end IsFreeGroup

