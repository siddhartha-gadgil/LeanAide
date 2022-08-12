/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Algebra.GroupPower.Basic

/-!
# Instances on spaces of monoid and group morphisms

We endow the space of monoid morphisms `M →* N` with a `comm_monoid` structure when the target is
commutative, through pointwise multiplication, and with a `comm_group` structure when the target
is a commutative group. We also prove the same instances for additive situations.

Since these structures permit morphisms of morphisms, we also provide some composition-like
operations.

Finally, we provide the `ring` structure on `add_monoid.End`.
-/


universe uM uN uP uQ

variable {M : Type uM} {N : Type uN} {P : Type uP} {Q : Type uQ}

/-- `(M →* N)` is a `comm_monoid` if `N` is commutative. -/
@[to_additive "`(M →+ N)` is an `add_comm_monoid` if `N` is commutative."]
instance [MulOneClassₓ M] [CommMonoidₓ N] : CommMonoidₓ (M →* N) where
  mul := (· * ·)
  mul_assoc := by
    intros <;> ext <;> apply mul_assoc
  one := 1
  one_mul := by
    intros <;> ext <;> apply one_mulₓ
  mul_one := by
    intros <;> ext <;> apply mul_oneₓ
  mul_comm := by
    intros <;> ext <;> apply mul_comm
  npow := fun n f =>
    { toFun := fun x => f x ^ n,
      map_one' := by
        simp ,
      map_mul' := fun x y => by
        simp [← mul_powₓ] }
  npow_zero' := fun f => by
    ext x
    simp
  npow_succ' := fun n f => by
    ext x
    simp [← pow_succₓ]

/-- If `G` is a commutative group, then `M →* G` is a commutative group too. -/
@[to_additive "If `G` is an additive commutative group, then `M →+ G` is an additive commutative\ngroup too."]
instance {M G} [MulOneClassₓ M] [CommGroupₓ G] : CommGroupₓ (M →* G) :=
  { MonoidHom.commMonoid with inv := Inv.inv, div := Div.div,
    div_eq_mul_inv := by
      intros
      ext
      apply div_eq_mul_inv,
    mul_left_inv := by
      intros <;> ext <;> apply mul_left_invₓ,
    zpow := fun n f =>
      { toFun := fun x => f x ^ n,
        map_one' := by
          simp ,
        map_mul' := fun x y => by
          simp [← mul_zpow] },
    zpow_zero' := fun f => by
      ext x
      simp ,
    zpow_succ' := fun n f => by
      ext x
      simp [← zpow_of_nat, ← pow_succₓ],
    zpow_neg' := fun n f => by
      ext x
      simp }

instance [AddCommMonoidₓ M] : AddCommMonoidₓ (AddMonoidₓ.End M) :=
  AddMonoidHom.addCommMonoid

instance [AddCommMonoidₓ M] : Semiringₓ (AddMonoidₓ.End M) :=
  { AddMonoidₓ.End.monoid M, AddMonoidHom.addCommMonoid with zero_mul := fun x => AddMonoidHom.ext fun i => rfl,
    mul_zero := fun x => AddMonoidHom.ext fun i => AddMonoidHom.map_zero _,
    left_distrib := fun x y z => AddMonoidHom.ext fun i => AddMonoidHom.map_add _ _ _,
    right_distrib := fun x y z => AddMonoidHom.ext fun i => rfl, natCast := fun n => n • 1,
    nat_cast_zero := AddMonoidₓ.nsmul_zero' _,
    nat_cast_succ := fun n => (AddMonoidₓ.nsmul_succ' n 1).trans (add_commₓ _ _) }

instance [AddCommGroupₓ M] : Ringₓ (AddMonoidₓ.End M) :=
  { AddMonoidₓ.End.semiring, AddMonoidHom.addCommGroup with }

/-!
### Morphisms of morphisms

The structures above permit morphisms that themselves produce morphisms, provided the codomain
is commutative.
-/


namespace MonoidHom

@[to_additive]
theorem ext_iff₂ {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} {f g : M →* N →* P} :
    f = g ↔ ∀ x y, f x y = g x y :=
  MonoidHom.ext_iff.trans <| forall_congrₓ fun _ => MonoidHom.ext_iff

/-- `flip` arguments of `f : M →* N →* P` -/
@[to_additive "`flip` arguments of `f : M →+ N →+ P`"]
def flip {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} (f : M →* N →* P) : N →* M →* P where
  toFun := fun y =>
    ⟨fun x => f x y, by
      rw [f.map_one, one_apply], fun x₁ x₂ => by
      rw [f.map_mul, mul_apply]⟩
  map_one' := ext fun x => (f x).map_one
  map_mul' := fun y₁ y₂ => ext fun x => (f x).map_mul y₁ y₂

@[simp, to_additive]
theorem flip_apply {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} (f : M →* N →* P) (x : M) (y : N) :
    f.flip y x = f x y :=
  rfl

@[to_additive]
theorem map_one₂ {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} (f : M →* N →* P) (n : N) :
    f 1 n = 1 :=
  (flip f n).map_one

@[to_additive]
theorem map_mul₂ {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} (f : M →* N →* P) (m₁ m₂ : M)
    (n : N) : f (m₁ * m₂) n = f m₁ n * f m₂ n :=
  (flip f n).map_mul _ _

@[to_additive]
theorem map_inv₂ {mM : Groupₓ M} {mN : MulOneClassₓ N} {mP : CommGroupₓ P} (f : M →* N →* P) (m : M) (n : N) :
    f m⁻¹ n = (f m n)⁻¹ :=
  (flip f n).map_inv _

@[to_additive]
theorem map_div₂ {mM : Groupₓ M} {mN : MulOneClassₓ N} {mP : CommGroupₓ P} (f : M →* N →* P) (m₁ m₂ : M) (n : N) :
    f (m₁ / m₂) n = f m₁ n / f m₂ n :=
  (flip f n).map_div _ _

/-- Evaluation of a `monoid_hom` at a point as a monoid homomorphism. See also `monoid_hom.apply`
for the evaluation of any function at a point. -/
@[to_additive
      "Evaluation of an `add_monoid_hom` at a point as an additive monoid homomorphism.\nSee also `add_monoid_hom.apply` for the evaluation of any function at a point.",
  simps]
def eval [MulOneClassₓ M] [CommMonoidₓ N] : M →* (M →* N) →* N :=
  (MonoidHom.id (M →* N)).flip

/-- The expression `λ g m, g (f m)` as a `monoid_hom`.
Equivalently, `(λ g, monoid_hom.comp g f)` as a `monoid_hom`. -/
@[to_additive
      "The expression `λ g m, g (f m)` as a `add_monoid_hom`.\nEquivalently, `(λ g, monoid_hom.comp g f)` as a `add_monoid_hom`.\n\nThis also exists in a `linear_map` version, `linear_map.lcomp`.",
  simps]
def compHom' [MulOneClassₓ M] [MulOneClassₓ N] [CommMonoidₓ P] (f : M →* N) : (N →* P) →* M →* P :=
  flip <| eval.comp f

/-- Composition of monoid morphisms (`monoid_hom.comp`) as a monoid morphism.

Note that unlike `monoid_hom.comp_hom'` this requires commutativity of `N`. -/
@[to_additive
      "Composition of additive monoid morphisms (`add_monoid_hom.comp`) as an additive\nmonoid morphism.\n\nNote that unlike `add_monoid_hom.comp_hom'` this requires commutativity of `N`.\n\nThis also exists in a `linear_map` version, `linear_map.llcomp`.",
  simps]
def compHom [MulOneClassₓ M] [CommMonoidₓ N] [CommMonoidₓ P] : (N →* P) →* (M →* N) →* M →* P where
  toFun := fun g => { toFun := g.comp, map_one' := comp_one g, map_mul' := comp_mul g }
  map_one' := by
    ext1 f
    exact one_comp f
  map_mul' := fun g₁ g₂ => by
    ext1 f
    exact mul_comp g₁ g₂ f

/-- Flipping arguments of monoid morphisms (`monoid_hom.flip`) as a monoid morphism. -/
@[to_additive
      "Flipping arguments of additive monoid morphisms (`add_monoid_hom.flip`)\nas an additive monoid morphism.",
  simps]
def flipHom {mM : MulOneClassₓ M} {mN : MulOneClassₓ N} {mP : CommMonoidₓ P} : (M →* N →* P) →* N →* M →* P where
  toFun := MonoidHom.flip
  map_one' := rfl
  map_mul' := fun f g => rfl

/-- The expression `λ m q, f m (g q)` as a `monoid_hom`.

Note that the expression `λ q n, f (g q) n` is simply `monoid_hom.comp`. -/
@[to_additive
      "The expression `λ m q, f m (g q)` as an `add_monoid_hom`.\n\nNote that the expression `λ q n, f (g q) n` is simply `add_monoid_hom.comp`.\n\nThis also exists as a `linear_map` version, `linear_map.compl₂`"]
def compl₂ [MulOneClassₓ M] [MulOneClassₓ N] [CommMonoidₓ P] [MulOneClassₓ Q] (f : M →* N →* P) (g : Q →* N) :
    M →* Q →* P :=
  (compHom' g).comp f

@[simp, to_additive]
theorem compl₂_apply [MulOneClassₓ M] [MulOneClassₓ N] [CommMonoidₓ P] [MulOneClassₓ Q] (f : M →* N →* P) (g : Q →* N)
    (m : M) (q : Q) : (compl₂ f g) m q = f m (g q) :=
  rfl

/-- The expression `λ m n, g (f m n)` as a `monoid_hom`. -/
@[to_additive
      "The expression `λ m n, g (f m n)` as an `add_monoid_hom`.\n\nThis also exists as a linear_map version, `linear_map.compr₂`"]
def compr₂ [MulOneClassₓ M] [MulOneClassₓ N] [CommMonoidₓ P] [CommMonoidₓ Q] (f : M →* N →* P) (g : P →* Q) :
    M →* N →* Q :=
  (compHom g).comp f

@[simp, to_additive]
theorem compr₂_apply [MulOneClassₓ M] [MulOneClassₓ N] [CommMonoidₓ P] [CommMonoidₓ Q] (f : M →* N →* P) (g : P →* Q)
    (m : M) (n : N) : (compr₂ f g) m n = g (f m n) :=
  rfl

end MonoidHom

/-!
### Miscellaneous definitions

Due to the fact this file imports `algebra.group_power.basic`, it is not possible to import it in
some of the lower-level files like `algebra.ring.basic`. The following lemmas should be rehomed
if the import structure permits them to be.
-/


section Semiringₓ

variable {R S : Type _} [NonUnitalNonAssocSemiringₓ R] [NonUnitalNonAssocSemiringₓ S]

/-- Multiplication of an element of a (semi)ring is an `add_monoid_hom` in both arguments.

This is a more-strongly bundled version of `add_monoid_hom.mul_left` and `add_monoid_hom.mul_right`.

A stronger version of this exists for algebras as `algebra.lmul`.
-/
def AddMonoidHom.mul : R →+ R →+ R where
  toFun := AddMonoidHom.mulLeft
  map_zero' := AddMonoidHom.ext <| zero_mul
  map_add' := fun a b => AddMonoidHom.ext <| add_mulₓ a b

theorem AddMonoidHom.mul_apply (x y : R) : AddMonoidHom.mul x y = x * y :=
  rfl

@[simp]
theorem AddMonoidHom.coe_mul : ⇑(AddMonoidHom.mul : R →+ R →+ R) = AddMonoidHom.mulLeft :=
  rfl

@[simp]
theorem AddMonoidHom.coe_flip_mul : ⇑(AddMonoidHom.mul : R →+ R →+ R).flip = AddMonoidHom.mulRight :=
  rfl

/-- An `add_monoid_hom` preserves multiplication if pre- and post- composition with
`add_monoid_hom.mul` are equivalent. By converting the statement into an equality of
`add_monoid_hom`s, this lemma allows various specialized `ext` lemmas about `→+` to then be applied.
-/
theorem AddMonoidHom.map_mul_iff (f : R →+ S) :
    (∀ x y, f (x * y) = f x * f y) ↔ (AddMonoidHom.mul : R →+ R →+ R).compr₂ f = (AddMonoidHom.mul.comp f).compl₂ f :=
  Iff.symm AddMonoidHom.ext_iff₂

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `add_monoid_hom.mul_left`. -/
@[simps]
def AddMonoidₓ.End.mulLeft : R →+ AddMonoidₓ.End R :=
  AddMonoidHom.mul

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `add_monoid_hom.mul_right`. -/
@[simps]
def AddMonoidₓ.End.mulRight : R →+ AddMonoidₓ.End R :=
  (AddMonoidHom.mul : R →+ AddMonoidₓ.End R).flip

end Semiringₓ

