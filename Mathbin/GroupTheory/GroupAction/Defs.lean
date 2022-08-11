/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathbin.Algebra.Group.TypeTags
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites
import Mathbin.Logic.Embedding

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `has_smul` and its additive version `has_vadd`:

* `mul_action M α` and its additive version `add_action G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `has_smul` and `has_vadd` that are defined in `algebra.group.defs`;
* `distrib_mul_action M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `smul_comm_class M N α` and its additive version `vadd_comm_class M N α`;
* `is_scalar_tower M N α` (no additive version).
* `is_central_scalar M α` (no additive version).

## Notation

- `a • b` is used as notation for `has_smul.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.

## Tags

group action
-/


variable {M N G A B α β γ δ : Type _}

open Function (Injective Surjective)

/-!
### Faithful actions
-/


/-- Typeclass for faithful actions. -/
class HasFaithfulVadd (G : Type _) (P : Type _) [HasVadd G P] : Prop where
  eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂

/-- Typeclass for faithful actions. -/
@[to_additive]
class HasFaithfulSmul (M : Type _) (α : Type _) [HasSmul M α] : Prop where
  eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂

export HasFaithfulSmul (eq_of_smul_eq_smul)

export HasFaithfulVadd (eq_of_vadd_eq_vadd)

@[to_additive]
theorem smul_left_injective' [HasSmul M α] [HasFaithfulSmul M α] : Function.Injective ((· • ·) : M → α → α) :=
  fun m₁ m₂ h => HasFaithfulSmul.eq_of_smul_eq_smul (congr_fun h)

/-- See also `monoid.to_mul_action` and `mul_zero_class.to_smul_with_zero`. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 910) Mul.toHasSmul (α : Type _) [Mul α] : HasSmul α α :=
  ⟨(· * ·)⟩

@[simp, to_additive]
theorem smul_eq_mul (α : Type _) [Mul α] {a a' : α} : a • a' = a * a' :=
  rfl

/-- Type class for additive monoid actions. -/
@[ext, protect_proj]
class AddAction (G : Type _) (P : Type _) [AddMonoidₓ G] extends HasVadd G P where
  zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p
  add_vadd : ∀ (g₁ g₂ : G) (p : P), g₁ + g₂ +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p)

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[ext, protect_proj, to_additive]
class MulAction (α : Type _) (β : Type _) [Monoidₓ α] extends HasSmul α β where
  one_smul : ∀ b : β, (1 : α) • b = b
  mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b

instance Additive.addAction [Monoidₓ α] [MulAction α β] : AddAction (Additive α) β where
  vadd := (· • ·) ∘ Additive.toMul
  zero_vadd := MulAction.one_smul
  add_vadd := MulAction.mul_smul

@[simp]
theorem Additive.of_mul_vadd [Monoidₓ α] [MulAction α β] (a : α) (b : β) : Additive.ofMul a +ᵥ b = a • b :=
  rfl

instance Multiplicative.mulAction [AddMonoidₓ α] [AddAction α β] : MulAction (Multiplicative α) β where
  smul := (· +ᵥ ·) ∘ Multiplicative.toAdd
  one_smul := AddAction.zero_vadd
  mul_smul := AddAction.add_vadd

@[simp]
theorem Multiplicative.of_add_smul [AddMonoidₓ α] [AddAction α β] (a : α) (b : β) :
    Multiplicative.ofAdd a • b = a +ᵥ b :=
  rfl

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `mul_action.is_pretransitive` and
`add_action.is_pretransitive` and provide `mul_action.exists_smul_eq`/`add_action.exists_vadd_eq`,
`mul_action.surjective_smul`/`add_action.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*_action.is_transitive`; users should assume
`[mul_action.is_pretransitive M α] [nonempty α]` instead. -/


/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
class AddAction.IsPretransitive (M α : Type _) [HasVadd M α] : Prop where
  exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive]
class MulAction.IsPretransitive (M α : Type _) [HasSmul M α] : Prop where
  exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y

namespace MulAction

variable (M) {α} [HasSmul M α] [IsPretransitive M α]

@[to_additive]
theorem exists_smul_eq (x y : α) : ∃ m : M, m • x = y :=
  IsPretransitive.exists_smul_eq x y

@[to_additive]
theorem surjective_smul (x : α) : Surjective fun c : M => c • x :=
  exists_smul_eq M x

/-- The regular action of a group on itself is transitive. -/
@[to_additive]
instance Regular.is_pretransitive [Groupₓ G] : IsPretransitive G G :=
  ⟨fun x y => ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

end MulAction

/-!
### Scalar tower and commuting actions
-/


/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class VaddCommClass (M N α : Type _) [HasVadd M α] [HasVadd N α] : Prop where
  vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a)

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive]
class SmulCommClass (M N α : Type _) [HasSmul M α] [HasSmul N α] : Prop where
  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a

export MulAction (mul_smul)

export AddAction (add_vadd)

export SmulCommClass (smul_comm)

export VaddCommClass (vadd_comm)

library_note "bundled maps over different rings"/--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `comm_semiring R`, and
not just `semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `smul_comm_class S R` on the appropriate modules. When
the caller has `comm_semiring R`, they can set `S = R` and `smul_comm_class_self` will populate the
instance. If the caller only has `semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`add_comm_monoid.nat_smul_comm_class` or `add_comm_monoid.nat_smul_comm_class'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `linear_map.prod_equiv`.
-/


/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive]
theorem SmulCommClass.symm (M N α : Type _) [HasSmul M α] [HasSmul N α] [SmulCommClass M N α] : SmulCommClass N M α :=
  ⟨fun a' a b => (smul_comm a a' b).symm⟩

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc VaddCommClass.symm

@[to_additive]
instance smul_comm_class_self (M α : Type _) [CommMonoidₓ M] [MulAction M α] : SmulCommClass M M α :=
  ⟨fun a a' b => by
    rw [← mul_smul, mul_comm, mul_smul]⟩

/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
class IsScalarTower (M N α : Type _) [HasSmul M N] [HasSmul N α] [HasSmul M α] : Prop where
  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z

@[simp]
theorem smul_assoc {M N} [HasSmul M N] [HasSmul N α] [HasSmul M α] [IsScalarTower M N α] (x : M) (y : N) (z : α) :
    (x • y) • z = x • y • z :=
  IsScalarTower.smul_assoc x y z

instance Semigroupₓ.is_scalar_tower [Semigroupₓ α] : IsScalarTower α α α :=
  ⟨mul_assoc⟩

/-- A typeclass indicating that the right (aka `mul_opposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
class IsCentralScalar (M α : Type _) [HasSmul M α] [HasSmul Mᵐᵒᵖ α] : Prop where
  op_smul_eq_smul : ∀ (m : M) (a : α), MulOpposite.op m • a = m • a

theorem IsCentralScalar.unop_smul_eq_smul {M α : Type _} [HasSmul M α] [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] (m : Mᵐᵒᵖ)
    (a : α) : MulOpposite.unop m • a = m • a :=
  MulOpposite.rec (fun m => (IsCentralScalar.op_smul_eq_smul _ _).symm) m

export IsCentralScalar (op_smul_eq_smul unop_smul_eq_smul)

-- these instances are very low priority, as there is usually a faster way to find these instances
instance (priority := 50) SmulCommClass.op_left [HasSmul M α] [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] [HasSmul N α]
    [SmulCommClass M N α] : SmulCommClass Mᵐᵒᵖ N α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m a, smul_comm]⟩

instance (priority := 50) SmulCommClass.op_right [HasSmul M α] [HasSmul N α] [HasSmul Nᵐᵒᵖ α] [IsCentralScalar N α]
    [SmulCommClass M N α] : SmulCommClass M Nᵐᵒᵖ α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul n (m • a), ← unop_smul_eq_smul n a, smul_comm]⟩

instance (priority := 50) IsScalarTower.op_left [HasSmul M α] [HasSmul Mᵐᵒᵖ α] [IsCentralScalar M α] [HasSmul M N]
    [HasSmul Mᵐᵒᵖ N] [IsCentralScalar M N] [HasSmul N α] [IsScalarTower M N α] : IsScalarTower Mᵐᵒᵖ N α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul m (n • a), ← unop_smul_eq_smul m n, smul_assoc]⟩

instance (priority := 50) IsScalarTower.op_right [HasSmul M α] [HasSmul M N] [HasSmul N α] [HasSmul Nᵐᵒᵖ α]
    [IsCentralScalar N α] [IsScalarTower M N α] : IsScalarTower M Nᵐᵒᵖ α :=
  ⟨fun m n a => by
    rw [← unop_smul_eq_smul n a, ← unop_smul_eq_smul (m • n) a, MulOpposite.unop_smul, smul_assoc]⟩

namespace HasSmul

variable [HasSmul M α]

/-- Auxiliary definition for `has_smul.comp`, `mul_action.comp_hom`,
`distrib_mul_action.comp_hom`, `module.comp_hom`, etc. -/
@[simp, to_additive " Auxiliary definition for `has_vadd.comp`, `add_action.comp_hom`, etc. "]
def Comp.smul (g : N → M) (n : N) (a : α) : α :=
  g n • a

variable (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`.

See note [reducible non-instances]. Since this is reducible, we make sure to go via
`has_smul.comp.smul` to prevent typeclass inference unfolding too far. -/
@[reducible,
  to_additive " An additive action of `M` on `α` and a function `N → M` induces\n  an additive action of `N` on `α` "]
def comp (g : N → M) : HasSmul N α where smul := HasSmul.Comp.smul g

variable {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `has_smul.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
theorem comp.is_scalar_tower [HasSmul M β] [HasSmul α β] [IsScalarTower M α β] (g : N → M) : by
    have := comp α g <;> have := comp β g <;> exact IsScalarTower N α β :=
  { smul_assoc := fun n => @smul_assoc _ _ _ _ _ _ _ (g n) }

/-- This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
theorem comp.smul_comm_class [HasSmul β α] [SmulCommClass M β α] (g : N → M) :
    have := comp α g
    SmulCommClass N β α :=
  { smul_comm := fun n => @smul_comm _ _ _ _ _ _ (g n) }

/-- This cannot be an instance because it can cause infinite loops whenever the `has_smul` arguments
are still metavariables.
-/
theorem comp.smul_comm_class' [HasSmul β α] [SmulCommClass β M α] (g : N → M) :
    have := comp α g
    SmulCommClass β N α :=
  { smul_comm := fun _ n => @smul_comm _ _ _ _ _ _ _ (g n) }

end HasSmul

section

/-- Note that the `smul_comm_class α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
@[to_additive]
theorem mul_smul_comm [Mul β] [HasSmul α β] [SmulCommClass α β β] (s : α) (x y : β) : x * s • y = s • (x * y) :=
  (smul_comm s x y).symm

/-- Note that the `is_scalar_tower α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
theorem smul_mul_assoc [Mul β] [HasSmul α β] [IsScalarTower α β β] (r : α) (x y : β) : r • x * y = r • (x * y) :=
  smul_assoc r x y

theorem smul_smul_smul_comm [HasSmul α β] [HasSmul α γ] [HasSmul β δ] [HasSmul α δ] [HasSmul γ δ] [IsScalarTower α β δ]
    [IsScalarTower α γ δ] [SmulCommClass β γ δ] (a : α) (b : β) (c : γ) (d : δ) : (a • b) • c • d = (a • c) • b • d :=
  by
  rw [smul_assoc, smul_assoc, smul_comm b]
  infer_instance

variable [HasSmul M α]

theorem Commute.smul_right [Mul α] [SmulCommClass M α α] [IsScalarTower M α α] {a b : α} (h : Commute a b) (r : M) :
    Commute a (r • b) :=
  (mul_smul_comm _ _ _).trans ((congr_arg _ h).trans <| (smul_mul_assoc _ _ _).symm)

theorem Commute.smul_left [Mul α] [SmulCommClass M α α] [IsScalarTower M α α] {a b : α} (h : Commute a b) (r : M) :
    Commute (r • a) b :=
  (h.symm.smul_right r).symm

end

section ite

variable [HasSmul M α] (p : Prop) [Decidable p]

@[to_additive]
theorem ite_smul (a₁ a₂ : M) (b : α) : ite p a₁ a₂ • b = ite p (a₁ • b) (a₂ • b) := by
  split_ifs <;> rfl

@[to_additive]
theorem smul_ite (a : M) (b₁ b₂ : α) : a • ite p b₁ b₂ = ite p (a • b₁) (a • b₂) := by
  split_ifs <;> rfl

end ite

section

variable [Monoidₓ M] [MulAction M α]

@[to_additive]
theorem smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b :=
  (mul_smul _ _ _).symm

variable (M)

@[simp, to_additive]
theorem one_smul (b : α) : (1 : M) • b = b :=
  MulAction.one_smul _

/-- `has_smul` version of `one_mul_eq_id` -/
@[to_additive]
theorem one_smul_eq_id : ((· • ·) (1 : M) : α → α) = id :=
  funext <| one_smul _

/-- `has_smul` version of `comp_mul_left` -/
@[to_additive]
theorem comp_smul_left (a₁ a₂ : M) : (· • ·) a₁ ∘ (· • ·) a₂ = ((· • ·) (a₁ * a₂) : α → α) :=
  funext fun _ => (mul_smul _ _ _).symm

variable {M}

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def Function.Injective.mulAction [HasSmul M β] (f : β → α) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul := fun x => hf <| (smul _ _).trans <| one_smul _ (f x)
  mul_smul := fun c₁ c₂ x =>
    hf <| by
      simp only [← smul, ← mul_smul]

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def Function.Surjective.mulAction [HasSmul M β] (f : α → β) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulAction M β where
  smul := (· • ·)
  one_smul := fun y => by
    rcases hf y with ⟨x, rfl⟩
    rw [← smul, one_smul]
  mul_smul := fun c₁ c₂ y => by
    rcases hf y with ⟨x, rfl⟩
    simp only [smul, ← mul_smul]

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.distrib_mul_action_left` and `function.surjective.module_left`.
-/
@[reducible, to_additive "Push forward the action of `R` on `M` along a compatible\nsurjective map `f : R →+ S`."]
def Function.Surjective.mulActionLeft {R S M : Type _} [Monoidₓ R] [MulAction R M] [Monoidₓ S] [HasSmul S M]
    (f : R →* S) (hf : Function.Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) : MulAction S M where
  smul := (· • ·)
  one_smul := fun b => by
    rw [← f.map_one, hsmul, one_smul]
  mul_smul :=
    hf.Forall₂.mpr fun a b x => by
      simp only [f.map_mul, ← hsmul, ← mul_smul]

section

variable (M)

/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `semiring.to_module`. -/
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 910) Monoidₓ.toMulAction : MulAction M M where
  smul := (· * ·)
  one_smul := one_mulₓ
  mul_smul := mul_assoc

/-- The regular action of a monoid on itself by left addition.

This is promoted to an `add_torsor` by `add_group_is_add_torsor`. -/
add_decl_doc AddMonoidₓ.toAddAction

instance IsScalarTower.left : IsScalarTower M M α :=
  ⟨fun x y z => mul_smul x y z⟩

variable {M}

/-- Note that the `is_scalar_tower M α α` and `smul_comm_class M α α` typeclass arguments are
usually satisfied by `algebra M α`. -/
theorem smul_mul_smul [Mul α] (r s : M) (x y : α) [IsScalarTower M α α] [SmulCommClass M α α] :
    r • x * s • y = (r * s) • (x * y) := by
  rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]

end

namespace MulAction

variable (M α)

/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive]
def toFun : α ↪ M → α :=
  ⟨fun y x => x • y, fun y₁ y₂ H =>
    one_smul M y₁ ▸
      one_smul M y₂ ▸ by
        convert congr_fun H 1⟩

/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/
add_decl_doc AddAction.toFun

variable {M α}

@[simp, to_additive]
theorem to_fun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y :=
  rfl

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[reducible, to_additive]
def compHom [Monoidₓ N] (g : N →* M) : MulAction N α where
  smul := HasSmul.Comp.smul g
  one_smul := by
    simp [← g.map_one, ← MulAction.one_smul]
  mul_smul := by
    simp [← g.map_mul, ← MulAction.mul_smul]

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc AddAction.compHom

end MulAction

end

section CompatibleScalar

@[simp]
theorem smul_one_smul {M} (N) [Monoidₓ N] [HasSmul M N] [MulAction N α] [HasSmul M α] [IsScalarTower M N α] (x : M)
    (y : α) : (x • (1 : N)) • y = x • y := by
  rw [smul_assoc, one_smul]

@[simp]
theorem smul_one_mul {M N} [MulOneClassₓ N] [HasSmul M N] [IsScalarTower M N N] (x : M) (y : N) : x • 1 * y = x • y :=
  by
  rw [smul_mul_assoc, one_mulₓ]

@[simp, to_additive]
theorem mul_smul_one {M N} [MulOneClassₓ N] [HasSmul M N] [SmulCommClass M N N] (x : M) (y : N) : y * x • 1 = x • y :=
  by
  rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_oneₓ]

theorem IsScalarTower.of_smul_one_mul {M N} [Monoidₓ N] [HasSmul M N] (h : ∀ (x : M) (y : N), x • (1 : N) * y = x • y) :
    IsScalarTower M N N :=
  ⟨fun x y z => by
    rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive]
theorem SmulCommClass.of_mul_smul_one {M N} [Monoidₓ N] [HasSmul M N] (H : ∀ (x : M) (y : N), y * x • (1 : N) = x • y) :
    SmulCommClass M N N :=
  ⟨fun x y z => by
    rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

end CompatibleScalar

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext]
class DistribMulAction (M : Type _) (A : Type _) [Monoidₓ M] [AddMonoidₓ A] extends MulAction M A where
  smul_add : ∀ (r : M) (x y : A), r • (x + y) = r • x + r • y
  smul_zero : ∀ r : M, r • (0 : A) = 0

section

variable [Monoidₓ M] [AddMonoidₓ A] [DistribMulAction M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
  DistribMulAction.smul_add _ _ _

@[simp]
theorem smul_zero (a : M) : a • (0 : A) = 0 :=
  DistribMulAction.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distribMulAction [AddMonoidₓ B] [HasSmul M B] (f : B →+ A) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.MulAction f smul with smul := (· • ·),
    smul_add := fun c x y =>
      hf <| by
        simp only [← smul, ← f.map_add, ← smul_add],
    smul_zero := fun c =>
      hf <| by
        simp only [← smul, ← f.map_zero, ← smul_zero] }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distribMulAction [AddMonoidₓ B] [HasSmul M B] (f : A →+ B) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : DistribMulAction M B :=
  { hf.MulAction f smul with smul := (· • ·),
    smul_add := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [← smul_add, smul, f.map_add],
    smul_zero := fun c => by
      simp only [f.map_zero, smul, ← smul_zero] }

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.mul_action_left` and `function.surjective.module_left`.
-/
@[reducible]
def Function.Surjective.distribMulActionLeft {R S M : Type _} [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M]
    [Monoidₓ S] [HasSmul S M] (f : R →* S) (hf : Function.Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    DistribMulAction S M :=
  { hf.mulActionLeft f hsmul with smul := (· • ·),
    smul_zero :=
      hf.forall.mpr fun c => by
        rw [hsmul, smul_zero],
    smul_add :=
      hf.forall.mpr fun c x y => by
        simp only [← hsmul, ← smul_add] }

variable (A)

/-- Compose a `distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def DistribMulAction.compHom [Monoidₓ N] (f : N →* M) : DistribMulAction N A :=
  { MulAction.compHom A f with smul := HasSmul.Comp.smul f, smul_zero := fun x => smul_zero (f x),
    smul_add := fun x => smul_add (f x) }

/-- Each element of the monoid defines a additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidHom (x : M) : A →+ A where
  toFun := (· • ·) x
  map_zero' := smul_zero x
  map_add' := smul_add x

variable (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
def DistribMulAction.toAddMonoidEnd : M →* AddMonoidₓ.End A where
  toFun := DistribMulAction.toAddMonoidHom A
  map_one' := AddMonoidHom.ext <| one_smul M
  map_mul' := fun x y => AddMonoidHom.ext <| mul_smul x y

instance AddMonoidₓ.nat_smul_comm_class :
    SmulCommClass ℕ M A where smul_comm := fun n x y => ((DistribMulAction.toAddMonoidHom A x).map_nsmul y n).symm

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance AddMonoidₓ.nat_smul_comm_class' : SmulCommClass M ℕ A :=
  SmulCommClass.symm _ _ _

end

section

variable [Monoidₓ M] [AddGroupₓ A] [DistribMulAction M A]

instance AddGroupₓ.int_smul_comm_class :
    SmulCommClass ℤ M A where smul_comm := fun n x y => ((DistribMulAction.toAddMonoidHom A x).map_zsmul y n).symm

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance AddGroupₓ.int_smul_comm_class' : SmulCommClass M ℤ A :=
  SmulCommClass.symm _ _ _

@[simp]
theorem smul_neg (r : M) (x : A) : r • -x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← smul_add, neg_add_selfₓ, smul_zero]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end

/-- Typeclass for multiplicative actions on multiplicative structures. This generalizes
conjugation actions. -/
@[ext]
class MulDistribMulAction (M : Type _) (A : Type _) [Monoidₓ M] [Monoidₓ A] extends MulAction M A where
  smul_mul : ∀ (r : M) (x y : A), r • (x * y) = r • x * r • y
  smul_one : ∀ r : M, r • (1 : A) = 1

export MulDistribMulAction (smul_one)

section

variable [Monoidₓ M] [Monoidₓ A] [MulDistribMulAction M A]

theorem smul_mul' (a : M) (b₁ b₂ : A) : a • (b₁ * b₂) = a • b₁ * a • b₂ :=
  MulDistribMulAction.smul_mul _ _ _

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulDistribMulAction [Monoidₓ B] [HasSmul M B] (f : B →* A) (hf : Injective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.MulAction f smul with smul := (· • ·),
    smul_mul := fun c x y =>
      hf <| by
        simp only [← smul, ← f.map_mul, ← smul_mul'],
    smul_one := fun c =>
      hf <| by
        simp only [← smul, ← f.map_one, ← smul_one] }

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulDistribMulAction [Monoidₓ B] [HasSmul M B] (f : A →* B) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B :=
  { hf.MulAction f smul with smul := (· • ·),
    smul_mul := fun c x y => by
      rcases hf x with ⟨x, rfl⟩
      rcases hf y with ⟨y, rfl⟩
      simp only [← smul_mul', smul, f.map_mul],
    smul_one := fun c => by
      simp only [f.map_one, smul, ← smul_one] }

variable (A)

/-- Compose a `mul_distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible]
def MulDistribMulAction.compHom [Monoidₓ N] (f : N →* M) : MulDistribMulAction N A :=
  { MulAction.compHom A f with smul := HasSmul.Comp.smul f, smul_one := fun x => smul_one (f x),
    smul_mul := fun x => smul_mul' (f x) }

/-- Scalar multiplication by `r` as a `monoid_hom`. -/
def MulDistribMulAction.toMonoidHom (r : M) : A →* A where
  toFun := (· • ·) r
  map_one' := smul_one r
  map_mul' := smul_mul' r

variable {A}

@[simp]
theorem MulDistribMulAction.to_monoid_hom_apply (r : M) (x : A) : MulDistribMulAction.toMonoidHom A r x = r • x :=
  rfl

variable (M A)

/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def MulDistribMulAction.toMonoidEnd : M →* Monoidₓ.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' := fun x y => MonoidHom.ext <| mul_smul x y

end

section

variable [Monoidₓ M] [Groupₓ A] [MulDistribMulAction M A]

@[simp]
theorem smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x

theorem smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  (MulDistribMulAction.toMonoidHom A r).map_div x y

end

variable (α)

/-- The monoid of endomorphisms.

Note that this is generalized by `category_theory.End` to categories other than `Type u`. -/
protected def Function.End :=
  α → α

instance : Monoidₓ (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc := fun f g h => rfl
  mul_one := fun f => rfl
  one_mul := fun f => rfl

instance : Inhabited (Function.End α) :=
  ⟨1⟩

variable {α}

/-- The tautological action by `function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `equiv.perm.apply_mul_action`
* `add_monoid.End.apply_distrib_mul_action`
* `add_aut.apply_distrib_mul_action`
* `mul_aut.apply_mul_distrib_mul_action`
* `ring_hom.apply_distrib_mul_action`
* `linear_equiv.apply_distrib_mul_action`
* `linear_map.apply_module`
* `ring_hom.apply_mul_semiring_action`
* `alg_equiv.apply_mul_semiring_action`
-/
instance Function.End.applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
theorem Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a :=
  rfl

/-- `function.End.apply_mul_action` is faithful. -/
instance Function.End.apply_has_faithful_smul : HasFaithfulSmul (Function.End α) α :=
  ⟨fun x y => funext⟩

/-- The tautological action by `add_monoid.End α` on `α`.

This generalizes `function.End.apply_mul_action`. -/
instance AddMonoidₓ.End.applyDistribMulAction [AddMonoidₓ α] : DistribMulAction (AddMonoidₓ.End α) α where
  smul := (· <| ·)
  smul_zero := AddMonoidHom.map_zero
  smul_add := AddMonoidHom.map_add
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
theorem AddMonoidₓ.End.smul_def [AddMonoidₓ α] (f : AddMonoidₓ.End α) (a : α) : f • a = f a :=
  rfl

/-- `add_monoid.End.apply_distrib_mul_action` is faithful. -/
instance AddMonoidₓ.End.apply_has_faithful_smul [AddMonoidₓ α] : HasFaithfulSmul (AddMonoidₓ.End α) α :=
  ⟨AddMonoidHom.ext⟩

/-- The monoid hom representing a monoid action.

When `M` is a group, see `mul_action.to_perm_hom`. -/
def MulAction.toEndHom [Monoidₓ M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' := fun x y => funext (mul_smul x y)

/-- The monoid action induced by a monoid hom to `function.End α`

See note [reducible non-instances]. -/
@[reducible]
def MulAction.ofEndHom [Monoidₓ M] (f : M →* Function.End α) : MulAction M α :=
  MulAction.compHom α f

/-- The tautological additive action by `additive (function.End α)` on `α`. -/
instance AddAction.functionEnd : AddAction (Additive (Function.End α)) α where
  vadd := (· <| ·)
  zero_vadd := fun _ => rfl
  add_vadd := fun _ _ _ => rfl

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `add_action.to_perm_hom`. -/
def AddAction.toEndHom [AddMonoidₓ M] [AddAction M α] : M →+ Additive (Function.End α) where
  toFun := (· +ᵥ ·)
  map_zero' := funext (zero_vadd M)
  map_add' := fun x y => funext (add_vadd x y)

/-- The additive action induced by a hom to `additive (function.End α)`

See note [reducible non-instances]. -/
@[reducible]
def AddAction.ofEndHom [AddMonoidₓ M] (f : M →+ Additive (Function.End α)) : AddAction M α :=
  AddAction.compHom α f

