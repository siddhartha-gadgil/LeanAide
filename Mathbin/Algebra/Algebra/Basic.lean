/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Ring.Aut
import Mathbin.Algebra.Ring.Ulift
import Mathbin.Algebra.Module.Ulift
import Mathbin.LinearAlgebra.Span
import Mathbin.Tactic.Abel

/-!
# Algebras over commutative semirings

In this file we define associative unital `algebra`s over commutative (semi)rings, algebra
homomorphisms `alg_hom`, and algebra equivalences `alg_equiv`.

`subalgebra`s are defined in `algebra.algebra.subalgebra`.

For the category of `R`-algebras, denoted `Algebra R`, see the file
`algebra/category/Algebra/basic.lean`.

See the implementation notes for remarks about non-associative and non-unital algebras.

## Main definitions:

* `algebra R A`: the algebra typeclass.
* `alg_hom R A B`: the type of `R`-algebra morphisms from `A` to `B`.
* `alg_equiv R A B`: the type of `R`-algebra isomorphisms between `A` to `B`.
* `algebra_map R A : R →+* A`: the canonical map from `R` to `A`, as a `ring_hom`. This is the
  preferred spelling of this map.
* `algebra.linear_map R A : R →ₗ[R] A`: the canonical map from `R` to `A`, as a `linear_map`.
* `algebra.of_id R A : R →ₐ[R] A`: the canonical map from `R` to `A`, as n `alg_hom`.
* Instances of `algebra` in this file:
  * `algebra.id`
  * `pi.algebra`
  * `prod.algebra`
  * `algebra_nat`
  * `algebra_int`
  * `algebra_rat`
  * `mul_opposite.algebra`
  * `module.End.algebra`

## Notations

* `A →ₐ[R] B` : `R`-algebra homomorphism from `A` to `B`.
* `A ≃ₐ[R] B` : `R`-algebra equivalence from `A` to `B`.

## Implementation notes

Given a commutative (semi)ring `R`, there are two ways to define an `R`-algebra structure on a
(possibly noncommutative) (semi)ring `A`:
* By endowing `A` with a morphism of rings `R →+* A` denoted `algebra_map R A` which lands in the
  center of `A`.
* By requiring `A` be an `R`-module such that the action associates and commutes with multiplication
  as `r • (a₁ * a₂) = (r • a₁) * a₂ = a₁ * (r • a₂)`.

We define `algebra R A` in a way that subsumes both definitions, by extending `has_smul R A` and
requiring that this scalar action `r • x` must agree with left multiplication by the image of the
structure morphism `algebra_map R A r * x`.

As a result, there are two ways to talk about an `R`-algebra `A` when `A` is a semiring:
1. ```lean
   variables [comm_semiring R] [semiring A]
   variables [algebra R A]
   ```
2. ```lean
   variables [comm_semiring R] [semiring A]
   variables [module R A] [smul_comm_class R A A] [is_scalar_tower R A A]
   ```

The first approach implies the second via typeclass search; so any lemma stated with the second set
of arguments will automatically apply to the first set. Typeclass search does not know that the
second approach implies the first, but this can be shown with:
```lean
example {R A : Type*} [comm_semiring R] [semiring A]
  [module R A] [smul_comm_class R A A] [is_scalar_tower R A A] : algebra R A :=
algebra.of_module smul_mul_assoc mul_smul_comm
```

The advantage of the first approach is that `algebra_map R A` is available, and `alg_hom R A B` and
`subalgebra R A` can be used. For concrete `R` and `A`, `algebra_map R A` is often definitionally
convenient.

The advantage of the second approach is that `comm_semiring R`, `semiring A`, and `module R A` can
all be relaxed independently; for instance, this allows us to:
* Replace `semiring A` with `non_unital_non_assoc_semiring A` in order to describe non-unital and/or
  non-associative algebras.
* Replace `comm_semiring R` and `module R A` with `comm_group R'` and `distrib_mul_action R' A`,
  which when `R' = Rˣ` lets us talk about the "algebra-like" action of `Rˣ` on an
  `R`-algebra `A`.

While `alg_hom R A B` cannot be used in the second approach, `non_unital_alg_hom R A B` still can.

You should always use the first approach when working with associative unital algebras, and mimic
the second approach only when you need to weaken a condition on either `R` or `A`.

-/


universe u v w u₁ v₁

open BigOperators

section Prio

-- ./././Mathport/Syntax/Translate/Basic.lean:304:40: warning: unsupported option extends_priority
-- We set this priority to 0 later in this file
set_option extends_priority 200

/-- An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.

See the implementation notes in this file for discussion of the details of this definition.
-/
/- control priority of
`instance [algebra R A] : has_smul R A` -/
@[nolint has_inhabited_instance]
class Algebra (R : Type u) (A : Type v) [CommSemiringₓ R] [Semiringₓ A] extends HasSmul R A, R →+* A where
  commutes' : ∀ r x, to_fun r * x = x * to_fun r
  smul_def' : ∀ r x, r • x = to_fun r * x

end Prio

/-- Embedding `R →+* A` given by `algebra` structure. -/
def algebraMap (R : Type u) (A : Type v) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] : R →+* A :=
  Algebra.toRingHom

/-- Creating an algebra from a morphism to the center of a semiring. -/
def RingHom.toAlgebra' {R S} [CommSemiringₓ R] [Semiringₓ S] (i : R →+* S) (h : ∀ c x, i c * x = x * i c) :
    Algebra R S where
  smul := fun c x => i c * x
  commutes' := h
  smul_def' := fun c x => rfl
  toRingHom := i

/-- Creating an algebra from a morphism to a commutative semiring. -/
def RingHom.toAlgebra {R S} [CommSemiringₓ R] [CommSemiringₓ S] (i : R →+* S) : Algebra R S :=
  i.toAlgebra' fun _ => mul_comm _

theorem RingHom.algebra_map_to_algebra {R S} [CommSemiringₓ R] [CommSemiringₓ S] (i : R →+* S) :
    @algebraMap R S _ _ i.toAlgebra = i :=
  rfl

namespace Algebra

variable {R : Type u} {S : Type v} {A : Type w} {B : Type _}

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • 1) * x = x * (r • 1) = r • x` for all `r : R` and `x : A`, then `A` is an `algebra`
over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule' [CommSemiringₓ R] [Semiringₓ A] [Module R A] (h₁ : ∀ (r : R) (x : A), r • 1 * x = r • x)
    (h₂ : ∀ (r : R) (x : A), x * r • 1 = r • x) : Algebra R A where
  toFun := fun r => r • 1
  map_one' := one_smul _ _
  map_mul' := fun r₁ r₂ => by
    rw [h₁, mul_smul]
  map_zero' := zero_smul _ _
  map_add' := fun r₁ r₂ => add_smul r₁ r₂ 1
  commutes' := fun r x => by
    simp only [← h₁, ← h₂]
  smul_def' := fun r x => by
    simp only [← h₁]

/-- Let `R` be a commutative semiring, let `A` be a semiring with a `module R` structure.
If `(r • x) * y = x * (r • y) = r • (x * y)` for all `r : R` and `x y : A`, then `A`
is an `algebra` over `R`.

See note [reducible non-instances]. -/
@[reducible]
def ofModule [CommSemiringₓ R] [Semiringₓ A] [Module R A] (h₁ : ∀ (r : R) (x y : A), r • x * y = r • (x * y))
    (h₂ : ∀ (r : R) (x y : A), x * r • y = r • (x * y)) : Algebra R A :=
  ofModule'
    (fun r x => by
      rw [h₁, one_mulₓ])
    fun r x => by
    rw [h₂, mul_oneₓ]

section Semiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ S]

variable [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

/-- We keep this lemma private because it picks up the `algebra.to_has_smul` instance
which we set to priority 0 shortly. See `smul_def` below for the public version. -/
private theorem smul_def'' (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x

/-- To prove two algebra structures on a fixed `[comm_semiring R] [semiring A]` agree,
it suffices to check the `algebra_map`s agree.
-/
-- We'll later use this to show `algebra ℤ M` is a subsingleton.
@[ext]
theorem algebra_ext {R : Type _} [CommSemiringₓ R] {A : Type _} [Semiringₓ A] (P Q : Algebra R A)
    (w :
      ∀ r : R,
        by
          have := P
          exact algebraMap R A r = by
          have := Q
          exact algebraMap R A r) :
    P = Q := by
  rcases P with ⟨⟨P⟩⟩
  rcases Q with ⟨⟨Q⟩⟩
  congr
  · funext r a
    replace w := congr_arg (fun s => s * a) (w r)
    simp only [smul_def''] at w
    apply w
    
  · ext r
    exact w r
    
  · apply proof_irrel_heq
    
  · apply proof_irrel_heq
    

-- see Note [lower instance priority]
instance (priority := 200) toModule : Module R A where
  one_smul := by
    simp [← smul_def'']
  mul_smul := by
    simp [← smul_def'', ← mul_assoc]
  smul_add := by
    simp [← smul_def'', ← mul_addₓ]
  smul_zero := by
    simp [← smul_def'']
  add_smul := by
    simp [← smul_def'', ← add_mulₓ]
  zero_smul := by
    simp [← smul_def'']

-- From now on, we don't want to use the following instance anymore.
-- Unfortunately, leaving it in place causes deterministic timeouts later in mathlib.
attribute [instance] Algebra.toHasSmul

theorem smul_def (r : R) (x : A) : r • x = algebraMap R A r * x :=
  Algebra.smul_def' r x

theorem algebra_map_eq_smul_one (r : R) : algebraMap R A r = r • 1 :=
  calc
    algebraMap R A r = algebraMap R A r * 1 := (mul_oneₓ _).symm
    _ = r • 1 := (Algebra.smul_def r 1).symm
    

theorem algebra_map_eq_smul_one' : ⇑(algebraMap R A) = fun r => r • (1 : A) :=
  funext algebra_map_eq_smul_one

/-- `mul_comm` for `algebra`s when one element is from the base ring. -/
theorem commutes (r : R) (x : A) : algebraMap R A r * x = x * algebraMap R A r :=
  Algebra.commutes' r x

/-- `mul_left_comm` for `algebra`s when one element is from the base ring. -/
theorem left_comm (x : A) (r : R) (y : A) : x * (algebraMap R A r * y) = algebraMap R A r * (x * y) := by
  rw [← mul_assoc, ← commutes, mul_assoc]

/-- `mul_right_comm` for `algebra`s when one element is from the base ring. -/
theorem right_comm (x : A) (r : R) (y : A) : x * algebraMap R A r * y = x * y * algebraMap R A r := by
  rw [mul_assoc, commutes, ← mul_assoc]

instance _root_.is_scalar_tower.right : IsScalarTower R A A :=
  ⟨fun x y z => by
    rw [smul_eq_mul, smul_eq_mul, smul_def, smul_def, mul_assoc]⟩

/-- This is just a special case of the global `mul_smul_comm` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem mul_smul_comm (s : R) (x y : A) : x * s • y = s • (x * y) := by
  -- TODO: set up `is_scalar_tower.smul_comm_class` earlier so that we can actually prove this using
  -- `mul_smul_comm s x y`.
  rw [smul_def, smul_def, left_comm]

/-- This is just a special case of the global `smul_mul_assoc` lemma that requires less typeclass
search (and was here first). -/
@[simp]
protected theorem smul_mul_assoc (r : R) (x y : A) : r • x * y = r • (x * y) :=
  smul_mul_assoc r x y

section

variable {r : R} {a : A}

@[simp]
theorem bit0_smul_one : bit0 r • (1 : A) = bit0 (r • (1 : A)) := by
  simp [← bit0, ← add_smul]

theorem bit0_smul_one' : bit0 r • (1 : A) = r • 2 := by
  simp [← bit0, ← add_smul, ← smul_add]

@[simp]
theorem bit0_smul_bit0 : bit0 r • bit0 a = r • bit0 (bit0 a) := by
  simp [← bit0, ← add_smul, ← smul_add]

@[simp]
theorem bit0_smul_bit1 : bit0 r • bit1 a = r • bit0 (bit1 a) := by
  simp [← bit0, ← add_smul, ← smul_add]

@[simp]
theorem bit1_smul_one : bit1 r • (1 : A) = bit1 (r • (1 : A)) := by
  simp [← bit1, ← add_smul]

theorem bit1_smul_one' : bit1 r • (1 : A) = r • 2 + 1 := by
  simp [← bit1, ← bit0, ← add_smul, ← smul_add]

@[simp]
theorem bit1_smul_bit0 : bit1 r • bit0 a = r • bit0 (bit0 a) + bit0 a := by
  simp [← bit1, ← add_smul, ← smul_add]

@[simp]
theorem bit1_smul_bit1 : bit1 r • bit1 a = r • bit0 (bit1 a) + bit1 a := by
  simp only [← bit0, ← bit1, ← add_smul, ← smul_add, ← one_smul]
  abel

end

variable (R A)

/-- The canonical ring homomorphism `algebra_map R A : R →* A` for any `R`-algebra `A`,
packaged as an `R`-linear map.
-/
protected def linearMap : R →ₗ[R] A :=
  { algebraMap R A with
    map_smul' := fun x y => by
      simp [← Algebra.smul_def] }

@[simp]
theorem linear_map_apply (r : R) : Algebra.linearMap R A r = algebraMap R A r :=
  rfl

theorem coe_linear_map : ⇑(Algebra.linearMap R A) = algebraMap R A :=
  rfl

instance id : Algebra R R :=
  (RingHom.id R).toAlgebra

variable {R A}

namespace id

@[simp]
theorem map_eq_id : algebraMap R R = RingHom.id _ :=
  rfl

theorem map_eq_self (x : R) : algebraMap R R x = x :=
  rfl

@[simp]
theorem smul_eq_mul (x y : R) : x • y = x * y :=
  rfl

end id

section PUnit

instance _root_.punit.algebra : Algebra R PUnit where
  toFun := fun x => PUnit.unit
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  commutes' := fun _ _ => rfl
  smul_def' := fun _ _ => rfl

@[simp]
theorem algebra_map_punit (r : R) : algebraMap R PUnit r = PUnit.unit :=
  rfl

end PUnit

section ULift

instance _root_.ulift.algebra : Algebra R (ULift A) :=
  { ULift.module', (ULift.ringEquiv : ULift A ≃+* A).symm.toRingHom.comp (algebraMap R A) with
    toFun := fun r => ULift.up (algebraMap R A r),
    commutes' := fun r x => ULift.down_injective <| Algebra.commutes r x.down,
    smul_def' := fun r x => ULift.down_injective <| Algebra.smul_def' r x.down }

theorem _root_.ulift.algebra_map_eq (r : R) : algebraMap R (ULift A) r = ULift.up (algebraMap R A r) :=
  rfl

@[simp]
theorem _root_.ulift.down_algebra_map (r : R) : (algebraMap R (ULift A) r).down = algebraMap R A r :=
  rfl

end ULift

section Prod

variable (R A B)

instance _root_.prod.algebra : Algebra R (A × B) :=
  { Prod.module, RingHom.prod (algebraMap R A) (algebraMap R B) with
    commutes' := by
      rintro r ⟨a, b⟩
      dsimp'
      rw [commutes r a, commutes r b],
    smul_def' := by
      rintro r ⟨a, b⟩
      dsimp'
      rw [smul_def r a, smul_def r b] }

variable {R A B}

@[simp]
theorem algebra_map_prod_apply (r : R) : algebraMap R (A × B) r = (algebraMap R A r, algebraMap R B r) :=
  rfl

end Prod

/-- Algebra over a subsemiring. This builds upon `subsemiring.module`. -/
instance ofSubsemiring (S : Subsemiring R) : Algebra S A :=
  { (algebraMap R A).comp S.Subtype with smul := (· • ·), commutes' := fun r x => Algebra.commutes r x,
    smul_def' := fun r x => Algebra.smul_def r x }

theorem algebra_map_of_subsemiring (S : Subsemiring R) : (algebraMap S R : S →+* R) = Subsemiring.subtype S :=
  rfl

theorem coe_algebra_map_of_subsemiring (S : Subsemiring R) : (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebra_map_of_subsemiring_apply (S : Subsemiring R) (x : S) : algebraMap S R x = x :=
  rfl

/-- Algebra over a subring. This builds upon `subring.module`. -/
instance ofSubring {R A : Type _} [CommRingₓ R] [Ringₓ A] [Algebra R A] (S : Subring R) : Algebra S A :=
  { Algebra.ofSubsemiring S.toSubsemiring, (algebraMap R A).comp S.Subtype with smul := (· • ·) }

theorem algebra_map_of_subring {R : Type _} [CommRingₓ R] (S : Subring R) :
    (algebraMap S R : S →+* R) = Subring.subtype S :=
  rfl

theorem coe_algebra_map_of_subring {R : Type _} [CommRingₓ R] (S : Subring R) :
    (algebraMap S R : S → R) = Subtype.val :=
  rfl

theorem algebra_map_of_subring_apply {R : Type _} [CommRingₓ R] (S : Subring R) (x : S) : algebraMap S R x = x :=
  rfl

/-- Explicit characterization of the submonoid map in the case of an algebra.
`S` is made explicit to help with type inference -/
def algebraMapSubmonoid (S : Type _) [Semiringₓ S] [Algebra R S] (M : Submonoid R) : Submonoid S :=
  Submonoid.map (algebraMap R S : R →* S) M

theorem mem_algebra_map_submonoid_of_mem {S : Type _} [Semiringₓ S] [Algebra R S] {M : Submonoid R} (x : M) :
    algebraMap R S x ∈ algebraMapSubmonoid S M :=
  Set.mem_image_of_mem (algebraMap R S) x.2

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R]

theorem mul_sub_algebra_map_commutes [Ringₓ A] [Algebra R A] (x : A) (r : R) :
    x * (x - algebraMap R A r) = (x - algebraMap R A r) * x := by
  rw [mul_sub, ← commutes, sub_mul]

theorem mul_sub_algebra_map_pow_commutes [Ringₓ A] [Algebra R A] (x : A) (r : R) (n : ℕ) :
    x * (x - algebraMap R A r) ^ n = (x - algebraMap R A r) ^ n * x := by
  induction' n with n ih
  · simp
    
  · rw [pow_succₓ, ← mul_assoc, mul_sub_algebra_map_commutes, mul_assoc, ih, ← mul_assoc]
    

end CommSemiringₓ

section Ringₓ

variable [CommRingₓ R]

variable (R)

/-- A `semiring` that is an `algebra` over a commutative ring carries a natural `ring` structure.
See note [reducible non-instances]. -/
@[reducible]
def semiringToRing [Semiringₓ A] [Algebra R A] : Ringₓ A :=
  { Module.addCommMonoidToAddCommGroup R, (inferInstance : Semiringₓ A) with }

end Ringₓ

end Algebra

namespace MulOpposite

variable {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

instance : Algebra R Aᵐᵒᵖ :=
  { MulOpposite.hasSmul A R with toRingHom := (algebraMap R A).toOpposite fun x y => Algebra.commutes _ _,
    smul_def' := fun c x =>
      unop_injective <| by
        dsimp'
        simp only [← op_mul, ← Algebra.smul_def, ← Algebra.commutes, ← op_unop],
    commutes' := fun r =>
      MulOpposite.rec fun x => by
        dsimp' <;> simp only [op_mul, ← Algebra.commutes] }

@[simp]
theorem algebra_map_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) :=
  rfl

end MulOpposite

namespace Module

variable (R : Type u) (M : Type v) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M]

instance : Algebra R (Module.End R M) :=
  Algebra.ofModule smul_mul_assoc fun r f g => (smul_comm r f g).symm

theorem algebra_map_End_eq_smul_id (a : R) : (algebraMap R (End R M)) a = a • LinearMap.id :=
  rfl

@[simp]
theorem algebra_map_End_apply (a : R) (m : M) : (algebraMap R (End R M)) a m = a • m :=
  rfl

@[simp]
theorem ker_algebra_map_End (K : Type u) (V : Type v) [Field K] [AddCommGroupₓ V] [Module K V] (a : K) (ha : a ≠ 0) :
    ((algebraMap K (End K V)) a).ker = ⊥ :=
  LinearMap.ker_smul _ _ ha

end Module

/-- Defining the homomorphism in the category R-Alg. -/
@[nolint has_inhabited_instance]
structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
  [Algebra R B] extends RingHom A B where
  commutes' : ∀ r : R, to_fun (algebraMap R A r) = algebraMap R B r

run_cmd
  tactic.add_doc_string `alg_hom.to_ring_hom "Reinterpret an `alg_hom` as a `ring_hom`"

-- mathport name: «expr →ₐ »
infixr:25 " →ₐ " => AlgHom _

-- mathport name: «expr →ₐ[ ] »
notation:25 A " →ₐ[" R "] " B => AlgHom R A B

/-- `alg_hom_class F R A B` asserts `F` is a type of bundled algebra homomorphisms
from `A` to `B`.  -/
class AlgHomClass (F : Type _) (R : outParam (Type _)) (A : outParam (Type _)) (B : outParam (Type _)) [CommSemiringₓ R]
  [Semiringₓ A] [Semiringₓ B] [Algebra R A] [Algebra R B] extends RingHomClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] AlgHomClass.toRingHomClass

attribute [simp] AlgHomClass.commutes

namespace AlgHomClass

variable {R : Type _} {A : Type _} {B : Type _} [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
  [Algebra R B]

-- see Note [lower instance priority]
instance (priority := 100) {F : Type _} [AlgHomClass F R A B] : LinearMapClass F R A B :=
  { ‹AlgHomClass F R A B› with
    map_smulₛₗ := fun f r x => by
      simp only [← Algebra.smul_def, ← map_mul, ← commutes, ← RingHom.id_apply] }

end AlgHomClass

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {C : Type u₁} {D : Type v₁}

section Semiringₓ

variable [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Semiringₓ C] [Semiringₓ D]

variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

instance : CoeFun (A →ₐ[R] B) fun _ => A → B :=
  ⟨AlgHom.toFun⟩

initialize_simps_projections AlgHom (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : A →ₐ[R] B) : f.toFun = f :=
  rfl

instance : AlgHomClass (A →ₐ[R] B) R A B where
  coe := toFun
  coe_injective' := fun f g h => by
    cases f
    cases g
    congr
  map_add := map_add'
  map_zero := map_zero'
  map_mul := map_mul'
  map_one := map_one'
  commutes := fun f => f.commutes'

instance coeRingHom : Coe (A →ₐ[R] B) (A →+* B) :=
  ⟨AlgHom.toRingHom⟩

instance coeMonoidHom : Coe (A →ₐ[R] B) (A →* B) :=
  ⟨fun f => ↑(f : A →+* B)⟩

instance coeAddMonoidHom : Coe (A →ₐ[R] B) (A →+ B) :=
  ⟨fun f => ↑(f : A →+* B)⟩

@[simp, norm_cast]
theorem coe_mk {f : A → B} (h₁ h₂ h₃ h₄ h₅) : ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  rfl

-- make the coercion the simp-normal form
@[simp]
theorem to_ring_hom_eq_coe (f : A →ₐ[R] B) : f.toRingHom = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_ring_hom (f : A →ₐ[R] B) : ⇑(f : A →+* B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →* B) = f :=
  rfl

@[simp, norm_cast]
theorem coe_to_add_monoid_hom (f : A →ₐ[R] B) : ⇑(f : A →+ B) = f :=
  rfl

variable (φ : A →ₐ[R] B)

theorem coe_fn_injective : @Function.Injective (A →ₐ[R] B) (A → B) coeFn :=
  FunLike.coe_injective

theorem coe_fn_inj {φ₁ φ₂ : A →ₐ[R] B} : (φ₁ : A → B) = φ₂ ↔ φ₁ = φ₂ :=
  FunLike.coe_fn_eq

theorem coe_ring_hom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+* B) := fun φ₁ φ₂ H =>
  coe_fn_injective <| show ((φ₁ : A →+* B) : A → B) = ((φ₂ : A →+* B) : A → B) from congr_arg _ H

theorem coe_monoid_hom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →* B) :=
  RingHom.coe_monoid_hom_injective.comp coe_ring_hom_injective

theorem coe_add_monoid_hom_injective : Function.Injective (coe : (A →ₐ[R] B) → A →+ B) :=
  RingHom.coe_add_monoid_hom_injective.comp coe_ring_hom_injective

protected theorem congr_fun {φ₁ φ₂ : A →ₐ[R] B} (H : φ₁ = φ₂) (x : A) : φ₁ x = φ₂ x :=
  FunLike.congr_fun H x

protected theorem congr_arg (φ : A →ₐ[R] B) {x y : A} (h : x = y) : φ x = φ y :=
  FunLike.congr_arg φ h

@[ext]
theorem ext {φ₁ φ₂ : A →ₐ[R] B} (H : ∀ x, φ₁ x = φ₂ x) : φ₁ = φ₂ :=
  FunLike.ext _ _ H

theorem ext_iff {φ₁ φ₂ : A →ₐ[R] B} : φ₁ = φ₂ ↔ ∀ x, φ₁ x = φ₂ x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe {f : A →ₐ[R] B} (h₁ h₂ h₃ h₄ h₅) : (⟨f, h₁, h₂, h₃, h₄, h₅⟩ : A →ₐ[R] B) = f :=
  ext fun _ => rfl

@[simp]
theorem commutes (r : R) : φ (algebraMap R A r) = algebraMap R B r :=
  φ.commutes' r

theorem comp_algebra_map : (φ : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext <| φ.commutes

protected theorem map_add (r s : A) : φ (r + s) = φ r + φ s :=
  map_add _ _ _

protected theorem map_zero : φ 0 = 0 :=
  map_zero _

protected theorem map_mul (x y) : φ (x * y) = φ x * φ y :=
  map_mul _ _ _

protected theorem map_one : φ 1 = 1 :=
  map_one _

protected theorem map_pow (x : A) (n : ℕ) : φ (x ^ n) = φ x ^ n :=
  map_pow _ _ _

@[simp]
protected theorem map_smul (r : R) (x : A) : φ (r • x) = r • φ x :=
  map_smul _ _ _

protected theorem map_sum {ι : Type _} (f : ι → A) (s : Finset ι) : φ (∑ x in s, f x) = ∑ x in s, φ (f x) :=
  map_sum _ _ _

protected theorem map_finsupp_sum {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Sum g) = f.Sum fun i a => φ (g i a) :=
  map_finsupp_sum _ _ _

protected theorem map_bit0 (x) : φ (bit0 x) = bit0 (φ x) :=
  map_bit0 _ _

protected theorem map_bit1 (x) : φ (bit1 x) = bit1 (φ x) :=
  map_bit1 _ _

/-- If a `ring_hom` is `R`-linear, then it is an `alg_hom`. -/
def mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : A →ₐ[R] B :=
  { f with toFun := f,
    commutes' := fun c => by
      simp only [← Algebra.algebra_map_eq_smul_one, ← h, ← f.map_one] }

@[simp]
theorem coe_mk' (f : A →+* B) (h : ∀ (c : R) (x), f (c • x) = c • f x) : ⇑(mk' f h) = f :=
  rfl

section

variable (R A)

/-- Identity map as an `alg_hom`. -/
protected def id : A →ₐ[R] A :=
  { RingHom.id A with commutes' := fun _ => rfl }

@[simp]
theorem coe_id : ⇑(AlgHom.id R A) = id :=
  rfl

@[simp]
theorem id_to_ring_hom : (AlgHom.id R A : A →+* A) = RingHom.id _ :=
  rfl

end

theorem id_apply (p : A) : AlgHom.id R A p = p :=
  rfl

/-- Composition of algebra homeomorphisms. -/
def comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : A →ₐ[R] C :=
  { φ₁.toRingHom.comp ↑φ₂ with
    commutes' := fun r : R => by
      rw [← φ₁.commutes, ← φ₂.commutes] <;> rfl }

@[simp]
theorem coe_comp (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂) = φ₁ ∘ φ₂ :=
  rfl

theorem comp_apply (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) (p : A) : φ₁.comp φ₂ p = φ₁ (φ₂ p) :=
  rfl

theorem comp_to_ring_hom (φ₁ : B →ₐ[R] C) (φ₂ : A →ₐ[R] B) : ⇑(φ₁.comp φ₂ : A →+* C) = (φ₁ : B →+* C).comp ↑φ₂ :=
  rfl

@[simp]
theorem comp_id : φ.comp (AlgHom.id R A) = φ :=
  ext fun x => rfl

@[simp]
theorem id_comp : (AlgHom.id R B).comp φ = φ :=
  ext fun x => rfl

theorem comp_assoc (φ₁ : C →ₐ[R] D) (φ₂ : B →ₐ[R] C) (φ₃ : A →ₐ[R] B) : (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) :=
  ext fun x => rfl

/-- R-Alg ⥤ R-Mod -/
def toLinearMap : A →ₗ[R] B where
  toFun := φ
  map_add' := map_add _
  map_smul' := map_smul _

@[simp]
theorem to_linear_map_apply (p : A) : φ.toLinearMap p = φ p :=
  rfl

theorem to_linear_map_injective : Function.Injective (toLinearMap : _ → A →ₗ[R] B) := fun φ₁ φ₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem comp_to_linear_map (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
theorem to_linear_map_id : toLinearMap (AlgHom.id R A) = LinearMap.id :=
  LinearMap.ext fun _ => rfl

/-- Promote a `linear_map` to an `alg_hom` by supplying proofs about the behavior on `1` and `*`. -/
@[simps]
def ofLinearMap (f : A →ₗ[R] B) (map_one : f 1 = 1) (map_mul : ∀ x y, f (x * y) = f x * f y) : A →ₐ[R] B :=
  { f.toAddMonoidHom with toFun := f, map_one' := map_one, map_mul' := map_mul,
    commutes' := fun c => by
      simp only [← Algebra.algebra_map_eq_smul_one, ← f.map_smul, ← map_one] }

@[simp]
theorem of_linear_map_to_linear_map (map_one) (map_mul) : ofLinearMap φ.toLinearMap map_one map_mul = φ := by
  ext
  rfl

@[simp]
theorem to_linear_map_of_linear_map (f : A →ₗ[R] B) (map_one) (map_mul) :
    toLinearMap (ofLinearMap f map_one map_mul) = f := by
  ext
  rfl

@[simp]
theorem of_linear_map_id (map_one) (map_mul) : ofLinearMap LinearMap.id map_one map_mul = AlgHom.id R A :=
  ext fun _ => rfl

theorem map_smul_of_tower {R'} [HasSmul R' A] [HasSmul R' B] [LinearMap.CompatibleSmul A B R' R] (r : R') (x : A) :
    φ (r • x) = r • φ x :=
  φ.toLinearMap.map_smul_of_tower r x

theorem map_list_prod (s : List A) : φ s.Prod = (s.map φ).Prod :=
  φ.toRingHom.map_list_prod s

section Prod

/-- First projection as `alg_hom`. -/
def fst : A × B →ₐ[R] A :=
  { RingHom.fst A B with commutes' := fun r => rfl }

/-- Second projection as `alg_hom`. -/
def snd : A × B →ₐ[R] B :=
  { RingHom.snd A B with commutes' := fun r => rfl }

end Prod

theorem algebra_map_eq_apply (f : A →ₐ[R] B) {y : R} {x : A} (h : algebraMap R A y = x) : algebraMap R B y = f x :=
  h ▸ (f.commutes _).symm

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A] [CommSemiringₓ B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_multiset_prod (s : Multiset A) : φ s.Prod = (s.map φ).Prod :=
  map_multiset_prod _ _

protected theorem map_prod {ι : Type _} (f : ι → A) (s : Finset ι) : φ (∏ x in s, f x) = ∏ x in s, φ (f x) :=
  map_prod _ _ _

protected theorem map_finsupp_prod {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A) :
    φ (f.Prod g) = f.Prod fun i a => φ (g i a) :=
  map_finsupp_prod _ _ _

end CommSemiringₓ

section Ringₓ

variable [CommSemiringₓ R] [Ringₓ A] [Ringₓ B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

protected theorem map_neg (x) : φ (-x) = -φ x :=
  map_neg _ _

protected theorem map_sub (x y) : φ (x - y) = φ x - φ y :=
  map_sub _ _ _

@[simp]
theorem map_int_cast (n : ℤ) : φ n = n :=
  φ.toRingHom.map_int_cast n

end Ringₓ

section DivisionRing

variable [CommSemiringₓ R] [DivisionRing A] [DivisionRing B]

variable [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)

@[simp]
theorem map_inv (x) : φ x⁻¹ = (φ x)⁻¹ :=
  φ.toRingHom.map_inv x

@[simp]
theorem map_div (x y) : φ (x / y) = φ x / φ y :=
  φ.toRingHom.map_div x y

end DivisionRing

end AlgHom

@[simp]
theorem Rat.smul_one_eq_coe {A : Type _} [DivisionRing A] [Algebra ℚ A] (m : ℚ) : m • (1 : A) = ↑m := by
  rw [Algebra.smul_def, mul_oneₓ, RingHom.eq_rat_cast]

/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
  [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where
  commutes' : ∀ r : R, to_fun (algebraMap R A r) = algebraMap R B r

attribute [nolint doc_blame] AlgEquiv.toRingEquiv

attribute [nolint doc_blame] AlgEquiv.toEquiv

attribute [nolint doc_blame] AlgEquiv.toAddEquiv

attribute [nolint doc_blame] AlgEquiv.toMulEquiv

-- mathport name: «expr ≃ₐ[ ] »
notation:50 A " ≃ₐ[" R "] " A' => AlgEquiv R A A'

/-- `alg_equiv_class F R A B` states that `F` is a type of algebra structure preserving
  equivalences. You should extend this class when you extend `alg_equiv`. -/
class AlgEquivClass (F : Type _) (R A B : outParam (Type _)) [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
  [Algebra R B] extends RingEquivClass F A B where
  commutes : ∀ (f : F) (r : R), f (algebraMap R A r) = algebraMap R B r

-- `R` becomes a metavariable but that's fine because it's an `out_param`
attribute [nolint dangerous_instance] AlgEquivClass.toRingEquivClass

namespace AlgEquivClass

-- See note [lower instance priority]
instance (priority := 100) toAlgHomClass (F R A B : Type _) [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B] [Algebra R A]
    [Algebra R B] [h : AlgEquivClass F R A B] : AlgHomClass F R A B :=
  { h with coe := coeFn, coe_injective' := FunLike.coe_injective, map_zero := map_zero, map_one := map_one }

end AlgEquivClass

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w} {A₃ : Type u₁}

section Semiringₓ

variable [CommSemiringₓ R] [Semiringₓ A₁] [Semiringₓ A₂] [Semiringₓ A₃]

variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable (e : A₁ ≃ₐ[R] A₂)

instance : AlgEquivClass (A₁ ≃ₐ[R] A₂) R A₁ A₂ where
  coe := toFun
  inv := invFun
  coe_injective' := fun f g h₁ h₂ => by
    cases f
    cases g
    congr
  map_add := map_add'
  map_mul := map_mul'
  commutes := commutes'
  left_inv := left_inv
  right_inv := right_inv

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : CoeFun (A₁ ≃ₐ[R] A₂) fun _ => A₁ → A₂ :=
  ⟨AlgEquiv.toFun⟩

@[ext]
theorem ext {f g : A₁ ≃ₐ[R] A₂} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

protected theorem congr_arg {f : A₁ ≃ₐ[R] A₂} {x x' : A₁} : x = x' → f x = f x' :=
  FunLike.congr_arg f

protected theorem congr_fun {f g : A₁ ≃ₐ[R] A₂} (h : f = g) (x : A₁) : f x = g x :=
  FunLike.congr_fun h x

protected theorem ext_iff {f g : A₁ ≃ₐ[R] A₂} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

theorem coe_fun_injective : @Function.Injective (A₁ ≃ₐ[R] A₂) (A₁ → A₂) fun e => (e : A₁ → A₂) :=
  FunLike.coe_injective

instance hasCoeToRingEquiv : Coe (A₁ ≃ₐ[R] A₂) (A₁ ≃+* A₂) :=
  ⟨AlgEquiv.toRingEquiv⟩

@[simp]
theorem coe_mk {to_fun inv_fun left_inv right_inv map_mul map_add commutes} :
    ⇑(⟨to_fun, inv_fun, left_inv, right_inv, map_mul, map_add, commutes⟩ : A₁ ≃ₐ[R] A₂) = to_fun :=
  rfl

@[simp]
theorem mk_coe (e : A₁ ≃ₐ[R] A₂) (e' h₁ h₂ h₃ h₄ h₅) : (⟨e, e', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂) = e :=
  ext fun _ => rfl

@[simp]
theorem to_fun_eq_coe (e : A₁ ≃ₐ[R] A₂) : e.toFun = e :=
  rfl

@[simp]
theorem to_equiv_eq_coe : e.toEquiv = e :=
  rfl

@[simp]
theorem to_ring_equiv_eq_coe : e.toRingEquiv = e :=
  rfl

@[simp, norm_cast]
theorem coe_ring_equiv : ((e : A₁ ≃+* A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_ring_equiv' : (e.toRingEquiv : A₁ → A₂) = e :=
  rfl

theorem coe_ring_equiv_injective : Function.Injective (coe : (A₁ ≃ₐ[R] A₂) → A₁ ≃+* A₂) := fun e₁ e₂ h =>
  ext <| RingEquiv.congr_fun h

protected theorem map_add : ∀ x y, e (x + y) = e x + e y :=
  map_add e

protected theorem map_zero : e 0 = 0 :=
  map_zero e

protected theorem map_mul : ∀ x y, e (x * y) = e x * e y :=
  map_mul e

protected theorem map_one : e 1 = 1 :=
  map_one e

@[simp]
theorem commutes : ∀ r : R, e (algebraMap R A₁ r) = algebraMap R A₂ r :=
  e.commutes'

@[simp]
theorem map_smul (r : R) (x : A₁) : e (r • x) = r • e x := by
  simp only [← Algebra.smul_def, ← map_mul, ← commutes]

theorem map_sum {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∑ x in s, f x) = ∑ x in s, e (f x) :=
  e.toAddEquiv.map_sum f s

theorem map_finsupp_sum {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.Sum g) = f.Sum fun i b => e (g i b) :=
  e.map_sum _ _

/-- Interpret an algebra equivalence as an algebra homomorphism.

This definition is included for symmetry with the other `to_*_hom` projections.
The `simp` normal form is to use the coercion of the `has_coe_to_alg_hom` instance. -/
def toAlgHom : A₁ →ₐ[R] A₂ :=
  { e with map_one' := e.map_one, map_zero' := e.map_zero }

instance hasCoeToAlgHom : Coe (A₁ ≃ₐ[R] A₂) (A₁ →ₐ[R] A₂) :=
  ⟨toAlgHom⟩

@[simp]
theorem to_alg_hom_eq_coe : e.toAlgHom = e :=
  rfl

@[simp, norm_cast]
theorem coe_alg_hom : ((e : A₁ →ₐ[R] A₂) : A₁ → A₂) = e :=
  rfl

theorem coe_alg_hom_injective : Function.Injective (coe : (A₁ ≃ₐ[R] A₂) → A₁ →ₐ[R] A₂) := fun e₁ e₂ h =>
  ext <| AlgHom.congr_fun h

/-- The two paths coercion can take to a `ring_hom` are equivalent -/
theorem coe_ring_hom_commutes : ((e : A₁ →ₐ[R] A₂) : A₁ →+* A₂) = ((e : A₁ ≃+* A₂) : A₁ →+* A₂) :=
  rfl

protected theorem map_pow : ∀ (x : A₁) (n : ℕ), e (x ^ n) = e x ^ n :=
  map_pow _

protected theorem injective : Function.Injective e :=
  EquivLike.injective e

protected theorem surjective : Function.Surjective e :=
  EquivLike.surjective e

protected theorem bijective : Function.Bijective e :=
  EquivLike.bijective e

/-- Algebra equivalences are reflexive. -/
@[refl]
def refl : A₁ ≃ₐ[R] A₁ :=
  { (1 : A₁ ≃+* A₁) with commutes' := fun r => rfl }

instance : Inhabited (A₁ ≃ₐ[R] A₁) :=
  ⟨refl⟩

@[simp]
theorem refl_to_alg_hom : ↑(refl : A₁ ≃ₐ[R] A₁) = AlgHom.id R A₁ :=
  rfl

@[simp]
theorem coe_refl : ⇑(refl : A₁ ≃ₐ[R] A₁) = id :=
  rfl

/-- Algebra equivalences are symmetric. -/
@[symm]
def symm (e : A₁ ≃ₐ[R] A₂) : A₂ ≃ₐ[R] A₁ :=
  { e.toRingEquiv.symm with
    commutes' := fun r => by
      rw [← e.to_ring_equiv.symm_apply_apply (algebraMap R A₁ r)]
      congr
      change _ = e _
      rw [e.commutes] }

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : A₁ ≃ₐ[R] A₂) : A₂ → A₁ :=
  e.symm

initialize_simps_projections AlgEquiv (toFun → apply, invFun → symmApply)

@[simp]
theorem inv_fun_eq_symm {e : A₁ ≃ₐ[R] A₂} : e.invFun = e.symm :=
  rfl

@[simp]
theorem symm_symm (e : A₁ ≃ₐ[R] A₂) : e.symm.symm = e := by
  ext
  rfl

theorem symm_bijective : Function.Bijective (symm : (A₁ ≃ₐ[R] A₂) → A₂ ≃ₐ[R] A₁) :=
  Equivₓ.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp]
theorem mk_coe' (e : A₁ ≃ₐ[R] A₂) (f h₁ h₂ h₃ h₄ h₅) : (⟨f, e, h₁, h₂, h₃, h₄, h₅⟩ : A₂ ≃ₐ[R] A₁) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl

@[simp]
theorem symm_mk (f f') (h₁ h₂ h₃ h₄ h₅) :
    (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm =
      { (⟨f, f', h₁, h₂, h₃, h₄, h₅⟩ : A₁ ≃ₐ[R] A₂).symm with toFun := f', invFun := f } :=
  rfl

@[simp]
theorem refl_symm : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).symm = AlgEquiv.refl :=
  rfl

/-- Algebra equivalences are transitive. -/
@[trans]
def trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : A₁ ≃ₐ[R] A₃ :=
  { e₁.toRingEquiv.trans e₂.toRingEquiv with
    commutes' := fun r =>
      show e₂.toFun (e₁.toFun _) = _ by
        rw [e₁.commutes', e₂.commutes'] }

@[simp]
theorem apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₃) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) (x : A₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
theorem comp_symm (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp (e : A₁ →ₐ[R] A₂) ↑e.symm = AlgHom.id R A₂ := by
  ext
  simp

@[simp]
theorem symm_comp (e : A₁ ≃ₐ[R] A₂) : AlgHom.comp ↑e.symm (e : A₁ →ₐ[R] A₂) = AlgHom.id R A₁ := by
  ext
  simp

theorem left_inverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.LeftInverse e.symm e :=
  e.left_inv

theorem right_inverse_symm (e : A₁ ≃ₐ[R] A₂) : Function.RightInverse e.symm e :=
  e.right_inv

/-- If `A₁` is equivalent to `A₁'` and `A₂` is equivalent to `A₂'`, then the type of maps
`A₁ →ₐ[R] A₂` is equivalent to the type of maps `A₁' →ₐ[R] A₂'`. -/
def arrowCongr {A₁' A₂' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Algebra R A₁'] [Algebra R A₂'] (e₁ : A₁ ≃ₐ[R] A₁')
    (e₂ : A₂ ≃ₐ[R] A₂') : (A₁ →ₐ[R] A₂) ≃ (A₁' →ₐ[R] A₂') where
  toFun := fun f => (e₂.toAlgHom.comp f).comp e₁.symm.toAlgHom
  invFun := fun f => (e₂.symm.toAlgHom.comp f).comp e₁.toAlgHom
  left_inv := fun f => by
    simp only [← AlgHom.comp_assoc, ← to_alg_hom_eq_coe, ← symm_comp]
    simp only [AlgHom.comp_assoc, ← symm_comp, ← AlgHom.id_comp, ← AlgHom.comp_id]
  right_inv := fun f => by
    simp only [← AlgHom.comp_assoc, ← to_alg_hom_eq_coe, ← comp_symm]
    simp only [AlgHom.comp_assoc, ← comp_symm, ← AlgHom.id_comp, ← AlgHom.comp_id]

theorem arrow_congr_comp {A₁' A₂' A₃' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Semiringₓ A₃'] [Algebra R A₁']
    [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') (e₃ : A₃ ≃ₐ[R] A₃') (f : A₁ →ₐ[R] A₂)
    (g : A₂ →ₐ[R] A₃) : arrowCongr e₁ e₃ (g.comp f) = (arrowCongr e₂ e₃ g).comp (arrowCongr e₁ e₂ f) := by
  ext
  simp only [← arrow_congr, ← Equivₓ.coe_fn_mk, ← AlgHom.comp_apply]
  congr
  exact (e₂.symm_apply_apply _).symm

@[simp]
theorem arrow_congr_refl : arrowCongr AlgEquiv.refl AlgEquiv.refl = Equivₓ.refl (A₁ →ₐ[R] A₂) := by
  ext
  rfl

@[simp]
theorem arrow_congr_trans {A₁' A₂' A₃' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Semiringₓ A₃'] [Algebra R A₁']
    [Algebra R A₂'] [Algebra R A₃'] (e₁ : A₁ ≃ₐ[R] A₂) (e₁' : A₁' ≃ₐ[R] A₂') (e₂ : A₂ ≃ₐ[R] A₃) (e₂' : A₂' ≃ₐ[R] A₃') :
    arrowCongr (e₁.trans e₂) (e₁'.trans e₂') = (arrowCongr e₁ e₁').trans (arrowCongr e₂ e₂') := by
  ext
  rfl

@[simp]
theorem arrow_congr_symm {A₁' A₂' : Type _} [Semiringₓ A₁'] [Semiringₓ A₂'] [Algebra R A₁'] [Algebra R A₂']
    (e₁ : A₁ ≃ₐ[R] A₁') (e₂ : A₂ ≃ₐ[R] A₂') : (arrowCongr e₁ e₂).symm = arrowCongr e₁.symm e₂.symm := by
  ext
  rfl

/-- If an algebra morphism has an inverse, it is a algebra isomorphism. -/
def ofAlgHom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ : f.comp g = AlgHom.id R A₂) (h₂ : g.comp f = AlgHom.id R A₁) :
    A₁ ≃ₐ[R] A₂ :=
  { f with toFun := f, invFun := g, left_inv := AlgHom.ext_iff.1 h₂, right_inv := AlgHom.ext_iff.1 h₁ }

theorem coe_alg_hom_of_alg_hom (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) : ↑(ofAlgHom f g h₁ h₂) = f :=
  AlgHom.ext fun _ => rfl

@[simp]
theorem of_alg_hom_coe_alg_hom (f : A₁ ≃ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) : ofAlgHom (↑f) g h₁ h₂ = f :=
  ext fun _ => rfl

theorem of_alg_hom_symm (f : A₁ →ₐ[R] A₂) (g : A₂ →ₐ[R] A₁) (h₁ h₂) : (ofAlgHom f g h₁ h₂).symm = ofAlgHom g f h₂ h₁ :=
  rfl

/-- Promotes a bijective algebra homomorphism to an algebra equivalence. -/
noncomputable def ofBijective (f : A₁ →ₐ[R] A₂) (hf : Function.Bijective f) : A₁ ≃ₐ[R] A₂ :=
  { RingEquiv.ofBijective (f : A₁ →+* A₂) hf, f with }

@[simp]
theorem coe_of_bijective {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} : (AlgEquiv.ofBijective f hf : A₁ → A₂) = f :=
  rfl

theorem of_bijective_apply {f : A₁ →ₐ[R] A₂} {hf : Function.Bijective f} (a : A₁) :
    (AlgEquiv.ofBijective f hf) a = f a :=
  rfl

/-- Forgetting the multiplicative structures, an equivalence of algebras is a linear equivalence. -/
@[simps apply]
def toLinearEquiv (e : A₁ ≃ₐ[R] A₂) : A₁ ≃ₗ[R] A₂ :=
  { e with toFun := e, map_smul' := e.map_smul, invFun := e.symm }

@[simp]
theorem to_linear_equiv_refl : (AlgEquiv.refl : A₁ ≃ₐ[R] A₁).toLinearEquiv = LinearEquiv.refl R A₁ :=
  rfl

@[simp]
theorem to_linear_equiv_symm (e : A₁ ≃ₐ[R] A₂) : e.toLinearEquiv.symm = e.symm.toLinearEquiv :=
  rfl

@[simp]
theorem to_linear_equiv_trans (e₁ : A₁ ≃ₐ[R] A₂) (e₂ : A₂ ≃ₐ[R] A₃) :
    (e₁.trans e₂).toLinearEquiv = e₁.toLinearEquiv.trans e₂.toLinearEquiv :=
  rfl

theorem to_linear_equiv_injective : Function.Injective (toLinearEquiv : _ → A₁ ≃ₗ[R] A₂) := fun e₁ e₂ h =>
  ext <| LinearEquiv.congr_fun h

/-- Interpret an algebra equivalence as a linear map. -/
def toLinearMap : A₁ →ₗ[R] A₂ :=
  e.toAlgHom.toLinearMap

@[simp]
theorem to_alg_hom_to_linear_map : (e : A₁ →ₐ[R] A₂).toLinearMap = e.toLinearMap :=
  rfl

@[simp]
theorem to_linear_equiv_to_linear_map : e.toLinearEquiv.toLinearMap = e.toLinearMap :=
  rfl

@[simp]
theorem to_linear_map_apply (x : A₁) : e.toLinearMap x = e x :=
  rfl

theorem to_linear_map_injective : Function.Injective (toLinearMap : _ → A₁ →ₗ[R] A₂) := fun e₁ e₂ h =>
  ext <| LinearMap.congr_fun h

@[simp]
theorem trans_to_linear_map (f : A₁ ≃ₐ[R] A₂) (g : A₂ ≃ₐ[R] A₃) :
    (f.trans g).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

section OfLinearEquiv

variable (l : A₁ ≃ₗ[R] A₂) (map_mul : ∀ x y : A₁, l (x * y) = l x * l y)
  (commutes : ∀ r : R, l (algebraMap R A₁ r) = algebraMap R A₂ r)

/-- Upgrade a linear equivalence to an algebra equivalence,
given that it distributes over multiplication and action of scalars.
-/
@[simps apply]
def ofLinearEquiv : A₁ ≃ₐ[R] A₂ :=
  { l with toFun := l, invFun := l.symm, map_mul' := map_mul, commutes' := commutes }

@[simp]
theorem of_linear_equiv_symm :
    (ofLinearEquiv l map_mul commutes).symm =
      ofLinearEquiv l.symm (ofLinearEquiv l map_mul commutes).symm.map_mul
        (ofLinearEquiv l map_mul commutes).symm.commutes :=
  rfl

@[simp]
theorem of_linear_equiv_to_linear_equiv (map_mul) (commutes) : ofLinearEquiv e.toLinearEquiv map_mul commutes = e := by
  ext
  rfl

@[simp]
theorem to_linear_equiv_of_linear_equiv : toLinearEquiv (ofLinearEquiv l map_mul commutes) = l := by
  ext
  rfl

end OfLinearEquiv

@[simps (config := { attrs := [] }) mul one]
instance aut : Groupₓ (A₁ ≃ₐ[R] A₁) where
  mul := fun ϕ ψ => ψ.trans ϕ
  mul_assoc := fun ϕ ψ χ => rfl
  one := refl
  one_mul := fun ϕ => ext fun x => rfl
  mul_one := fun ϕ => ext fun x => rfl
  inv := symm
  mul_left_inv := fun ϕ => ext <| symm_apply_apply ϕ

@[simp]
theorem one_apply (x : A₁) : (1 : A₁ ≃ₐ[R] A₁) x = x :=
  rfl

@[simp]
theorem mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl

/-- An algebra isomorphism induces a group isomorphism between automorphism groups -/
@[simps apply]
def autCongr (ϕ : A₁ ≃ₐ[R] A₂) : (A₁ ≃ₐ[R] A₁) ≃* A₂ ≃ₐ[R] A₂ where
  toFun := fun ψ => ϕ.symm.trans (ψ.trans ϕ)
  invFun := fun ψ => ϕ.trans (ψ.trans ϕ.symm)
  left_inv := fun ψ => by
    ext
    simp_rw [trans_apply, symm_apply_apply]
  right_inv := fun ψ => by
    ext
    simp_rw [trans_apply, apply_symm_apply]
  map_mul' := fun ψ χ => by
    ext
    simp only [← mul_apply, ← trans_apply, ← symm_apply_apply]

@[simp]
theorem aut_congr_refl : autCongr AlgEquiv.refl = MulEquiv.refl (A₁ ≃ₐ[R] A₁) := by
  ext
  rfl

@[simp]
theorem aut_congr_symm (ϕ : A₁ ≃ₐ[R] A₂) : (autCongr ϕ).symm = autCongr ϕ.symm :=
  rfl

@[simp]
theorem aut_congr_trans (ϕ : A₁ ≃ₐ[R] A₂) (ψ : A₂ ≃ₐ[R] A₃) : (autCongr ϕ).trans (autCongr ψ) = autCongr (ϕ.trans ψ) :=
  rfl

/-- The tautological action by `A₁ ≃ₐ[R] A₁` on `A₁`.

This generalizes `function.End.apply_mul_action`. -/
instance applyMulSemiringAction : MulSemiringAction (A₁ ≃ₐ[R] A₁) A₁ where
  smul := (· <| ·)
  smul_zero := AlgEquiv.map_zero
  smul_add := AlgEquiv.map_add
  smul_one := AlgEquiv.map_one
  smul_mul := AlgEquiv.map_mul
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
protected theorem smul_def (f : A₁ ≃ₐ[R] A₁) (a : A₁) : f • a = f a :=
  rfl

instance apply_has_faithful_smul : HasFaithfulSmul (A₁ ≃ₐ[R] A₁) A₁ :=
  ⟨fun _ _ => AlgEquiv.ext⟩

instance apply_smul_comm_class : SmulCommClass R (A₁ ≃ₐ[R] A₁) A₁ where smul_comm := fun r e a => (e.map_smul r a).symm

instance apply_smul_comm_class' : SmulCommClass (A₁ ≃ₐ[R] A₁) R A₁ where smul_comm := fun e r a => e.map_smul r a

@[simp]
theorem algebra_map_eq_apply (e : A₁ ≃ₐ[R] A₂) {y : R} {x : A₁} : algebraMap R A₂ y = e x ↔ algebraMap R A₁ y = x :=
  ⟨fun h => by
    simpa using e.symm.to_alg_hom.algebra_map_eq_apply h, fun h => e.toAlgHom.algebra_map_eq_apply h⟩

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ A₁] [CommSemiringₓ A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

theorem map_prod {ι : Type _} (f : ι → A₁) (s : Finset ι) : e (∏ x in s, f x) = ∏ x in s, e (f x) :=
  map_prod _ f s

theorem map_finsupp_prod {α : Type _} [Zero α] {ι : Type _} (f : ι →₀ α) (g : ι → α → A₁) :
    e (f.Prod g) = f.Prod fun i a => e (g i a) :=
  map_finsupp_prod _ f g

end CommSemiringₓ

section Ringₓ

variable [CommSemiringₓ R] [Ringₓ A₁] [Ringₓ A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

protected theorem map_neg (x) : e (-x) = -e x :=
  map_neg e x

protected theorem map_sub (x y) : e (x - y) = e x - e y :=
  map_sub e x y

end Ringₓ

section DivisionRing

variable [CommRingₓ R] [DivisionRing A₁] [DivisionRing A₂]

variable [Algebra R A₁] [Algebra R A₂] (e : A₁ ≃ₐ[R] A₂)

@[simp]
theorem map_inv (x) : e x⁻¹ = (e x)⁻¹ :=
  e.toAlgHom.map_inv x

@[simp]
theorem map_div (x y) : e (x / y) = e x / e y :=
  e.toAlgHom.map_div x y

end DivisionRing

end AlgEquiv

namespace MulSemiringAction

variable {M G : Type _} (R A : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

section

variable [Monoidₓ M] [MulSemiringAction M A] [SmulCommClass M R A]

/-- Each element of the monoid defines a algebra homomorphism.

This is a stronger version of `mul_semiring_action.to_ring_hom` and
`distrib_mul_action.to_linear_map`. -/
@[simps]
def toAlgHom (m : M) : A →ₐ[R] A :=
  AlgHom.mk' (MulSemiringAction.toRingHom _ _ m) (smul_comm _)

theorem to_alg_hom_injective [HasFaithfulSmul M A] :
    Function.Injective (MulSemiringAction.toAlgHom R A : M → A →ₐ[R] A) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => AlgHom.ext_iff.1 h r

end

section

variable [Groupₓ G] [MulSemiringAction G A] [SmulCommClass G R A]

/-- Each element of the group defines a algebra equivalence.

This is a stronger version of `mul_semiring_action.to_ring_equiv` and
`distrib_mul_action.to_linear_equiv`. -/
@[simps]
def toAlgEquiv (g : G) : A ≃ₐ[R] A :=
  { MulSemiringAction.toRingEquiv _ _ g, MulSemiringAction.toAlgHom R A g with }

theorem to_alg_equiv_injective [HasFaithfulSmul G A] :
    Function.Injective (MulSemiringAction.toAlgEquiv R A : G → A ≃ₐ[R] A) := fun m₁ m₂ h =>
  eq_of_smul_eq_smul fun r => AlgEquiv.ext_iff.1 h r

end

end MulSemiringAction

section Nat

variable {R : Type _} [Semiringₓ R]

/-- Semiring ⥤ ℕ-Alg -/
-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℕ`-algebras. This is only an issue since `algebra.id` and `algebra_nat` are not yet defeq.
-- TODO: fix this by adding an `of_nat` field to semirings.
instance (priority := 99) algebraNat : Algebra ℕ R where
  commutes' := Nat.cast_commute
  smul_def' := fun _ _ => nsmul_eq_mul _ _
  toRingHom := Nat.castRingHom R

instance nat_algebra_subsingleton : Subsingleton (Algebra ℕ R) :=
  ⟨fun P Q => by
    ext
    simp ⟩

end Nat

namespace RingHom

variable {R S : Type _}

/-- Reinterpret a `ring_hom` as an `ℕ`-algebra homomorphism. -/
def toNatAlgHom [Semiringₓ R] [Semiringₓ S] (f : R →+* S) : R →ₐ[ℕ] S :=
  { f with toFun := f,
    commutes' := fun n => by
      simp }

/-- Reinterpret a `ring_hom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ringₓ R] [Ringₓ S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with
    commutes' := fun n => by
      simp }

-- note that `R`, `S` could be `semiring`s but this is useless mathematically speaking -
-- a ℚ-algebra is a ring. furthermore, this change probably slows down elaboration.
@[simp]
theorem map_rat_algebra_map [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) (r : ℚ) :
    f (algebraMap ℚ R r) = algebraMap ℚ S r :=
  RingHom.ext_iff.1 (Subsingleton.elimₓ (f.comp (algebraMap ℚ R)) (algebraMap ℚ S)) r

/-- Reinterpret a `ring_hom` as a `ℚ`-algebra homomorphism. This actually yields an equivalence,
see `ring_hom.equiv_rat_alg_hom`. -/
def toRatAlgHom [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : R →ₐ[ℚ] S :=
  { f with commutes' := f.map_rat_algebra_map }

@[simp]
theorem to_rat_alg_hom_to_ring_hom [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S) : ↑f.toRatAlgHom = f :=
  RingHom.ext fun x => rfl

end RingHom

section

variable {R S : Type _}

@[simp]
theorem AlgHom.to_ring_hom_to_rat_alg_hom [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] (f : R →ₐ[ℚ] S) :
    (f : R →+* S).toRatAlgHom = f :=
  AlgHom.ext fun x => rfl

/-- The equivalence between `ring_hom` and `ℚ`-algebra homomorphisms. -/
@[simps]
def RingHom.equivRatAlgHom [Ringₓ R] [Ringₓ S] [Algebra ℚ R] [Algebra ℚ S] : (R →+* S) ≃ (R →ₐ[ℚ] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom
  left_inv := RingHom.to_rat_alg_hom_to_ring_hom
  right_inv := AlgHom.to_ring_hom_to_rat_alg_hom

end

section Rat

instance algebraRat {α} [DivisionRing α] [CharZero α] : Algebra ℚ α :=
  (Rat.castHom α).toAlgebra' fun r x => r.cast_commute x

@[simp]
theorem algebra_map_rat_rat : algebraMap ℚ ℚ = RingHom.id ℚ :=
  Subsingleton.elimₓ _ _

-- TODO[gh-6025]: make this an instance once safe to do so
theorem algebra_rat_subsingleton {α} [Semiringₓ α] : Subsingleton (Algebra ℚ α) :=
  ⟨fun x y => Algebra.algebra_ext x y <| RingHom.congr_fun <| Subsingleton.elimₓ _ _⟩

end Rat

namespace Algebra

open Module

variable (R : Type u) (A : Type v)

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

/-- `algebra_map` as an `alg_hom`. -/
def ofId : R →ₐ[R] A :=
  { algebraMap R A with commutes' := fun _ => rfl }

variable {R}

theorem of_id_apply (r) : ofId R A r = algebraMap R A r :=
  rfl

end Algebra

section Int

variable (R : Type _) [Ringₓ R]

/-- Ring ⥤ ℤ-Alg -/
-- Lower the priority so that `algebra.id` is picked most of the time when working with
-- `ℤ`-algebras. This is only an issue since `algebra.id ℤ` and `algebra_int ℤ` are not yet defeq.
-- TODO: fix this by adding an `of_int` field to rings.
instance (priority := 99) algebraInt : Algebra ℤ R where
  commutes' := Int.cast_commute
  smul_def' := fun _ _ => zsmul_eq_mul _ _
  toRingHom := Int.castRingHom R

/-- A special case of `ring_hom.eq_int_cast'` that happens to be true definitionally -/
@[simp]
theorem algebra_map_int_eq : algebraMap ℤ R = Int.castRingHom R :=
  rfl

variable {R}

instance int_algebra_subsingleton : Subsingleton (Algebra ℤ R) :=
  ⟨fun P Q => by
    ext
    simp ⟩

end Int

namespace NoZeroSmulDivisors

variable {R A : Type _}

open Algebra

/-- If `algebra_map R A` is injective and `A` has no zero divisors,
`R`-multiples in `A` are zero only if one of the factors is zero.

Cannot be an instance because there is no `injective (algebra_map R A)` typeclass.
-/
theorem of_algebra_map_injective [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [NoZeroDivisors A]
    (h : Function.Injective (algebraMap R A)) : NoZeroSmulDivisors R A :=
  ⟨fun c x hcx => (mul_eq_zero.mp ((smul_def c x).symm.trans hcx)).imp_left (map_eq_zero_iff (algebraMap R A) h).mp⟩

variable (R A)

theorem algebra_map_injective [CommRingₓ R] [Ringₓ A] [Nontrivial A] [Algebra R A] [NoZeroSmulDivisors R A] :
    Function.Injective (algebraMap R A) :=
  suffices Function.Injective fun c : R => c • (1 : A) by
    convert this
    ext
    rw [Algebra.smul_def, mul_oneₓ]
  smul_left_injective R one_ne_zero

variable {R A}

theorem iff_algebra_map_injective [CommRingₓ R] [Ringₓ A] [IsDomain A] [Algebra R A] :
    NoZeroSmulDivisors R A ↔ Function.Injective (algebraMap R A) :=
  ⟨@NoZeroSmulDivisors.algebra_map_injective R A _ _ _ _, NoZeroSmulDivisors.of_algebra_map_injective⟩

-- see note [lower instance priority]
instance (priority := 100) CharZero.no_zero_smul_divisors_nat [Semiringₓ R] [NoZeroDivisors R] [CharZero R] :
    NoZeroSmulDivisors ℕ R :=
  NoZeroSmulDivisors.of_algebra_map_injective <| (algebraMap ℕ R).injective_nat

-- see note [lower instance priority]
instance (priority := 100) CharZero.no_zero_smul_divisors_int [Ringₓ R] [NoZeroDivisors R] [CharZero R] :
    NoZeroSmulDivisors ℤ R :=
  NoZeroSmulDivisors.of_algebra_map_injective <| (algebraMap ℤ R).injective_int

section Field

variable [Field R] [Semiringₓ A] [Algebra R A]

-- see note [lower instance priority]
instance (priority := 100) Algebra.no_zero_smul_divisors [Nontrivial A] [NoZeroDivisors A] : NoZeroSmulDivisors R A :=
  NoZeroSmulDivisors.of_algebra_map_injective (algebraMap R A).Injective

end Field

end NoZeroSmulDivisors

/-!
The R-algebra structure on `Π i : I, A i` when each `A i` is an R-algebra.

We couldn't set this up back in `algebra.pi_instances` because this file imports it.
-/


namespace Pi

variable {I : Type u}

-- The indexing type
variable {R : Type _}

-- The scalar type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

variable (I f)

instance algebra {r : CommSemiringₓ R} [s : ∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] : Algebra R (∀ i : I, f i) :=
  { (Pi.ringHom fun i => algebraMap R (f i) : R →+* ∀ i : I, f i) with
    commutes' := fun a f => by
      ext
      simp [← Algebra.commutes],
    smul_def' := fun a f => by
      ext
      simp [← Algebra.smul_def] }

@[simp]
theorem algebra_map_apply {r : CommSemiringₓ R} [s : ∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] (a : R) (i : I) :
    algebraMap R (∀ i, f i) a i = algebraMap R (f i) a :=
  rfl

-- One could also build a `Π i, R i`-algebra structure on `Π i, A i`,
-- when each `A i` is an `R i`-algebra, although I'm not sure that it's useful.
variable {I} (R) (f)

/-- `function.eval` as an `alg_hom`. The name matches `pi.eval_ring_hom`, `pi.eval_monoid_hom`,
etc. -/
@[simps]
def evalAlgHom {r : CommSemiringₓ R} [∀ i, Semiringₓ (f i)] [∀ i, Algebra R (f i)] (i : I) : (∀ i, f i) →ₐ[R] f i :=
  { Pi.evalRingHom f i with toFun := fun f => f i, commutes' := fun r => rfl }

variable (A B : Type _) [CommSemiringₓ R] [Semiringₓ B] [Algebra R B]

/-- `function.const` as an `alg_hom`. The name matches `pi.const_ring_hom`, `pi.const_monoid_hom`,
etc. -/
@[simps]
def constAlgHom : B →ₐ[R] A → B :=
  { Pi.constRingHom A B with toFun := Function.const _, commutes' := fun r => rfl }

/-- When `R` is commutative and permits an `algebra_map`, `pi.const_ring_hom` is equal to that
map. -/
@[simp]
theorem const_ring_hom_eq_algebra_map : constRingHom A R = algebraMap R (A → R) :=
  rfl

@[simp]
theorem const_alg_hom_eq_algebra_of_id : constAlgHom R A R = Algebra.ofId R (A → R) :=
  rfl

end Pi

/-- A special case of `pi.algebra` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this, -/
instance Function.algebra {R : Type _} (I : Type _) (A : Type _) [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] :
    Algebra R (I → A) :=
  Pi.algebra _ _

namespace AlgEquiv

/-- A family of algebra equivalences `Π j, (A₁ j ≃ₐ A₂ j)` generates a
multiplicative equivalence between `Π j, A₁ j` and `Π j, A₂ j`.

This is the `alg_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`alg_equiv.arrow_congr`.
-/
@[simps apply]
def piCongrRight {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiringₓ R] [∀ i, Semiringₓ (A₁ i)] [∀ i, Semiringₓ (A₂ i)]
    [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) : (∀ i, A₁ i) ≃ₐ[R] ∀ i, A₂ i :=
  { @RingEquiv.piCongrRight ι A₁ A₂ _ _ fun i => (e i).toRingEquiv with toFun := fun x j => e j (x j),
    invFun := fun x j => (e j).symm (x j),
    commutes' := fun r => by
      ext i
      simp }

@[simp]
theorem Pi_congr_right_refl {R ι : Type _} {A : ι → Type _} [CommSemiringₓ R] [∀ i, Semiringₓ (A i)]
    [∀ i, Algebra R (A i)] : (piCongrRight fun i => (AlgEquiv.refl : A i ≃ₐ[R] A i)) = AlgEquiv.refl :=
  rfl

@[simp]
theorem Pi_congr_right_symm {R ι : Type _} {A₁ A₂ : ι → Type _} [CommSemiringₓ R] [∀ i, Semiringₓ (A₁ i)]
    [∀ i, Semiringₓ (A₂ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)] (e : ∀ i, A₁ i ≃ₐ[R] A₂ i) :
    (piCongrRight e).symm = Pi_congr_right fun i => (e i).symm :=
  rfl

@[simp]
theorem Pi_congr_right_trans {R ι : Type _} {A₁ A₂ A₃ : ι → Type _} [CommSemiringₓ R] [∀ i, Semiringₓ (A₁ i)]
    [∀ i, Semiringₓ (A₂ i)] [∀ i, Semiringₓ (A₃ i)] [∀ i, Algebra R (A₁ i)] [∀ i, Algebra R (A₂ i)]
    [∀ i, Algebra R (A₃ i)] (e₁ : ∀ i, A₁ i ≃ₐ[R] A₂ i) (e₂ : ∀ i, A₂ i ≃ₐ[R] A₃ i) :
    (piCongrRight e₁).trans (piCongrRight e₂) = Pi_congr_right fun i => (e₁ i).trans (e₂ i) :=
  rfl

end AlgEquiv

section IsScalarTower

variable {R : Type _} [CommSemiringₓ R]

variable (A : Type _) [Semiringₓ A] [Algebra R A]

variable {M : Type _} [AddCommMonoidₓ M] [Module A M] [Module R M] [IsScalarTower R A M]

variable {N : Type _} [AddCommMonoidₓ N] [Module A N] [Module R N] [IsScalarTower R A N]

theorem algebra_compatible_smul (r : R) (m : M) : r • m = (algebraMap R A) r • m := by
  rw [← one_smul A m, ← smul_assoc, Algebra.smul_def, mul_oneₓ, one_smul]

@[simp]
theorem algebra_map_smul (r : R) (m : M) : (algebraMap R A) r • m = r • m :=
  (algebra_compatible_smul A r m).symm

theorem NoZeroSmulDivisors.trans (R A M : Type _) [CommRingₓ R] [Ringₓ A] [IsDomain A] [Algebra R A] [AddCommGroupₓ M]
    [Module R M] [Module A M] [IsScalarTower R A M] [NoZeroSmulDivisors R A] [NoZeroSmulDivisors A M] :
    NoZeroSmulDivisors R M := by
  refine' ⟨fun r m h => _⟩
  rw [algebra_compatible_smul A r m] at h
  cases' smul_eq_zero.1 h with H H
  · have : Function.Injective (algebraMap R A) := NoZeroSmulDivisors.iff_algebra_map_injective.1 inferInstance
    left
    exact (injective_iff_map_eq_zero _).1 this _ H
    
  · right
    exact H
    

variable {A}

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_smul_comm_class : SmulCommClass R A M :=
  ⟨fun r a m => by
    rw [algebra_compatible_smul A r (a • m), smul_smul, Algebra.commutes, mul_smul, ← algebra_compatible_smul]⟩

-- see Note [lower instance priority]
instance (priority := 100) IsScalarTower.to_smul_comm_class' : SmulCommClass A R M :=
  SmulCommClass.symm _ _ _

theorem smul_algebra_smul_comm (r : R) (a : A) (m : M) : a • r • m = r • a • m :=
  smul_comm _ _ _

namespace LinearMap

instance coeIsScalarTower : Coe (M →ₗ[A] N) (M →ₗ[R] N) :=
  ⟨restrictScalars R⟩

variable (R) {A M N}

@[simp, norm_cast squash]
theorem coe_restrict_scalars_eq_coe (f : M →ₗ[A] N) : (f.restrictScalars R : M → N) = f :=
  rfl

@[simp, norm_cast squash]
theorem coe_coe_is_scalar_tower (f : M →ₗ[A] N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl

/-- `A`-linearly coerce a `R`-linear map from `M` to `A` to a function, given an algebra `A` over
a commutative semiring `R` and `M` a module over `R`. -/
def ltoFun (R : Type u) (M : Type v) (A : Type w) [CommSemiringₓ R] [AddCommMonoidₓ M] [Module R M] [CommRingₓ A]
    [Algebra R A] : (M →ₗ[R] A) →ₗ[A] M → A where
  toFun := LinearMap.toFun
  map_add' := fun f g => rfl
  map_smul' := fun c f => rfl

end LinearMap

end IsScalarTower

/-! TODO: The following lemmas no longer involve `algebra` at all, and could be moved closer
to `algebra/module/submodule.lean`. Currently this is tricky because `ker`, `range`, `⊤`, and `⊥`
are all defined in `linear_algebra/basic.lean`. -/


section Module

open Module

variable (R S M N : Type _) [Semiringₓ R] [Semiringₓ S] [HasSmul R S]

variable [AddCommMonoidₓ M] [Module R M] [Module S M] [IsScalarTower R S M]

variable [AddCommMonoidₓ N] [Module R N] [Module S N] [IsScalarTower R S N]

variable {S M N}

@[simp]
theorem LinearMap.ker_restrict_scalars (f : M →ₗ[S] N) : (f.restrictScalars R).ker = f.ker.restrictScalars R :=
  rfl

end Module

namespace Submodule

variable (R A M : Type _)

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [AddCommMonoidₓ M]

variable [Module R M] [Module A M] [IsScalarTower R A M]

/-- If `A` is an `R`-algebra such that the induced morhpsim `R →+* A` is surjective, then the
`R`-module generated by a set `X` equals the `A`-module generated by `X`. -/
theorem span_eq_restrict_scalars (X : Set M) (hsur : Function.Surjective (algebraMap R A)) :
    span R X = restrictScalars R (span A X) := by
  apply (span_le_restrict_scalars R A X).antisymm fun m hm => _
  refine' span_induction hm subset_span (zero_mem _) (fun _ _ => add_mem) fun a m hm => _
  obtain ⟨r, rfl⟩ := hsur a
  simpa [← algebra_map_smul] using smul_mem _ r hm

end Submodule

namespace AlgHom

variable {R : Type u} {A : Type v} {B : Type w} {I : Type _}

variable [CommSemiringₓ R] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R A] [Algebra R B]

/-- `R`-algebra homomorphism between the function spaces `I → A` and `I → B`, induced by an
`R`-algebra homomorphism `f` between `A` and `B`. -/
@[simps]
protected def compLeft (f : A →ₐ[R] B) (I : Type _) : (I → A) →ₐ[R] I → B :=
  { f.toRingHom.compLeft I with toFun := fun h => f ∘ h,
    commutes' := fun c => by
      ext
      exact f.commutes' c }

end AlgHom

example {R A} [CommSemiringₓ R] [Semiringₓ A] [Module R A] [SmulCommClass R A A] [IsScalarTower R A A] : Algebra R A :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

