/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.SmulWithZero
import Mathbin.GroupTheory.GroupAction.BigOperators
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.Tactic.NormNum

/-!
# Modules over a ring

In this file we define

* `module R M` : an additive commutative monoid `M` is a `module` over a
  `semiring R` if for `r : R` and `x : M` their "scalar multiplication `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

## Implementation notes

In typical mathematical usage, our definition of `module` corresponds to "semimodule", and the
word "module" is reserved for `module R M` where `R` is a `ring` and `M` an `add_comm_group`.
If `R` is a `field` and `M` an `add_comm_group`, `M` would be called an `R`-vector space.
Since those assumptions can be made by changing the typeclasses applied to `R` and `M`,
without changing the axioms in `module`, mathlib calls everything a `module`.

In older versions of mathlib, we had separate `semimodule` and `vector_space` abbreviations.
This caused inference issues in some cases, while not providing any real advantages, so we decided
to use a canonical `module` typeclass throughout.

## Tags

semimodule, module, vector space
-/


open Function

open BigOperators

universe u v

variable {α R k S M M₂ M₃ ι : Type _}

/-- A module is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[ext, protect_proj]
class Module (R : Type u) (M : Type v) [Semiringₓ R] [AddCommMonoidₓ M] extends DistribMulAction R M where
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  zero_smul : ∀ x : M, (0 : R) • x = 0

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (r s : R) (x y : M)

/-- A module over a semiring automatically inherits a `mul_action_with_zero` structure. -/
-- see Note [lower instance priority]
instance (priority := 100) Module.toMulActionWithZero : MulActionWithZero R M :=
  { (inferInstance : MulAction R M) with smul_zero := smul_zero, zero_smul := Module.zero_smul }

instance AddCommMonoidₓ.natModule : Module ℕ M where
  one_smul := one_nsmul
  mul_smul := fun m n a => mul_nsmul a m n
  smul_add := fun n a b => nsmul_add a b n
  smul_zero := nsmul_zero
  zero_smul := zero_nsmul
  add_smul := fun r s x => add_nsmul x r s

theorem add_smul : (r + s) • x = r • x + s • x :=
  Module.add_smul r s x

theorem Convex.combo_self {a b : R} (h : a + b = 1) (x : M) : a • x + b • x = x := by
  rw [← add_smul, h, one_smul]

variable (R)

theorem two_smul : (2 : R) • x = x + x := by
  rw [bit0, add_smul, one_smul]

theorem two_smul' : (2 : R) • x = bit0 x :=
  two_smul R x

@[simp]
theorem inv_of_two_smul_add_inv_of_two_smul [Invertible (2 : R)] (x : M) : (⅟ 2 : R) • x + (⅟ 2 : R) • x = x :=
  Convex.combo_self inv_of_two_add_inv_of_two _

/-- Pullback a `module` structure along an injective additive monoid homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.module [AddCommMonoidₓ M₂] [HasSmul R M₂] (f : M₂ →+ M) (hf : Injective f)
    (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.DistribMulAction f smul with smul := (· • ·),
    add_smul := fun c₁ c₂ x =>
      hf <| by
        simp only [← smul, ← f.map_add, ← add_smul],
    zero_smul := fun x =>
      hf <| by
        simp only [← smul, ← zero_smul, ← f.map_zero] }

/-- Pushforward a `module` structure along a surjective additive monoid homomorphism. -/
protected def Function.Surjective.module [AddCommMonoidₓ M₂] [HasSmul R M₂] (f : M →+ M₂) (hf : Surjective f)
    (smul : ∀ (c : R) (x), f (c • x) = c • f x) : Module R M₂ :=
  { hf.DistribMulAction f smul with smul := (· • ·),
    add_smul := fun c₁ c₂ x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [← add_smul, smul, f.map_add],
    zero_smul := fun x => by
      rcases hf x with ⟨x, rfl⟩
      simp only [f.map_zero, smul, ← zero_smul] }

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →+* S`.

See also `function.surjective.mul_action_left` and `function.surjective.distrib_mul_action_left`.
-/
@[reducible]
def Function.Surjective.moduleLeft {R S M : Type _} [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [Semiringₓ S]
    [HasSmul S M] (f : R →+* S) (hf : Function.Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) : Module S M :=
  { hf.distribMulActionLeft f.toMonoidHom hsmul with smul := (· • ·),
    zero_smul := fun x => by
      rw [← f.map_zero, hsmul, zero_smul],
    add_smul :=
      hf.Forall₂.mpr fun a b x => by
        simp only [f.map_add, ← hsmul, ← add_smul] }

variable {R} (M)

/-- Compose a `module` with a `ring_hom`, with action `f s • m`.

See note [reducible non-instances]. -/
@[reducible]
def Module.compHom [Semiringₓ S] (f : S →+* R) : Module S M :=
  { MulActionWithZero.compHom M f.toMonoidWithZeroHom, DistribMulAction.compHom M (f : S →* R) with
    smul := HasSmul.Comp.smul f,
    add_smul := fun r s x => by
      simp [← add_smul] }

variable (R) (M)

/-- `(•)` as an `add_monoid_hom`.

This is a stronger version of `distrib_mul_action.to_add_monoid_End` -/
@[simps apply_apply]
def Module.toAddMonoidEnd : R →+* AddMonoidₓ.End M :=
  { DistribMulAction.toAddMonoidEnd R M with
    map_zero' :=
      AddMonoidHom.ext fun r => by
        simp ,
    map_add' := fun x y =>
      AddMonoidHom.ext fun r => by
        simp [← add_smul] }

/-- A convenience alias for `module.to_add_monoid_End` as an `add_monoid_hom`, usually to allow the
use of `add_monoid_hom.flip`. -/
def smulAddHom : R →+ M →+ M :=
  (Module.toAddMonoidEnd R M).toAddMonoidHom

variable {R M}

@[simp]
theorem smul_add_hom_apply (r : R) (x : M) : smulAddHom R M r x = r • x :=
  rfl

theorem Module.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 := by
  rw [← one_smul R x, ← zero_eq_one, zero_smul]

theorem List.sum_smul {l : List R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_list_sum l

theorem Multiset.sum_smul {l : Multiset R} {x : M} : l.Sum • x = (l.map fun r => r • x).Sum :=
  ((smulAddHom R M).flip x).map_multiset_sum l

theorem Finset.sum_smul {f : ι → R} {s : Finset ι} {x : M} : (∑ i in s, f i) • x = ∑ i in s, f i • x :=
  ((smulAddHom R M).flip x).map_sum f s

end AddCommMonoidₓ

variable (R)

/-- An `add_comm_monoid` that is a `module` over a `ring` carries a natural `add_comm_group`
structure.
See note [reducible non-instances]. -/
@[reducible]
def Module.addCommMonoidToAddCommGroup [Ringₓ R] [AddCommMonoidₓ M] [Module R M] : AddCommGroupₓ M :=
  { (inferInstance : AddCommMonoidₓ M) with neg := fun a => (-1 : R) • a,
    add_left_neg := fun a =>
      show (-1 : R) • a + a = 0 by
        nth_rw 1[← one_smul _ a]
        rw [← add_smul, add_left_negₓ, zero_smul] }

variable {R}

section AddCommGroupₓ

variable (R M) [Semiringₓ R] [AddCommGroupₓ M]

instance AddCommGroupₓ.intModule : Module ℤ M where
  one_smul := one_zsmul
  mul_smul := fun m n a => mul_zsmul a m n
  smul_add := fun n a b => zsmul_add a b n
  smul_zero := zsmul_zero
  zero_smul := zero_zsmul
  add_smul := fun r s x => add_zsmul x r s

/-- A structure containing most informations as in a module, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `add_comm_group`,
this provides a way to construct a module structure by checking less properties, in
`module.of_core`. -/
@[nolint has_inhabited_instance]
structure Module.Core extends HasSmul R M where
  smul_add : ∀ (r : R) (x y : M), r • (x + y) = r • x + r • y
  add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  mul_smul : ∀ (r s : R) (x : M), (r * s) • x = r • s • x
  one_smul : ∀ x : M, (1 : R) • x = x

variable {R M}

/-- Define `module` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `module.core`, when the underlying space is an `add_comm_group`. -/
def Module.ofCore (H : Module.Core R M) : Module R M := by
  let this := H.to_has_smul <;>
    exact
      { H with zero_smul := fun x => (AddMonoidHom.mk' (fun r : R => r • x) fun r s => H.add_smul r s x).map_zero,
        smul_zero := fun r => (AddMonoidHom.mk' ((· • ·) r) (H.smul_add r)).map_zero }

end AddCommGroupₓ

/-- A variant of `module.ext` that's convenient for term-mode. -/
-- We'll later use this to show `module ℕ M` and `module ℤ M` are subsingletons.
theorem Module.ext' {R : Type _} [Semiringₓ R] {M : Type _} [AddCommMonoidₓ M] (P Q : Module R M)
    (w :
      ∀ (r : R) (m : M),
        by
          have := P
          exact r • m = by
          have := Q
          exact r • m) :
    P = Q := by
  ext
  exact w _ _

section Module

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M] (r s : R) (x y : M)

@[simp]
theorem neg_smul : -r • x = -(r • x) :=
  eq_neg_of_add_eq_zero_left <| by
    rw [← add_smul, add_left_negₓ, zero_smul]

@[simp]
theorem neg_smul_neg : -r • -x = r • x := by
  rw [neg_smul, smul_neg, neg_negₓ]

@[simp]
theorem Units.neg_smul (u : Rˣ) (x : M) : -u • x = -(u • x) := by
  rw [Units.smul_def, Units.coe_neg, neg_smul, Units.smul_def]

variable (R)

theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by
  simp

variable {R}

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y := by
  simp [← add_smul, ← sub_eq_add_neg]

end Module

/-- A module over a `subsingleton` semiring is a `subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
protected theorem Module.subsingleton (R M : Type _) [Semiringₓ R] [Subsingleton R] [AddCommMonoidₓ M] [Module R M] :
    Subsingleton M :=
  ⟨fun x y => by
    rw [← one_smul R x, ← one_smul R y, Subsingleton.elimₓ (1 : R) 0, zero_smul, zero_smul]⟩

/-- A semiring is `nontrivial` provided that there exists a nontrivial module over this semiring. -/
protected theorem Module.nontrivial (R M : Type _) [Semiringₓ R] [Nontrivial M] [AddCommMonoidₓ M] [Module R M] :
    Nontrivial R :=
  (subsingleton_or_nontrivial R).resolve_left fun hR => not_subsingleton M <| Module.subsingleton R M

-- see Note [lower instance priority]
instance (priority := 910) Semiringₓ.toModule [Semiringₓ R] : Module R R where
  smul_add := mul_addₓ
  add_smul := add_mulₓ
  zero_smul := zero_mul
  smul_zero := mul_zero

/-- Like `semiring.to_module`, but multiplies on the right. -/
-- see Note [lower instance priority]
instance (priority := 910) Semiringₓ.toOppositeModule [Semiringₓ R] : Module Rᵐᵒᵖ R :=
  { MonoidWithZeroₓ.toOppositeMulActionWithZero R with smul_add := fun r x y => add_mulₓ _ _ _,
    add_smul := fun r x y => mul_addₓ _ _ _ }

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def RingHom.toModule [Semiringₓ R] [Semiringₓ S] (f : R →+* S) : Module R S :=
  Module.compHom S f

/-- The tautological action by `R →+* R` on `R`.

This generalizes `function.End.apply_mul_action`. -/
instance RingHom.applyDistribMulAction [Semiringₓ R] : DistribMulAction (R →+* R) R where
  smul := (· <| ·)
  smul_zero := RingHom.map_zero
  smul_add := RingHom.map_add
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

@[simp]
protected theorem RingHom.smul_def [Semiringₓ R] (f : R →+* R) (a : R) : f • a = f a :=
  rfl

/-- `ring_hom.apply_distrib_mul_action` is faithful. -/
instance RingHom.apply_has_faithful_smul [Semiringₓ R] : HasFaithfulSmul (R →+* R) R :=
  ⟨RingHom.ext⟩

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

section

variable (R)

/-- `nsmul` is equal to any other module structure via a cast. -/
theorem nsmul_eq_smul_cast (n : ℕ) (b : M) : n • b = (n : R) • b := by
  induction' n with n ih
  · rw [Nat.cast_zeroₓ, zero_smul, zero_smul]
    
  · rw [Nat.succ_eq_add_one, Nat.cast_succₓ, add_smul, add_smul, one_smul, ih, one_smul]
    

end

/-- Convert back any exotic `ℕ`-smul to the canonical instance. This should not be needed since in
mathlib all `add_comm_monoid`s should normally have exactly one `ℕ`-module structure by design.
-/
theorem nat_smul_eq_nsmul (h : Module ℕ M) (n : ℕ) (x : M) : @HasSmul.smul ℕ M h.toHasSmul n x = n • x := by
  rw [nsmul_eq_smul_cast ℕ n x, Nat.cast_id]

/-- All `ℕ`-module structures are equal. Not an instance since in mathlib all `add_comm_monoid`
should normally have exactly one `ℕ`-module structure by design. -/
def AddCommMonoidₓ.natModule.unique : Unique (Module ℕ M) where
  default := by
    infer_instance
  uniq := fun P => (Module.ext' P _) fun n => nat_smul_eq_nsmul P n

instance AddCommMonoidₓ.nat_is_scalar_tower :
    IsScalarTower ℕ R M where smul_assoc := fun n x y =>
    Nat.recOn n
      (by
        simp only [← zero_smul])
      fun n ih => by
      simp only [← Nat.succ_eq_add_one, ← add_smul, ← one_smul, ← ih]

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Semiringₓ S] [Ringₓ R] [AddCommGroupₓ M] [Module S M] [Module R M]

section

variable (R)

/-- `zsmul` is equal to any other module structure via a cast. -/
theorem zsmul_eq_smul_cast (n : ℤ) (b : M) : n • b = (n : R) • b :=
  have : (smulAddHom ℤ M).flip b = ((smulAddHom R M).flip b).comp (Int.castAddHom R) := by
    ext
    simp
  AddMonoidHom.congr_fun this n

end

/-- Convert back any exotic `ℤ`-smul to the canonical instance. This should not be needed since in
mathlib all `add_comm_group`s should normally have exactly one `ℤ`-module structure by design. -/
theorem int_smul_eq_zsmul (h : Module ℤ M) (n : ℤ) (x : M) : @HasSmul.smul ℤ M h.toHasSmul n x = n • x := by
  rw [zsmul_eq_smul_cast ℤ n x, Int.cast_id]

/-- All `ℤ`-module structures are equal. Not an instance since in mathlib all `add_comm_group`
should normally have exactly one `ℤ`-module structure by design. -/
def AddCommGroupₓ.intModule.unique : Unique (Module ℤ M) where
  default := by
    infer_instance
  uniq := fun P => (Module.ext' P _) fun n => int_smul_eq_zsmul P n

end AddCommGroupₓ

theorem map_int_cast_smul [AddCommGroupₓ M] [AddCommGroupₓ M₂] {F : Type _} [AddMonoidHomClass F M M₂] (f : F)
    (R S : Type _) [Ringₓ R] [Ringₓ S] [Module R M] [Module S M₂] (x : ℤ) (a : M) : f ((x : R) • a) = (x : S) • f a :=
  by
  simp only [zsmul_eq_smul_cast, ← map_zsmul]

theorem map_nat_cast_smul [AddCommMonoidₓ M] [AddCommMonoidₓ M₂] {F : Type _} [AddMonoidHomClass F M M₂] (f : F)
    (R S : Type _) [Semiringₓ R] [Semiringₓ S] [Module R M] [Module S M₂] (x : ℕ) (a : M) :
    f ((x : R) • a) = (x : S) • f a := by
  simp only [nsmul_eq_smul_cast, ← map_nsmul]

theorem map_inv_int_cast_smul [AddCommGroupₓ M] [AddCommGroupₓ M₂] {F : Type _} [AddMonoidHomClass F M M₂] (f : F)
    (R S : Type _) [DivisionRing R] [DivisionRing S] [Module R M] [Module S M₂] (n : ℤ) (x : M) :
    f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases' hR : (n : R) = 0 <;> by_cases' hS : (n : S) = 0
  · simp [← hR, ← hS]
    
  · suffices ∀ y, f y = 0 by
      simp [← this]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x), ← map_int_cast_smul f R S]
    simp [← hR]
    
  · suffices ∀ y, f y = 0 by
      simp [← this]
    clear x
    intro x
    rw [← smul_inv_smul₀ hR x, map_int_cast_smul f R S, hS, zero_smul]
    
  · rw [← inv_smul_smul₀ hS (f _), ← map_int_cast_smul f R S, smul_inv_smul₀ hR]
    

theorem map_inv_nat_cast_smul [AddCommGroupₓ M] [AddCommGroupₓ M₂] {F : Type _} [AddMonoidHomClass F M M₂] (f : F)
    (R S : Type _) [DivisionRing R] [DivisionRing S] [Module R M] [Module S M₂] (n : ℕ) (x : M) :
    f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  exact_mod_cast map_inv_int_cast_smul f R S n x

theorem map_rat_cast_smul [AddCommGroupₓ M] [AddCommGroupₓ M₂] {F : Type _} [AddMonoidHomClass F M M₂] (f : F)
    (R S : Type _) [DivisionRing R] [DivisionRing S] [Module R M] [Module S M₂] (c : ℚ) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul, map_int_cast_smul f R S,
    map_inv_nat_cast_smul f R S]

theorem map_rat_smul [AddCommGroupₓ M] [AddCommGroupₓ M₂] [Module ℚ M] [Module ℚ M₂] {F : Type _}
    [AddMonoidHomClass F M M₂] (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x :=
  Rat.cast_id c ▸ map_rat_cast_smul f ℚ ℚ c x

/-- There can be at most one `module ℚ E` structure on an additive commutative group. This is not
an instance because `simp` becomes very slow if we have many `subsingleton` instances,
see [gh-6025]. -/
theorem subsingleton_rat_module (E : Type _) [AddCommGroupₓ E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x => @map_rat_smul _ _ _ _ P Q _ _ (AddMonoidHom.id E) r x⟩

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of integer numbers in `R` and `S`. -/
theorem inv_int_cast_smul_eq {E : Type _} (R S : Type _) [AddCommGroupₓ E] [DivisionRing R] [DivisionRing S]
    [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_int_cast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of natural numbers in `R` and `S`. -/
theorem inv_nat_cast_smul_eq {E : Type _} (R S : Type _) [AddCommGroupₓ E] [DivisionRing R] [DivisionRing S]
    [Module R E] [Module S E] (n : ℕ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_nat_cast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over a division rings `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of integers in `R` -/
theorem inv_int_cast_smul_comm {α E : Type _} (R : Type _) [AddCommGroupₓ E] [DivisionRing R] [Monoidₓ α] [Module R E]
    [DistribMulAction α E] (n : ℤ) (s : α) (x : E) : (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_int_cast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm

/-- If `E` is a vector space over a division rings `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`. -/
theorem inv_nat_cast_smul_comm {α E : Type _} (R : Type _) [AddCommGroupₓ E] [DivisionRing R] [Monoidₓ α] [Module R E]
    [DistribMulAction α E] (n : ℕ) (s : α) (x : E) : (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_nat_cast_smul (DistribMulAction.toAddMonoidHom E s) R R n x).symm

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on rational numbers in `R` and `S`. -/
theorem rat_cast_smul_eq {E : Type _} (R S : Type _) [AddCommGroupₓ E] [DivisionRing R] [DivisionRing S] [Module R E]
    [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x :=
  map_rat_cast_smul (AddMonoidHom.id E) R S r x

instance AddCommGroupₓ.int_is_scalar_tower {R : Type u} {M : Type v} [Ringₓ R] [AddCommGroupₓ M] [Module R M] :
    IsScalarTower ℤ R M where smul_assoc := fun n x y => ((smulAddHom R M).flip y).map_zsmul x n

instance IsScalarTower.rat {R : Type u} {M : Type v} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [Module ℚ R]
    [Module ℚ M] : IsScalarTower ℚ R M where smul_assoc := fun r x y => map_rat_smul ((smulAddHom R M).flip y) r x

instance SmulCommClass.rat {R : Type u} {M : Type v} [Semiringₓ R] [AddCommGroupₓ M] [Module R M] [Module ℚ M] :
    SmulCommClass ℚ R M where smul_comm := fun r x y => (map_rat_smul (smulAddHom R M x) r y).symm

instance SmulCommClass.rat' {R : Type u} {M : Type v} [Semiringₓ R] [AddCommGroupₓ M] [Module R M] [Module ℚ M] :
    SmulCommClass R ℚ M :=
  SmulCommClass.symm _ _ _

section NoZeroSmulDivisors

/-! ### `no_zero_smul_divisors`

This section defines the `no_zero_smul_divisors` class, and includes some tests
for the vanishing of elements (especially in modules over division rings).
-/


/-- `no_zero_smul_divisors R M` states that a scalar multiple is `0` only if either argument is `0`.
This a version of saying that `M` is torsion free, without assuming `R` is zero-divisor free.

The main application of `no_zero_smul_divisors R M`, when `M` is a module,
is the result `smul_eq_zero`: a scalar multiple is `0` iff either argument is `0`.

It is a generalization of the `no_zero_divisors` class to heterogeneous multiplication.
-/
class NoZeroSmulDivisors (R M : Type _) [Zero R] [Zero M] [HasSmul R M] : Prop where
  eq_zero_or_eq_zero_of_smul_eq_zero : ∀ {c : R} {x : M}, c • x = 0 → c = 0 ∨ x = 0

export NoZeroSmulDivisors (eq_zero_or_eq_zero_of_smul_eq_zero)

/-- Pullback a `no_zero_smul_divisors` instance along an injective function. -/
theorem Function.Injective.no_zero_smul_divisors {R M N : Type _} [Zero R] [Zero M] [Zero N] [HasSmul R M] [HasSmul R N]
    [NoZeroSmulDivisors R N] (f : M → N) (hf : Function.Injective f) (h0 : f 0 = 0)
    (hs : ∀ (c : R) (x : M), f (c • x) = c • f x) : NoZeroSmulDivisors R M :=
  ⟨fun c m h =>
    Or.imp_rightₓ (@hf _ _) <|
      h0.symm ▸
        eq_zero_or_eq_zero_of_smul_eq_zero
          (by
            rw [← hs, h, h0])⟩

-- See note [lower instance priority]
instance (priority := 100) NoZeroDivisors.to_no_zero_smul_divisors [Zero R] [Mul R] [NoZeroDivisors R] :
    NoZeroSmulDivisors R R :=
  ⟨fun c x => eq_zero_or_eq_zero_of_mul_eq_zero⟩

section Module

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

@[simp]
theorem smul_eq_zero [NoZeroSmulDivisors R M] {c : R} {x : M} : c • x = 0 ↔ c = 0 ∨ x = 0 :=
  ⟨eq_zero_or_eq_zero_of_smul_eq_zero, fun h => h.elim (fun h => h.symm ▸ zero_smul R x) fun h => h.symm ▸ smul_zero c⟩

theorem smul_ne_zero [NoZeroSmulDivisors R M] {c : R} {x : M} : c • x ≠ 0 ↔ c ≠ 0 ∧ x ≠ 0 := by
  simp only [← Ne.def, ← smul_eq_zero, ← not_or_distrib]

section Nat

variable (R) (M) [NoZeroSmulDivisors R M] [CharZero R]

include R

theorem Nat.no_zero_smul_divisors : NoZeroSmulDivisors ℕ M :=
  ⟨by
    intro c x
    rw [nsmul_eq_smul_cast R, smul_eq_zero]
    simp ⟩

@[simp]
theorem two_nsmul_eq_zero {v : M} : 2 • v = 0 ↔ v = 0 := by
  have := Nat.no_zero_smul_divisors R M
  norm_num [← smul_eq_zero]

end Nat

variable (R M)

/-- If `M` is an `R`-module with one and `M` has characteristic zero, then `R` has characteristic
zero as well. Usually `M` is an `R`-algebra. -/
theorem CharZero.of_module (M) [AddCommMonoidWithOne M] [CharZero M] [Module R M] : CharZero R := by
  refine' ⟨fun m n h => @Nat.cast_injective M _ _ _ _ _⟩
  rw [← nsmul_one, ← nsmul_one, nsmul_eq_smul_cast R m (1 : M), nsmul_eq_smul_cast R n (1 : M), h]

end Module

section AddCommGroupₓ

-- `R` can still be a semiring here
variable [Semiringₓ R] [AddCommGroupₓ M] [Module R M]

section SmulInjective

variable (M)

theorem smul_right_injective [NoZeroSmulDivisors R M] {c : R} (hc : c ≠ 0) : Function.Injective ((· • ·) c : M → M) :=
  (injective_iff_map_eq_zero (smulAddHom R M c)).2 fun a ha => (smul_eq_zero.mp ha).resolve_left hc

variable {M}

theorem smul_right_inj [NoZeroSmulDivisors R M] {c : R} (hc : c ≠ 0) {x y : M} : c • x = c • y ↔ x = y :=
  (smul_right_injective M hc).eq_iff

end SmulInjective

section Nat

variable (R M) [NoZeroSmulDivisors R M] [CharZero R]

include R

theorem self_eq_neg {v : M} : v = -v ↔ v = 0 := by
  rw [← two_nsmul_eq_zero R M, two_smul, add_eq_zero_iff_eq_neg]

theorem neg_eq_self {v : M} : -v = v ↔ v = 0 := by
  rw [eq_comm, self_eq_neg R M]

theorem self_ne_neg {v : M} : v ≠ -v ↔ v ≠ 0 :=
  (self_eq_neg R M).Not

theorem neg_ne_self {v : M} : -v ≠ v ↔ v ≠ 0 :=
  (neg_eq_self R M).Not

end Nat

end AddCommGroupₓ

section Module

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M] [NoZeroSmulDivisors R M]

section SmulInjective

variable (R)

theorem smul_left_injective {x : M} (hx : x ≠ 0) : Function.Injective fun c : R => c • x := fun c d h =>
  sub_eq_zero.mp
    ((smul_eq_zero.mp
          (calc
            (c - d) • x = c • x - d • x := sub_smul c d x
            _ = 0 := sub_eq_zero.mpr h
            )).resolve_right
      hx)

end SmulInjective

end Module

section DivisionRing

variable [DivisionRing R] [AddCommGroupₓ M] [Module R M]

-- see note [lower instance priority]
instance (priority := 100) DivisionRing.to_no_zero_smul_divisors : NoZeroSmulDivisors R M :=
  ⟨fun c x h => or_iff_not_imp_left.2 fun hc => (smul_eq_zero_iff_eq' hc).1 h⟩

end DivisionRing

end NoZeroSmulDivisors

@[simp]
theorem Nat.smul_one_eq_coe {R : Type _} [Semiringₓ R] (m : ℕ) : m • (1 : R) = ↑m := by
  rw [nsmul_eq_mul, mul_oneₓ]

@[simp]
theorem Int.smul_one_eq_coe {R : Type _} [Ringₓ R] (m : ℤ) : m • (1 : R) = ↑m := by
  rw [zsmul_eq_mul, mul_oneₓ]

theorem Finset.cast_card [CommSemiringₓ R] (s : Finset α) : (s.card : R) = ∑ a in s, 1 := by
  rw [Finset.sum_const, Nat.smul_one_eq_coe]

