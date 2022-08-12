/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.MonoidAlgebra.Basic

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `free_algebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `free_algebra.ι R` is the function `X → free_algebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `free_algebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : free_algebra R X → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equiv_monoid_algebra_free_monoid : free_algebra R X ≃ₐ[R] monoid_algebra R (free_monoid X)`
6. An inductive principle `induction`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `free_algebra.pre` by an
inductively defined relation `free_algebra.rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `free_algebra.pre R X`, the terms of which should be thought
  of as representatives for the elements of `free_algebra R X`.
  It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `free_algebra.rel R X` on `free_algebra.pre R X`.
  This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
  multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
  structure map for the algebra.
3. The free algebra `free_algebra R X` is the quotient of `free_algebra.pre R X` by
  the relation `free_algebra.rel R X`.
-/


variable (R : Type _) [CommSemiringₓ R]

variable (X : Type _)

namespace FreeAlgebra

/-- This inductive type is used to express representatives of the free algebra.
-/
inductive Pre
  | of : X → pre
  | of_scalar : R → pre
  | add : pre → pre → pre
  | mul : pre → pre → pre

namespace Pre

instance : Inhabited (Pre R X) :=
  ⟨of_scalar 0⟩

/-- Coercion from `X` to `pre R X`. Note: Used for notation only. -/
-- Note: These instances are only used to simplify the notation.
def hasCoeGenerator : Coe X (Pre R X) :=
  ⟨of⟩

/-- Coercion from `R` to `pre R X`. Note: Used for notation only. -/
def hasCoeSemiring : Coe R (Pre R X) :=
  ⟨of_scalar⟩

/-- Multiplication in `pre R X` defined as `pre.mul`. Note: Used for notation only. -/
def hasMul : Mul (Pre R X) :=
  ⟨mul⟩

/-- Addition in `pre R X` defined as `pre.add`. Note: Used for notation only. -/
def hasAdd : Add (Pre R X) :=
  ⟨add⟩

/-- Zero in `pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
def hasZero : Zero (Pre R X) :=
  ⟨of_scalar 0⟩

/-- One in `pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
def hasOne : One (Pre R X) :=
  ⟨of_scalar 1⟩

/-- Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
def hasSmul : HasSmul R (Pre R X) :=
  ⟨fun r m => mul (of_scalar r) m⟩

end Pre

attribute [local instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero pre.has_one pre.has_smul

/-- Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `pre R X` to `A`. This is mainly used in the construction of `free_algebra.lift`.
-/
def liftFun {A : Type _} [Semiringₓ A] [Algebra R A] (f : X → A) : Pre R X → A := fun t =>
  Pre.recOn t f (algebraMap _ _) (fun _ _ => (· + ·)) fun _ _ => (· * ·)

/-- An inductively defined relation on `pre R X` used to force the initial algebra structure on
the associated quotient.
-/
inductive Rel : Pre R X → Pre R X → Prop-- force `of_scalar` to be a central semiring morphism

  | add_scalar {r s : R} : rel (↑(r + s)) (↑r + ↑s)
  | mul_scalar {r s : R} : rel (↑(r * s)) (↑r * ↑s)
  | central_scalar {r : R} {a : Pre R X} : rel (r * a) (a * r)-- commutative additive semigroup

  | add_assocₓ {a b c : Pre R X} : rel (a + b + c) (a + (b + c))
  | add_commₓ {a b : Pre R X} : rel (a + b) (b + a)
  | zero_addₓ {a : Pre R X} : rel (0 + a) a-- multiplicative monoid

  | mul_assoc {a b c : Pre R X} : rel (a * b * c) (a * (b * c))
  | one_mulₓ {a : Pre R X} : rel (1 * a) a
  | mul_oneₓ {a : Pre R X} : rel (a * 1) a-- distributivity

  | left_distrib {a b c : Pre R X} : rel (a * (b + c)) (a * b + a * c)
  | right_distrib {a b c : Pre R X} : rel ((a + b) * c) (a * c + b * c)-- other relations needed for semiring

  | zero_mul {a : Pre R X} : rel (0 * a) 0
  | mul_zero {a : Pre R X} : rel (a * 0) 0-- compatibility

  | add_compat_left {a b c : Pre R X} : rel a b → rel (a + c) (b + c)
  | add_compat_right {a b c : Pre R X} : rel a b → rel (c + a) (c + b)
  | mul_compat_left {a b c : Pre R X} : rel a b → rel (a * c) (b * c)
  | mul_compat_right {a b c : Pre R X} : rel a b → rel (c * a) (c * b)

end FreeAlgebra

/-- The free algebra for the type `X` over the commutative semiring `R`.
-/
def FreeAlgebra :=
  Quot (FreeAlgebra.Rel R X)

namespace FreeAlgebra

attribute [local instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero pre.has_one pre.has_smul

instance : Semiringₓ (FreeAlgebra R X) where
  add := Quot.map₂ (· + ·) (fun _ _ _ => Rel.add_compat_right) fun _ _ _ => Rel.add_compat_left
  add_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.add_assoc
  zero := Quot.mk _ 0
  zero_add := by
    rintro ⟨⟩
    exact Quot.sound rel.zero_add
  add_zero := by
    rintro ⟨⟩
    change Quot.mk _ _ = _
    rw [Quot.sound rel.add_comm, Quot.sound rel.zero_add]
  add_comm := by
    rintro ⟨⟩ ⟨⟩
    exact Quot.sound rel.add_comm
  mul := Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_compat_right) fun _ _ _ => Rel.mul_compat_left
  mul_assoc := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.mul_assoc
  one := Quot.mk _ 1
  one_mul := by
    rintro ⟨⟩
    exact Quot.sound rel.one_mul
  mul_one := by
    rintro ⟨⟩
    exact Quot.sound rel.mul_one
  left_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.left_distrib
  right_distrib := by
    rintro ⟨⟩ ⟨⟩ ⟨⟩
    exact Quot.sound rel.right_distrib
  zero_mul := by
    rintro ⟨⟩
    exact Quot.sound rel.zero_mul
  mul_zero := by
    rintro ⟨⟩
    exact Quot.sound rel.mul_zero

instance : Inhabited (FreeAlgebra R X) :=
  ⟨0⟩

instance : HasSmul R (FreeAlgebra R X) where smul := fun r => Quot.map ((· * ·) ↑r) fun a b => Rel.mul_compat_right

instance : Algebra R (FreeAlgebra R X) where
  toFun := fun r => Quot.mk _ r
  map_one' := rfl
  map_mul' := fun _ _ => Quot.sound Rel.mul_scalar
  map_zero' := rfl
  map_add' := fun _ _ => Quot.sound Rel.add_scalar
  commutes' := fun _ => by
    rintro ⟨⟩
    exact Quot.sound rel.central_scalar
  smul_def' := fun _ _ => rfl

instance {S : Type _} [CommRingₓ S] : Ringₓ (FreeAlgebra S X) :=
  Algebra.semiringToRing S

variable {X}

/-- The canonical function `X → free_algebra R X`.
-/
def ι : X → FreeAlgebra R X := fun m => Quot.mk _ m

@[simp]
theorem quot_mk_eq_ι (m : X) : Quot.mk (FreeAlgebra.Rel R X) m = ι R m :=
  rfl

variable {A : Type _} [Semiringₓ A] [Algebra R A]

/-- Internal definition used to define `lift` -/
private def lift_aux (f : X → A) : FreeAlgebra R X →ₐ[R] A where
  toFun := fun a =>
    (Quot.liftOn a (liftFun _ _ f)) fun a b h => by
      induction h
      · exact (algebraMap R A).map_add h_r h_s
        
      · exact (algebraMap R A).map_mul h_r h_s
        
      · apply Algebra.commutes
        
      · change _ + _ + _ = _ + (_ + _)
        rw [add_assocₓ]
        
      · change _ + _ = _ + _
        rw [add_commₓ]
        
      · change algebraMap _ _ _ + lift_fun R X f _ = lift_fun R X f _
        simp
        
      · change _ * _ * _ = _ * (_ * _)
        rw [mul_assoc]
        
      · change algebraMap _ _ _ * lift_fun R X f _ = lift_fun R X f _
        simp
        
      · change lift_fun R X f _ * algebraMap _ _ _ = lift_fun R X f _
        simp
        
      · change _ * (_ + _) = _ * _ + _ * _
        rw [left_distrib]
        
      · change (_ + _) * _ = _ * _ + _ * _
        rw [right_distrib]
        
      · change algebraMap _ _ _ * _ = algebraMap _ _ _
        simp
        
      · change _ * algebraMap _ _ _ = algebraMap _ _ _
        simp
        
      repeat'
        change lift_fun R X f _ + lift_fun R X f _ = _
        rw [h_ih]
        rfl
      repeat'
        change lift_fun R X f _ * lift_fun R X f _ = _
        rw [h_ih]
        rfl
  map_one' := by
    change algebraMap _ _ _ = _
    simp
  map_mul' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  map_zero' := by
    change algebraMap _ _ _ = _
    simp
  map_add' := by
    rintro ⟨⟩ ⟨⟩
    rfl
  commutes' := by
    tauto

/-- Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `free_algebra R X → A`.
-/
def lift : (X → A) ≃ (FreeAlgebra R X →ₐ[R] A) where
  toFun := liftAux R
  invFun := fun F => F ∘ ι R
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun F => by
    ext x
    rcases x with ⟨⟩
    induction x
    case pre.of =>
      change ((F : FreeAlgebra R X → A) ∘ ι R) _ = _
      rfl
    case pre.of_scalar =>
      change algebraMap _ _ x = F (algebraMap _ _ x)
      rw [AlgHom.commutes F x]
    case pre.add a b ha hb =>
      change lift_aux R (F ∘ ι R) (Quot.mk _ _ + Quot.mk _ _) = F (Quot.mk _ _ + Quot.mk _ _)
      rw [AlgHom.map_add, AlgHom.map_add, ha, hb]
    case pre.mul a b ha hb =>
      change lift_aux R (F ∘ ι R) (Quot.mk _ _ * Quot.mk _ _) = F (Quot.mk _ _ * Quot.mk _ _)
      rw [AlgHom.map_mul, AlgHom.map_mul, ha, hb]

@[simp]
theorem lift_aux_eq (f : X → A) : liftAux R f = lift R f :=
  rfl

@[simp]
theorem lift_symm_apply (F : FreeAlgebra R X →ₐ[R] A) : (lift R).symm F = F ∘ ι R :=
  rfl

variable {R X}

@[simp]
theorem ι_comp_lift (f : X → A) : (lift R f : FreeAlgebra R X → A) ∘ ι R = f := by
  ext
  rfl

@[simp]
theorem lift_ι_apply (f : X → A) (x) : lift R f (ι R x) = f x :=
  rfl

@[simp]
theorem lift_unique (f : X → A) (g : FreeAlgebra R X →ₐ[R] A) : (g : FreeAlgebra R X → A) ∘ ι R = f ↔ g = lift R f :=
  (lift R).symm_apply_eq

/-!
At this stage we set the basic definitions as `@[irreducible]`, so from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden.

Of course, one still has the option to locally make these definitions `semireducible` if so desired,
and Lean is still willing in some circumstances to do unification based on the underlying
definition.
-/


-- Marking `free_algebra` irreducible makes `ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.
@[simp]
theorem lift_comp_ι (g : FreeAlgebra R X →ₐ[R] A) : lift R ((g : FreeAlgebra R X → A) ∘ ι R) = g := by
  rw [← lift_symm_apply]
  exact (lift R).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : FreeAlgebra R X →ₐ[R] A}
    (w : (f : FreeAlgebra R X → A) ∘ ι R = (g : FreeAlgebra R X → A) ∘ ι R) : f = g := by
  rw [← lift_symm_apply, ← lift_symm_apply] at w
  exact (lift R).symm.Injective w

/-- The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
noncomputable def equivMonoidAlgebraFreeMonoid : FreeAlgebra R X ≃ₐ[R] MonoidAlgebra R (FreeMonoid X) :=
  AlgEquiv.ofAlgHom (lift R fun x => (MonoidAlgebra.of R (FreeMonoid X)) (FreeMonoid.of x))
    ((MonoidAlgebra.lift R (FreeMonoid X) (FreeAlgebra R X)) (FreeMonoid.lift (ι R)))
    (by
      apply MonoidAlgebra.alg_hom_ext
      intro x
      apply FreeMonoid.recOn x
      · simp
        rfl
        
      · intro x y ih
        simp at ih
        simp [← ih]
        )
    (by
      ext
      simp )

instance [Nontrivial R] : Nontrivial (FreeAlgebra R X) :=
  equivMonoidAlgebraFreeMonoid.Surjective.Nontrivial

section

/-- The left-inverse of `algebra_map`. -/
def algebraMapInv : FreeAlgebra R X →ₐ[R] R :=
  lift R (0 : X → R)

theorem algebra_map_left_inverse : Function.LeftInverse algebraMapInv (algebraMap R <| FreeAlgebra R X) := fun x => by
  simp [← algebra_map_inv]

@[simp]
theorem algebra_map_inj (x y : R) : algebraMap R (FreeAlgebra R X) x = algebraMap R (FreeAlgebra R X) y ↔ x = y :=
  algebra_map_left_inverse.Injective.eq_iff

@[simp]
theorem algebra_map_eq_zero_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) algebra_map_left_inverse.Injective

@[simp]
theorem algebra_map_eq_one_iff (x : R) : algebraMap R (FreeAlgebra R X) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) algebra_map_left_inverse.Injective

-- this proof is copied from the approach in `free_abelian_group.of_injective`
theorem ι_injective [Nontrivial R] : Function.Injective (ι R : X → FreeAlgebra R X) := fun x y hoxy =>
  Classical.by_contradiction fun hxy : x ≠ y =>
    let f : FreeAlgebra R X →ₐ[R] R :=
      lift R fun z => by
        classical <;> exact if x = z then (1 : R) else 0
    have hfx1 : f (ι R x) = 1 := (lift_ι_apply _ _).trans <| if_pos rfl
    have hfy1 : f (ι R y) = 1 := hoxy ▸ hfx1
    have hfy0 : f (ι R y) = 0 := (lift_ι_apply _ _).trans <| if_neg hxy
    one_ne_zero <| hfy1.symm.trans hfy0

@[simp]
theorem ι_inj [Nontrivial R] (x y : X) : ι R x = ι R y ↔ x = y :=
  ι_injective.eq_iff

@[simp]
theorem ι_ne_algebra_map [Nontrivial R] (x : X) (r : R) : ι R x ≠ algebraMap R _ r := fun h => by
  let f0 : FreeAlgebra R X →ₐ[R] R := lift R 0
  let f1 : FreeAlgebra R X →ₐ[R] R := lift R 1
  have hf0 : f0 (ι R x) = 0 := lift_ι_apply _ _
  have hf1 : f1 (ι R x) = 1 := lift_ι_apply _ _
  rw [h, f0.commutes, Algebra.id.map_eq_self] at hf0
  rw [h, f1.commutes, Algebra.id.map_eq_self] at hf1
  exact zero_ne_one (hf0.symm.trans hf1)

@[simp]
theorem ι_ne_zero [Nontrivial R] (x : X) : ι R x ≠ 0 :=
  ι_ne_algebra_map x 0

@[simp]
theorem ι_ne_one [Nontrivial R] (x : X) : ι R x ≠ 1 :=
  ι_ne_algebra_map x 1

end

end FreeAlgebra

/- There is something weird in the above namespace that breaks the typeclass resolution of
`has_coe_to_sort` below. Closing it and reopening it fixes it... -/
namespace FreeAlgebra

/-- An induction principle for the free algebra.

If `C` holds for the `algebra_map` of `r : R` into `free_algebra R X`, the `ι` of `x : X`, and is
preserved under addition and muliplication, then it holds for all of `free_algebra R X`.
-/
@[elab_as_eliminator]
theorem induction {C : FreeAlgebra R X → Prop} (h_grade0 : ∀ r, C (algebraMap R (FreeAlgebra R X) r))
    (h_grade1 : ∀ x, C (ι R x)) (h_mul : ∀ a b, C a → C b → C (a * b)) (h_add : ∀ a b, C a → C b → C (a + b))
    (a : FreeAlgebra R X) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : Subalgebra R (FreeAlgebra R X) :=
    { Carrier := C, mul_mem' := h_mul, add_mem' := h_add, algebra_map_mem' := h_grade0 }
  let of : X → s := Subtype.coind (ι R) h_grade1
  -- the mapping through the subalgebra is the identity
  have of_id : AlgHom.id R (FreeAlgebra R X) = s.val.comp (lift R of) := by
    ext
    simp [← of, ← Subtype.coind]
  -- finding a proof is finding an element of the subalgebra
  convert Subtype.prop (lift R of a)
  simp [← AlgHom.ext_iff] at of_id
  exact of_id a

end FreeAlgebra

