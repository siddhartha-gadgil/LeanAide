/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.GroupRingAction
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Equivariant homomorphisms

## Main definitions

* `mul_action_hom M X Y`, the type of equivariant functions from `X` to `Y`, where `M` is a monoid
  that acts on the types `X` and `Y`.
* `distrib_mul_action_hom M A B`, the type of equivariant additive monoid homomorphisms
  from `A` to `B`, where `M` is a monoid that acts on the additive monoids `A` and `B`.
* `mul_semiring_action_hom M R S`, the type of equivariant ring homomorphisms
  from `R` to `S`, where `M` is a monoid that acts on the rings `R` and `S`.

The above types have corresponding classes:
* `smul_hom_class F M X Y` states that `F` is a type of bundled `X → Y` homs
  preserving scalar multiplication by `M`
* `distrib_mul_action_hom_class F M A B` states that `F` is a type of bundled `A → B` homs
  preserving the additive monoid structure and scalar multiplication by `M`
* `mul_semiring_action_hom_class F M R S` states that `F` is a type of bundled `R → S` homs
  preserving the ring structure and scalar multiplication by `M`

## Notations

* `X →[M] Y` is `mul_action_hom M X Y`.
* `A →+[M] B` is `distrib_mul_action_hom M A B`.
* `R →+*[M] S` is `mul_semiring_action_hom M R S`.

-/


variable (M' : Type _)

variable (X : Type _) [HasSmul M' X]

variable (Y : Type _) [HasSmul M' Y]

variable (Z : Type _) [HasSmul M' Z]

variable (M : Type _) [Monoidₓ M]

variable (A : Type _) [AddMonoidₓ A] [DistribMulAction M A]

variable (A' : Type _) [AddGroupₓ A'] [DistribMulAction M A']

variable (B : Type _) [AddMonoidₓ B] [DistribMulAction M B]

variable (B' : Type _) [AddGroupₓ B'] [DistribMulAction M B']

variable (C : Type _) [AddMonoidₓ C] [DistribMulAction M C]

variable (R : Type _) [Semiringₓ R] [MulSemiringAction M R]

variable (R' : Type _) [Ringₓ R'] [MulSemiringAction M R']

variable (S : Type _) [Semiringₓ S] [MulSemiringAction M S]

variable (S' : Type _) [Ringₓ S'] [MulSemiringAction M S']

variable (T : Type _) [Semiringₓ T] [MulSemiringAction M T]

variable (G : Type _) [Groupₓ G] (H : Subgroup G)

/-- Equivariant functions. -/
@[nolint has_inhabited_instance]
structure MulActionHom where
  toFun : X → Y
  map_smul' : ∀ (m : M') (x : X), to_fun (m • x) = m • to_fun x

-- mathport name: «expr →[ ] »
notation:25 X " →[" M:25 "] " Y:0 => MulActionHom M X Y

/-- `smul_hom_class F M X Y` states that `F` is a type of morphisms preserving
scalar multiplication by `M`.

You should extend this class when you extend `mul_action_hom`. -/
class SmulHomClass (F : Type _) (M X Y : outParam <| Type _) [HasSmul M X] [HasSmul M Y] extends
  FunLike F X fun _ => Y where
  map_smul : ∀ (f : F) (c : M) (x : X), f (c • x) = c • f x

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] SmulHomClass.toFunLike

export SmulHomClass (map_smul)

attribute [simp] map_smul

namespace MulActionHom

instance : CoeFun (X →[M'] Y) fun _ => X → Y :=
  ⟨MulActionHom.toFun⟩

instance : SmulHomClass (X →[M'] Y) M' X Y where
  coe := MulActionHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_smul := MulActionHom.map_smul'

variable {M M' X Y}

protected theorem map_smul (f : X →[M'] Y) (m : M') (x : X) : f (m • x) = m • f x :=
  map_smul _ _ _

@[ext]
theorem ext : ∀ {f g : X →[M'] Y}, (∀ x, f x = g x) → f = g :=
  FunLike.ext

theorem ext_iff {f g : X →[M'] Y} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

protected theorem congr_fun {f g : X →[M'] Y} (h : f = g) (x : X) : f x = g x :=
  FunLike.congr_fun h _

variable (M M') {X}

/-- The identity map as an equivariant map. -/
protected def id : X →[M'] X :=
  ⟨id, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : X) : MulActionHom.id M' x = x :=
  rfl

variable {M M' X Y Z}

/-- Composition of two equivariant maps. -/
def comp (g : Y →[M'] Z) (f : X →[M'] Y) : X →[M'] Z :=
  ⟨g ∘ f, fun m x =>
    calc
      g (f (m • x)) = g (m • f x) := by
        rw [f.map_smul]
      _ = m • g (f x) := g.map_smul _ _
      ⟩

@[simp]
theorem comp_apply (g : Y →[M'] Z) (f : X →[M'] Y) (x : X) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : X →[M'] Y) : (MulActionHom.id M').comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : X →[M'] Y) : f.comp (MulActionHom.id M') = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

variable {A B}

/-- The inverse of a bijective equivariant map is equivariant. -/
@[simps]
def inverse (f : A →[M] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →[M] A where
  toFun := g
  map_smul' := fun m x =>
    calc
      g (m • x) = g (m • f (g x)) := by
        rw [h₂]
      _ = g (f (m • g x)) := by
        rw [f.map_smul]
      _ = m • g x := by
        rw [h₁]
      

end MulActionHom

/-- Equivariant additive monoid homomorphisms. -/
structure DistribMulActionHom extends A →[M] B, A →+ B

/-- Reinterpret an equivariant additive monoid homomorphism as an additive monoid homomorphism. -/
add_decl_doc DistribMulActionHom.toAddMonoidHom

/-- Reinterpret an equivariant additive monoid homomorphism as an equivariant function. -/
add_decl_doc DistribMulActionHom.toMulActionHom

-- mathport name: «expr →+[ ] »
notation:25 A " →+[" M:25 "] " B:0 => DistribMulActionHom M A B

/-- `distrib_mul_action_hom_class F M A B` states that `F` is a type of morphisms preserving
the additive monoid structure and scalar multiplication by `M`.

You should extend this class when you extend `distrib_mul_action_hom`. -/
class DistribMulActionHomClass (F : Type _) (M A B : outParam <| Type _) [Monoidₓ M] [AddMonoidₓ A] [AddMonoidₓ B]
  [DistribMulAction M A] [DistribMulAction M B] extends SmulHomClass F M A B, AddMonoidHomClass F A B

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] DistribMulActionHomClass.toAddMonoidHomClass

namespace DistribMulActionHom

instance hasCoe : Coe (A →+[M] B) (A →+ B) :=
  ⟨toAddMonoidHom⟩

instance hasCoe' : Coe (A →+[M] B) (A →[M] B) :=
  ⟨toMulActionHom⟩

instance : CoeFun (A →+[M] B) fun _ => A → B :=
  ⟨toFun⟩

instance : DistribMulActionHomClass (A →+[M] B) M A B where
  coe := DistribMulActionHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_smul := DistribMulActionHom.map_smul'
  map_zero := DistribMulActionHom.map_zero'
  map_add := DistribMulActionHom.map_add'

variable {M A B}

@[simp]
theorem to_fun_eq_coe (f : A →+[M] B) : f.toFun = ⇑f :=
  rfl

@[norm_cast]
theorem coe_fn_coe (f : A →+[M] B) : ((f : A →+ B) : A → B) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : A →+[M] B) : ((f : A →[M] B) : A → B) = f :=
  rfl

@[ext]
theorem ext : ∀ {f g : A →+[M] B}, (∀ x, f x = g x) → f = g :=
  FunLike.ext

theorem ext_iff {f g : A →+[M] B} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

protected theorem congr_fun {f g : A →+[M] B} (h : f = g) (x : A) : f x = g x :=
  FunLike.congr_fun h _

theorem to_mul_action_hom_injective {f g : A →+[M] B} (h : (f : A →[M] B) = (g : A →[M] B)) : f = g := by
  ext a
  exact MulActionHom.congr_fun h a

theorem to_add_monoid_hom_injective {f g : A →+[M] B} (h : (f : A →+ B) = (g : A →+ B)) : f = g := by
  ext a
  exact AddMonoidHom.congr_fun h a

protected theorem map_zero (f : A →+[M] B) : f 0 = 0 :=
  map_zero _

protected theorem map_add (f : A →+[M] B) (x y : A) : f (x + y) = f x + f y :=
  map_add _ _ _

protected theorem map_neg (f : A' →+[M] B') (x : A') : f (-x) = -f x :=
  map_neg _ _

protected theorem map_sub (f : A' →+[M] B') (x y : A') : f (x - y) = f x - f y :=
  map_sub _ _ _

protected theorem map_smul (f : A →+[M] B) (m : M) (x : A) : f (m • x) = m • f x :=
  map_smul _ _ _

variable (M) {A}

/-- The identity map as an equivariant additive monoid homomorphism. -/
protected def id : A →+[M] A :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : A) : DistribMulActionHom.id M x = x :=
  rfl

variable {M A B C}

instance : Zero (A →+[M] B) :=
  ⟨{ (0 : A →+ B) with
      map_smul' := by
        simp }⟩

instance : One (A →+[M] A) :=
  ⟨DistribMulActionHom.id M⟩

@[simp]
theorem coe_zero : ((0 : A →+[M] B) : A → B) = 0 :=
  rfl

@[simp]
theorem coe_one : ((1 : A →+[M] A) : A → A) = id :=
  rfl

theorem zero_apply (a : A) : (0 : A →+[M] B) a = 0 :=
  rfl

theorem one_apply (a : A) : (1 : A →+[M] A) a = a :=
  rfl

instance : Inhabited (A →+[M] B) :=
  ⟨0⟩

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : B →+[M] C) (f : A →+[M] B) : A →+[M] C :=
  { MulActionHom.comp (g : B →[M] C) (f : A →[M] B), AddMonoidHom.comp (g : B →+ C) (f : A →+ B) with }

@[simp]
theorem comp_apply (g : B →+[M] C) (f : A →+[M] B) (x : A) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : A →+[M] B) : (DistribMulActionHom.id M).comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : A →+[M] B) : f.comp (DistribMulActionHom.id M) = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

/-- The inverse of a bijective `distrib_mul_action_hom` is a `distrib_mul_action_hom`. -/
@[simps]
def inverse (f : A →+[M] B) (g : B → A) (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →+[M] A :=
  { (f : A →+ B).inverse g h₁ h₂, (f : A →[M] B).inverse g h₁ h₂ with toFun := g }

section Semiringₓ

variable {R M'} [AddMonoidₓ M'] [DistribMulAction R M']

@[ext]
theorem ext_ring {f g : R →+[R] M'} (h : f 1 = g 1) : f = g := by
  ext x
  rw [← mul_oneₓ x, ← smul_eq_mul R, f.map_smul, g.map_smul, h]

theorem ext_ring_iff {f g : R →+[R] M'} : f = g ↔ f 1 = g 1 :=
  ⟨fun h => h ▸ rfl, ext_ring⟩

end Semiringₓ

end DistribMulActionHom

/-- Equivariant ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure MulSemiringActionHom extends R →+[M] S, R →+* S

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc MulSemiringActionHom.toRingHom

/-- Reinterpret an equivariant ring homomorphism as an equivariant additive monoid homomorphism. -/
add_decl_doc MulSemiringActionHom.toDistribMulActionHom

-- mathport name: «expr →+*[ ] »
notation:25 R " →+*[" M:25 "] " S:0 => MulSemiringActionHom M R S

/-- `mul_semiring_action_hom_class F M R S` states that `F` is a type of morphisms preserving
the ring structure and scalar multiplication by `M`.

You should extend this class when you extend `mul_semiring_action_hom`. -/
class MulSemiringActionHomClass (F : Type _) (M R S : outParam <| Type _) [Monoidₓ M] [Semiringₓ R] [Semiringₓ S]
  [DistribMulAction M R] [DistribMulAction M S] extends DistribMulActionHomClass F M R S, RingHomClass F R S

-- `M` becomes a metavariable but it's an `out_param` so it's not a problem.
attribute [nolint dangerous_instance] MulSemiringActionHomClass.toRingHomClass

namespace MulSemiringActionHom

instance hasCoe : Coe (R →+*[M] S) (R →+* S) :=
  ⟨toRingHom⟩

instance hasCoe' : Coe (R →+*[M] S) (R →+[M] S) :=
  ⟨toDistribMulActionHom⟩

instance : CoeFun (R →+*[M] S) fun _ => R → S :=
  ⟨fun c => c.toFun⟩

instance : MulSemiringActionHomClass (R →+*[M] S) M R S where
  coe := MulSemiringActionHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_smul := MulSemiringActionHom.map_smul'
  map_zero := MulSemiringActionHom.map_zero'
  map_add := MulSemiringActionHom.map_add'
  map_one := MulSemiringActionHom.map_one'
  map_mul := MulSemiringActionHom.map_mul'

variable {M R S}

@[norm_cast]
theorem coe_fn_coe (f : R →+*[M] S) : ((f : R →+* S) : R → S) = f :=
  rfl

@[norm_cast]
theorem coe_fn_coe' (f : R →+*[M] S) : ((f : R →+[M] S) : R → S) = f :=
  rfl

@[ext]
theorem ext : ∀ {f g : R →+*[M] S}, (∀ x, f x = g x) → f = g :=
  FunLike.ext

theorem ext_iff {f g : R →+*[M] S} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

protected theorem map_zero (f : R →+*[M] S) : f 0 = 0 :=
  map_zero _

protected theorem map_add (f : R →+*[M] S) (x y : R) : f (x + y) = f x + f y :=
  map_add _ _ _

protected theorem map_neg (f : R' →+*[M] S') (x : R') : f (-x) = -f x :=
  map_neg _ _

protected theorem map_sub (f : R' →+*[M] S') (x y : R') : f (x - y) = f x - f y :=
  map_sub _ _ _

protected theorem map_one (f : R →+*[M] S) : f 1 = 1 :=
  map_one _

protected theorem map_mul (f : R →+*[M] S) (x y : R) : f (x * y) = f x * f y :=
  map_mul _ _ _

protected theorem map_smul (f : R →+*[M] S) (m : M) (x : R) : f (m • x) = m • f x :=
  map_smul _ _ _

variable (M) {R}

/-- The identity map as an equivariant ring homomorphism. -/
protected def id : R →+*[M] R :=
  ⟨id, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, fun _ _ => rfl⟩

@[simp]
theorem id_apply (x : R) : MulSemiringActionHom.id M x = x :=
  rfl

variable {M R S T}

/-- Composition of two equivariant additive monoid homomorphisms. -/
def comp (g : S →+*[M] T) (f : R →+*[M] S) : R →+*[M] T :=
  { DistribMulActionHom.comp (g : S →+[M] T) (f : R →+[M] S), RingHom.comp (g : S →+* T) (f : R →+* S) with }

@[simp]
theorem comp_apply (g : S →+*[M] T) (f : R →+*[M] S) (x : R) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem id_comp (f : R →+*[M] S) : (MulSemiringActionHom.id M).comp f = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

@[simp]
theorem comp_id (f : R →+*[M] S) : f.comp (MulSemiringActionHom.id M) = f :=
  ext fun x => by
    rw [comp_apply, id_apply]

end MulSemiringActionHom

section

variable (M) {R'} (U : Subring R') [IsInvariantSubring M U]

/-- The canonical inclusion from an invariant subring. -/
def IsInvariantSubring.subtypeHom : U →+*[M] R' :=
  { U.Subtype with map_smul' := fun m s => rfl }

@[simp]
theorem IsInvariantSubring.coe_subtype_hom : (IsInvariantSubring.subtypeHom M U : U → R') = coe :=
  rfl

@[simp]
theorem IsInvariantSubring.coe_subtype_hom' : (IsInvariantSubring.subtypeHom M U : U →+* R') = U.Subtype :=
  rfl

end

