/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.Algebra.Bilinear

/-!
# Towers of algebras

In this file we prove basic facts about towers of algebra.

An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

An important definition is `to_alg_hom R S A`, the canonical `R`-algebra homomorphism `S →ₐ[R] A`.

-/


open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable [AddCommMonoidₓ M] [Module R M] [Module A M] [IsScalarTower R A M]

variable {A}

/-- The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`
on the `R`-module `M`.

This is a stronger version of `distrib_mul_action.to_linear_map`, and could also have been
called `algebra.to_module_End`. -/
def lsmul : A →ₐ[R] Module.End R M where
  toFun := DistribMulAction.toLinearMap R M
  map_one' := LinearMap.ext fun _ => one_smul A _
  map_mul' := fun a b => LinearMap.ext <| smul_assoc a b
  map_zero' := LinearMap.ext fun _ => zero_smul A _
  map_add' := fun a b => LinearMap.ext fun _ => add_smul _ _ _
  commutes' := fun r => LinearMap.ext <| algebra_map_smul A r

@[simp]
theorem lsmul_coe (a : A) : (lsmul R M a : M → M) = (· • ·) a :=
  rfl

theorem lmul_algebra_map (x : R) : lmul R A (algebraMap R A x) = Algebra.lsmul R A x :=
  Eq.symm <| LinearMap.ext <| smul_def x

end Algebra

namespace IsScalarTower

section Module

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable [HasSmul R M] [MulAction A M] [IsScalarTower R A M]

variable {R} (A) {M}

theorem algebra_map_smul (r : R) (x : M) : algebraMap R A r • x = r • x := by
  rw [Algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

end Module

section Semiringₓ

variable [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable {R S A}

theorem of_algebra_map_eq [Algebra R A] (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) :
    IsScalarTower R S A :=
  ⟨fun x y z => by
    simp_rw [Algebra.smul_def, RingHom.map_mul, mul_assoc, h]⟩

/-- See note [partially-applied ext lemmas]. -/
theorem of_algebra_map_eq' [Algebra R A] (h : algebraMap R A = (algebraMap S A).comp (algebraMap R S)) :
    IsScalarTower R S A :=
  of_algebra_map_eq <| RingHom.ext_iff.1 h

variable (R S A)

instance subalgebra (S₀ : Subalgebra R S) : IsScalarTower S₀ S A :=
  of_algebra_map_eq fun x => rfl

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

theorem algebra_map_eq : algebraMap R A = (algebraMap S A).comp (algebraMap R S) :=
  RingHom.ext fun x => by
    simp_rw [RingHom.comp_apply, Algebra.algebra_map_eq_smul_one, smul_assoc, one_smul]

theorem algebra_map_apply (x : R) : algebraMap R A x = algebraMap S A (algebraMap R S x) := by
  rw [algebra_map_eq R S A, RingHom.comp_apply]

instance subalgebra' (S₀ : Subalgebra R S) : IsScalarTower R S₀ A :=
  (@IsScalarTower.of_algebra_map_eq R S₀ A _ _ _ _ _ _) fun _ => (IsScalarTower.algebra_map_apply R S A _ : _)

@[ext]
theorem Algebra.ext {S : Type u} {A : Type v} [CommSemiringₓ S] [Semiringₓ A] (h1 h2 : Algebra S A)
    (h :
      ∀ (r : S) (x : A),
        (have := h1
          r • x) =
          r • x) :
    h1 = h2 :=
  (Algebra.algebra_ext _ _) fun r => by
    simpa only [← @Algebra.smul_def _ _ _ _ h1, ← @Algebra.smul_def _ _ _ _ h2, ← mul_oneₓ] using h r 1

/-- In a tower, the canonical map from the middle element to the top element is an
algebra homomorphism over the bottom element. -/
def toAlgHom : S →ₐ[R] A :=
  { algebraMap S A with commutes' := fun _ => (algebra_map_apply _ _ _ _).symm }

theorem to_alg_hom_apply (y : S) : toAlgHom R S A y = algebraMap S A y :=
  rfl

@[simp]
theorem coe_to_alg_hom : ↑(toAlgHom R S A) = algebraMap S A :=
  RingHom.ext fun _ => rfl

@[simp]
theorem coe_to_alg_hom' : (toAlgHom R S A : S → A) = algebraMap S A :=
  rfl

variable {R S A B}

@[simp]
theorem _root_.alg_hom.map_algebra_map (f : A →ₐ[S] B) (r : R) : f (algebraMap R A r) = algebraMap R B r := by
  rw [algebra_map_apply R S A r, f.commutes, ← algebra_map_apply R S B]

variable (R)

@[simp]
theorem _root_.alg_hom.comp_algebra_map_of_tower (f : A →ₐ[S] B) :
    (f : A →+* B).comp (algebraMap R A) = algebraMap R B :=
  RingHom.ext f.map_algebra_map

variable (R) {S A B}

-- conflicts with is_scalar_tower.subalgebra
instance (priority := 999) subsemiring (U : Subsemiring S) : IsScalarTower U S A :=
  of_algebra_map_eq fun x => rfl

@[nolint instance_priority]
instance of_ring_hom {R A B : Type _} [CommSemiringₓ R] [CommSemiringₓ A] [CommSemiringₓ B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : @IsScalarTower R A B _ f.toRingHom.toAlgebra.toHasSmul _ := by
  let this := (f : A →+* B).toAlgebra
  exact of_algebra_map_eq fun x => (f.commutes x).symm

end Semiringₓ

end IsScalarTower

section Homs

variable [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R S] [Algebra S A] [Algebra S B]

variable [Algebra R A] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

variable (R) {A S B}

open IsScalarTower

namespace AlgHom

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=
  { (f : A →+* B) with
    commutes' := fun r => by
      rw [algebra_map_apply R S A, algebra_map_apply R S B]
      exact f.commutes (algebraMap R S r) }

theorem restrict_scalars_apply (f : A →ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl

@[simp]
theorem coe_restrict_scalars (f : A →ₐ[S] B) : (f.restrictScalars R : A →+* B) = f :=
  rfl

@[simp]
theorem coe_restrict_scalars' (f : A →ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl

theorem restrict_scalars_injective : Function.Injective (restrictScalars R : (A →ₐ[S] B) → A →ₐ[R] B) := fun f g h =>
  AlgHom.ext (AlgHom.congr_fun h : _)

end AlgHom

namespace AlgEquiv

/-- R ⟶ S induces S-Alg ⥤ R-Alg -/
def restrictScalars (f : A ≃ₐ[S] B) : A ≃ₐ[R] B :=
  { (f : A ≃+* B) with
    commutes' := fun r => by
      rw [algebra_map_apply R S A, algebra_map_apply R S B]
      exact f.commutes (algebraMap R S r) }

theorem restrict_scalars_apply (f : A ≃ₐ[S] B) (x : A) : f.restrictScalars R x = f x :=
  rfl

@[simp]
theorem coe_restrict_scalars (f : A ≃ₐ[S] B) : (f.restrictScalars R : A ≃+* B) = f :=
  rfl

@[simp]
theorem coe_restrict_scalars' (f : A ≃ₐ[S] B) : (restrictScalars R f : A → B) = f :=
  rfl

theorem restrict_scalars_injective : Function.Injective (restrictScalars R : (A ≃ₐ[S] B) → A ≃ₐ[R] B) := fun f g h =>
  AlgEquiv.ext (AlgEquiv.congr_fun h : _)

end AlgEquiv

end Homs

namespace Subalgebra

open IsScalarTower

section Semiringₓ

variable (R) {S A B} [CommSemiringₓ R] [CommSemiringₓ S] [Semiringₓ A] [Semiringₓ B]

variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]

variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A`, reinterpret
`U` as an `R`-subalgebra of `A`. -/
def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebra_map_mem' := fun x => by
      rw [algebra_map_apply R S A]
      exact U.algebra_map_mem _ }

@[simp]
theorem coe_restrict_scalars {U : Subalgebra S A} : (restrictScalars R U : Set A) = (U : Set A) :=
  rfl

@[simp]
theorem restrict_scalars_top : restrictScalars R (⊤ : Subalgebra S A) = ⊤ :=
  SetLike.coe_injective rfl

@[simp]
theorem restrict_scalars_to_submodule {U : Subalgebra S A} :
    (U.restrictScalars R).toSubmodule = U.toSubmodule.restrictScalars R :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_restrict_scalars {U : Subalgebra S A} {x : A} : x ∈ restrictScalars R U ↔ x ∈ U :=
  Iff.rfl

theorem restrict_scalars_injective : Function.Injective (restrictScalars R : Subalgebra S A → Subalgebra R A) :=
  fun U V H =>
  ext fun x => by
    rw [← mem_restrict_scalars R, H, mem_restrict_scalars]

/-- Produces an `R`-algebra map from `U.restrict_scalars R` given an `S`-algebra map from `U`.

This is a special case of `alg_hom.restrict_scalars` that can be helpful in elaboration. -/
@[simp]
def ofRestrictScalars (U : Subalgebra S A) (f : U →ₐ[S] B) : U.restrictScalars R →ₐ[R] B :=
  f.restrictScalars R

end Semiringₓ

end Subalgebra

namespace Algebra

variable {R A} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable {M} [AddCommMonoidₓ M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem span_restrict_scalars_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s).restrictScalars R = Submodule.span R s := by
  refine' le_antisymmₓ (fun x hx => _) (Submodule.span_subset_span _ _ _)
  refine' Submodule.span_induction hx _ _ _ _
  · exact fun x hx => Submodule.subset_span hx
    
  · exact Submodule.zero_mem _
    
  · exact fun x y => Submodule.add_mem _
    
  · intro c x hx
    obtain ⟨c', rfl⟩ := h c
    rw [IsScalarTower.algebra_map_smul]
    exact Submodule.smul_mem _ _ hx
    

theorem coe_span_eq_span_of_surjective (h : Function.Surjective (algebraMap R A)) (s : Set M) :
    (Submodule.span A s : Set M) = Submodule.span R s :=
  congr_arg coe (Algebra.span_restrict_scalars_eq_span_of_surjective h s)

end Algebra

namespace IsScalarTower

open Subalgebra

variable [CommSemiringₓ R] [CommSemiringₓ S] [CommSemiringₓ A]

variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem adjoin_range_to_alg_hom (t : Set A) :
    (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R = (Algebra.adjoin S t).restrictScalars R :=
  Subalgebra.ext fun z =>
    show
      z ∈ Subsemiring.closure (Set.Range (algebraMap (toAlgHom R S A).range A) ∪ t : Set A) ↔
        z ∈ Subsemiring.closure (Set.Range (algebraMap S A) ∪ t : Set A)
      by
      suffices Set.Range (algebraMap (toAlgHom R S A).range A) = Set.Range (algebraMap S A) by
        rw [this]
      ext z
      exact ⟨fun ⟨⟨x, y, h1⟩, h2⟩ => ⟨y, h2 ▸ h1⟩, fun ⟨y, hy⟩ => ⟨⟨z, y, hy⟩, rfl⟩⟩

end IsScalarTower

section Semiringₓ

variable {R S A}

namespace Submodule

section Module

variable [Semiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A]

variable [Module R S] [Module S A] [Module R A] [IsScalarTower R S A]

open IsScalarTower

theorem smul_mem_span_smul_of_mem {s : Set S} {t : Set A} {k : S} (hks : k ∈ span R s) {x : A} (hx : x ∈ t) :
    k • x ∈ span R (s • t) :=
  span_induction hks (fun c hc => subset_span <| Set.mem_smul.2 ⟨c, x, hc, hx, rfl⟩)
    (by
      rw [zero_smul]
      exact zero_mem _)
    (fun c₁ c₂ ih₁ ih₂ => by
      rw [add_smul]
      exact add_mem ih₁ ih₂)
    fun b c hc => by
    rw [IsScalarTower.smul_assoc]
    exact smul_mem _ _ hc

variable [SmulCommClass R S A]

theorem smul_mem_span_smul {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A} (hx : x ∈ span R t) :
    k • x ∈ span R (s • t) :=
  span_induction hx (fun x hx => smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hx)
    (by
      rw [smul_zero]
      exact zero_mem _)
    (fun x y ihx ihy => by
      rw [smul_add]
      exact add_mem ihx ihy)
    fun c x hx => smul_comm c k x ▸ smul_mem _ _ hx

theorem smul_mem_span_smul' {s : Set S} (hs : span R s = ⊤) {t : Set A} {k : S} {x : A} (hx : x ∈ span R (s • t)) :
    k • x ∈ span R (s • t) :=
  span_induction hx
    (fun x hx => by
      let ⟨p, q, hp, hq, hpq⟩ := Set.mem_smul.1 hx
      rw [← hpq, smul_smul]
      exact smul_mem_span_smul_of_mem (hs.symm ▸ mem_top) hq)
    (by
      rw [smul_zero]
      exact zero_mem _)
    (fun x y ihx ihy => by
      rw [smul_add]
      exact add_mem ihx ihy)
    fun c x hx => smul_comm c k x ▸ smul_mem _ _ hx

theorem span_smul {s : Set S} (hs : span R s = ⊤) (t : Set A) : span R (s • t) = (span S t).restrictScalars R :=
  (le_antisymmₓ
      (span_le.2 fun x hx =>
        let ⟨p, q, hps, hqt, hpqx⟩ := Set.mem_smul.1 hx
        hpqx ▸ (span S t).smul_mem p (subset_span hqt)))
    fun p hp =>
    span_induction hp (fun x hx => one_smul S x ▸ smul_mem_span_smul hs (subset_span hx)) (zero_mem _)
      (fun _ _ => add_mem) fun k x hx => smul_mem_span_smul' hs hx

end Module

section Algebra

variable [CommSemiringₓ R] [Semiringₓ S] [AddCommMonoidₓ A]

variable [Algebra R S] [Module S A] [Module R A] [IsScalarTower R S A]

/-- A variant of `submodule.span_image` for `algebra_map`. -/
theorem span_algebra_map_image (a : Set R) :
    Submodule.span R (algebraMap R S '' a) = (Submodule.span R a).map (Algebra.linearMap R S) :=
  (Submodule.span_image <| Algebra.linearMap R S).trans rfl

theorem span_algebra_map_image_of_tower {S T : Type _} [CommSemiringₓ S] [Semiringₓ T] [Module R S]
    [IsScalarTower R S S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (a : Set S) :
    Submodule.span R (algebraMap S T '' a) = (Submodule.span R a).map ((Algebra.linearMap S T).restrictScalars R) :=
  (Submodule.span_image <| (Algebra.linearMap S T).restrictScalars R).trans rfl

theorem map_mem_span_algebra_map_image {S T : Type _} [CommSemiringₓ S] [Semiringₓ T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (x : S) (a : Set S) (hx : x ∈ Submodule.span R a) :
    algebraMap S T x ∈ Submodule.span R (algebraMap S T '' a) := by
  rw [span_algebra_map_image_of_tower, mem_map]
  exact ⟨x, hx, rfl⟩

end Algebra

end Submodule

end Semiringₓ

section Ringₓ

namespace Algebra

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A]

variable [AddCommGroupₓ M] [Module A M] [Module R M] [IsScalarTower R A M]

theorem lsmul_injective [NoZeroSmulDivisors A M] {x : A} (hx : x ≠ 0) : Function.Injective (lsmul R M x) :=
  smul_right_injective _ hx

end Algebra

end Ringₓ

