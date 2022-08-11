/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.Algebra.Lie.IdealOperations

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `lie_module.is_trivial`
  * `is_lie_abelian`
  * `commutative_ring_iff_abelian_lie_ring`
  * `lie_module.ker`
  * `lie_module.max_triv_submodule`
  * `lie_algebra.center`

## Tags

lie algebra, abelian, commutative, center
-/


universe u v w w₁ w₂

/-- A Lie (ring) module is trivial iff all brackets vanish. -/
class LieModule.IsTrivial (L : Type v) (M : Type w) [HasBracket L M] [Zero M] : Prop where
  trivial : ∀ (x : L) (m : M), ⁅x,m⁆ = 0

@[simp]
theorem trivial_lie_zero (L : Type v) (M : Type w) [HasBracket L M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) :
    ⁅x,m⁆ = 0 :=
  LieModule.IsTrivial.trivial x m

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
abbrev IsLieAbelian (L : Type v) [HasBracket L L] [Zero L] : Prop :=
  LieModule.IsTrivial L L

instance LieIdeal.is_lie_abelian_of_trivial (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [h : LieModule.IsTrivial L I] :
    IsLieAbelian I where trivial := fun x y => by
    apply h.trivial

theorem Function.Injective.is_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRingₓ R] [LieRing L₁]
    [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂} (h₁ : Function.Injective f)
    (h₂ : IsLieAbelian L₂) : IsLieAbelian L₁ :=
  { trivial := fun x y =>
      h₁ <|
        calc
          f ⁅x,y⁆ = ⁅f x,f y⁆ := LieHom.map_lie f x y
          _ = 0 := trivial_lie_zero _ _ _ _
          _ = f 0 := f.map_zero.symm
           }

theorem Function.Surjective.is_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRingₓ R] [LieRing L₁]
    [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂} (h₁ : Function.Surjective f)
    (h₂ : IsLieAbelian L₁) : IsLieAbelian L₂ :=
  { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie, trivial_lie_zero, LieHom.map_zero] }

theorem lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRingₓ R] [LieRing L₁]
    [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) : IsLieAbelian L₁ ↔ IsLieAbelian L₂ :=
  ⟨e.symm.Injective.IsLieAbelian, e.Injective.IsLieAbelian⟩

theorem commutative_ring_iff_abelian_lie_ring {A : Type v} [Ringₓ A] : IsCommutative A (· * ·) ↔ IsLieAbelian A := by
  have h₁ : IsCommutative A (· * ·) ↔ ∀ a b : A, a * b = b * a := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  have h₂ : IsLieAbelian A ↔ ∀ a b : A, ⁅a,b⁆ = 0 := ⟨fun h => h.1, fun h => ⟨h⟩⟩
  simp only [← h₁, ← h₂, ← LieRing.of_associative_ring_bracket, ← sub_eq_zero]

theorem LieAlgebra.is_lie_abelian_bot (R : Type u) (L : Type v) [CommRingₓ R] [LieRing L] [LieAlgebra R L] :
    IsLieAbelian (⊥ : LieIdeal R L) :=
  ⟨fun ⟨x, hx⟩ _ => by
    convert zero_lie _⟩

section Center

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L]

variable [AddCommGroupₓ M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable [AddCommGroupₓ N] [Module R N] [LieRingModule L N] [LieModule R L N]

namespace LieModule

/-- The kernel of the action of a Lie algebra `L` on a Lie module `M` as a Lie ideal in `L`. -/
protected def ker : LieIdeal R L :=
  (toEndomorphism R L M).ker

@[simp]
protected theorem mem_ker (x : L) : x ∈ LieModule.ker R L M ↔ ∀ m : M, ⁅x,m⁆ = 0 := by
  simp only [← LieModule.ker, ← LieHom.mem_ker, ← LinearMap.ext_iff, ← LinearMap.zero_apply, ←
    to_endomorphism_apply_apply]

/-- The largest submodule of a Lie module `M` on which the Lie algebra `L` acts trivially. -/
def maxTrivSubmodule : LieSubmodule R L M where
  Carrier := { m | ∀ x : L, ⁅x,m⁆ = 0 }
  zero_mem' := fun x => lie_zero x
  add_mem' := fun x y hx hy z => by
    rw [lie_add, hx, hy, add_zeroₓ]
  smul_mem' := fun c x hx y => by
    rw [lie_smul, hx, smul_zero]
  lie_mem := fun x m hm y => by
    rw [hm, lie_zero]

@[simp]
theorem mem_max_triv_submodule (m : M) : m ∈ maxTrivSubmodule R L M ↔ ∀ x : L, ⁅x,m⁆ = 0 :=
  Iff.rfl

instance : IsTrivial L (maxTrivSubmodule R L M) where trivial := fun x m => Subtype.ext (m.property x)

@[simp]
theorem ideal_oper_max_triv_submodule_eq_bot (I : LieIdeal R L) : ⁅I,maxTrivSubmodule R L M⁆ = ⊥ := by
  rw [← LieSubmodule.coe_to_submodule_eq_iff, LieSubmodule.lie_ideal_oper_eq_linear_span,
    LieSubmodule.bot_coe_submodule, Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x

theorem le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} :
    N ≤ maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L),N⁆ = ⊥ := by
  refine' ⟨fun h => _, fun h m hm => _⟩
  · rw [← le_bot_iff, ← ideal_oper_max_triv_submodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right _ _ ⊤ h
    
  · rw [mem_max_triv_submodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm
    

theorem trivial_iff_le_maximal_trivial (N : LieSubmodule R L M) : IsTrivial L N ↔ N ≤ maxTrivSubmodule R L M :=
  ⟨fun h m hm x => IsTrivial.dcasesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩

theorem is_trivial_iff_max_triv_eq_top : IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤ := by
  constructor
  · rintro ⟨h⟩
    ext
    simp only [← mem_max_triv_submodule, ← h, ← forall_const, ← true_iffₓ, ← eq_self_iff_true]
    
  · intro h
    constructor
    intro x m
    revert x
    rw [← mem_max_triv_submodule R L M, h]
    exact LieSubmodule.mem_top m
    

variable {R L M N}

/-- `max_triv_submodule` is functorial. -/
def maxTrivHom (f : M →ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M →ₗ⁅R,L⁆ maxTrivSubmodule R L N where
  toFun := fun m =>
    ⟨f m, fun x =>
      (LieModuleHom.map_lie _ _ _).symm.trans <| (congr_arg f (m.property x)).trans (LieModuleHom.map_zero _)⟩
  map_add' := fun m n => by
    simpa
  map_smul' := fun t m => by
    simpa
  map_lie' := fun x m => by
    simp

@[norm_cast, simp]
theorem coe_max_triv_hom_apply (f : M →ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) : (maxTrivHom f m : N) = f m :=
  rfl

/-- The maximal trivial submodules of Lie-equivalent Lie modules are Lie-equivalent. -/
def maxTrivEquiv (e : M ≃ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ≃ₗ⁅R,L⁆ maxTrivSubmodule R L N :=
  { maxTrivHom (e : M →ₗ⁅R,L⁆ N) with toFun := maxTrivHom (e : M →ₗ⁅R,L⁆ N),
    invFun := maxTrivHom (e.symm : N →ₗ⁅R,L⁆ M),
    left_inv := fun m => by
      ext
      simp ,
    right_inv := fun n => by
      ext
      simp }

@[norm_cast, simp]
theorem coe_max_triv_equiv_apply (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) : (maxTrivEquiv e m : N) = e ↑m :=
  rfl

@[simp]
theorem max_triv_equiv_of_refl_eq_refl : maxTrivEquiv (LieModuleEquiv.refl : M ≃ₗ⁅R,L⁆ M) = LieModuleEquiv.refl := by
  ext
  simp only [← coe_max_triv_equiv_apply, ← LieModuleEquiv.refl_apply]

@[simp]
theorem max_triv_equiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) : (maxTrivEquiv e).symm = maxTrivEquiv e.symm :=
  rfl

/-- A linear map between two Lie modules is a morphism of Lie modules iff the Lie algebra action
on it is trivial. -/
def maxTrivLinearMapEquivLieModuleHom : maxTrivSubmodule R L (M →ₗ[R] N) ≃ₗ[R] M →ₗ⁅R,L⁆ N where
  toFun := fun f =>
    { toLinearMap := f.val,
      map_lie' := fun x m => by
        have hf : ⁅x,f.val⁆ m = 0 := by
          rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply, sub_eq_zero, ← LinearMap.to_fun_eq_coe] at hf
        exact hf.symm }
  map_add' := fun f g => by
    ext
    simp
  map_smul' := fun F G => by
    ext
    simp
  invFun := fun F =>
    ⟨F, fun x => by
      ext
      simp ⟩
  left_inv := fun f => by
    simp
  right_inv := fun F => by
    simp

@[simp]
theorem coe_max_triv_linear_map_equiv_lie_module_hom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom f : M → N) = f := by
  ext
  rfl

@[simp]
theorem coe_max_triv_linear_map_equiv_lie_module_hom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom.symm f : M → N) = f :=
  rfl

@[simp]
theorem coe_linear_map_max_triv_linear_map_equiv_lie_module_hom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom f : M →ₗ[R] N) = (f : M →ₗ[R] N) := by
  ext
  rfl

@[simp]
theorem coe_linear_map_max_triv_linear_map_equiv_lie_module_hom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom.symm f : M →ₗ[R] N) = (f : M →ₗ[R] N) :=
  rfl

end LieModule

namespace LieAlgebra

/-- The center of a Lie algebra is the set of elements that commute with everything. It can
be viewed as the maximal trivial submodule of the Lie algebra as a Lie module over itself via the
adjoint representation. -/
abbrev center : LieIdeal R L :=
  LieModule.maxTrivSubmodule R L L

instance : IsLieAbelian (center R L) :=
  inferInstance

@[simp]
theorem ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L :=
  rfl

@[simp]
theorem self_module_ker_eq_center : LieModule.ker R L L = center R L := by
  ext y
  simp only [← LieModule.mem_max_triv_submodule, ← LieModule.mem_ker, lie_skew _ y, ← neg_eq_zero]

theorem abelian_of_le_center (I : LieIdeal R L) (h : I ≤ center R L) : IsLieAbelian I := by
  have : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  exact LieIdeal.is_lie_abelian_of_trivial R L I

theorem is_lie_abelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤ :=
  LieModule.is_trivial_iff_max_triv_eq_top R L L

end LieAlgebra

end Center

section IdealOperations

open LieSubmodule LieSubalgebra

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

@[simp]
theorem LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I,N⁆ = ⊥ := by
  suffices : ⁅I,N⁆ ≤ ⊥
  exact le_bot_iff.mp this
  rw [lie_ideal_oper_eq_span, LieSubmodule.lie_span_le]
  rintro m ⟨x, n, h⟩
  rw [trivial_lie_zero] at h
  simp [h]

theorem LieSubmodule.lie_abelian_iff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I,I⁆ = ⊥ := by
  simp only [← _root_.eq_bot_iff, ← lie_ideal_oper_eq_span, ← LieSubmodule.lie_span_le, ← LieSubmodule.bot_coe, ←
    Set.subset_singleton_iff, ← Set.mem_set_of_eq, ← exists_imp_distrib]
  refine'
    ⟨fun h z x y hz =>
      hz.symm.trans
        ((LieSubalgebra.coe_bracket _ _ _).symm.trans
          ((coe_zero_iff_zero _ _).mpr
            (by
              apply h.trivial))),
      fun h => ⟨fun x y => (coe_zero_iff_zero _ _).mp (h _ x y rfl)⟩⟩

end IdealOperations

