/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.Algebra.Lie.Submodule
import Mathbin.Algebra.Lie.OfAssociative
import Mathbin.LinearAlgebra.Isomorphisms

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `lie_submodule.quotient.lie_quotient_lie_module`
  * `lie_submodule.quotient.lie_quotient_lie_algebra`

## Tags

lie algebra, quotient
-/


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [AddCommGroupₓ M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

variable (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
instance : HasQuotient M (LieSubmodule R L M) :=
  ⟨fun N => M ⧸ N.toSubmodule⟩

namespace Quotientₓ

variable {N I}

instance addCommGroup : AddCommGroupₓ (M ⧸ N) :=
  Submodule.Quotient.addCommGroup _

instance module' {S : Type _} [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] : Module S (M ⧸ N) :=
  Submodule.Quotient.module' _

instance module : Module R (M ⧸ N) :=
  Submodule.Quotient.module _

instance is_central_scalar {S : Type _} [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] [HasSmul Sᵐᵒᵖ R]
    [Module Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScalar S (M ⧸ N) :=
  Submodule.Quotient.is_central_scalar _

instance inhabited : Inhabited (M ⧸ N) :=
  ⟨0⟩

/-- Map sending an element of `M` to the corresponding element of `M/N`, when `N` is a
lie_submodule of the lie_module `N`. -/
abbrev mk : M → M ⧸ N :=
  Submodule.Quotient.mk

theorem is_quotient_mk (m : M) : Quotientₓ.mk' m = (mk m : M ⧸ N) :=
  rfl

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
def lieSubmoduleInvariant : L →ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule :=
  LinearMap.codRestrict _ (LieModule.toEndomorphism R L M) N.lie_mem

variable (N)

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
def actionAsEndoMap : L →ₗ⁅R⁆ Module.End R (M ⧸ N) :=
  { LinearMap.comp (Submodule.mapqLinear (N : Submodule R M) ↑N) lieSubmoduleInvariant with
    map_lie' := fun x y => Submodule.linear_map_qext _ <| LinearMap.ext fun m => congr_arg mk <| lie_lie _ _ _ }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
instance actionAsEndoMapBracket : HasBracket L (M ⧸ N) :=
  ⟨fun x n => actionAsEndoMap N x n⟩

instance lieQuotientLieRingModule : LieRingModule L (M ⧸ N) :=
  { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := HasBracket.bracket }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
instance lieQuotientLieModule : LieModule R L (M ⧸ N) :=
  LieModule.compLieHom _ (actionAsEndoMap N)

instance lieQuotientHasBracket : HasBracket (L ⧸ I) (L ⧸ I) :=
  ⟨by
    intro x y
    apply Quotientₓ.liftOn₂' x y fun x' y' => mk ⁅x',y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.to_submodule).2
    rw [Submodule.quotient_rel_r_def] at h₁ h₂
    have h : ⁅x₁,x₂⁆ - ⁅y₁,y₂⁆ = ⁅x₁,x₂ - y₂⁆ + ⁅x₁ - y₁,y₂⁆ := by
      simp [-lie_skew, ← sub_eq_add_neg, ← add_assocₓ]
    rw [h]
    apply Submodule.add_mem
    · apply lie_mem_right R L I x₁ (x₂ - y₂) h₂
      
    · apply lie_mem_left R L I (x₁ - y₁) y₂ h₁
      ⟩

@[simp]
theorem mk_bracket (x y : L) : mk ⁅x,y⁆ = ⁅(mk x : L ⧸ I),(mk y : L ⧸ I)⁆ :=
  rfl

instance lieQuotientLieRing : LieRing (L ⧸ I) where
  add_lie := by
    intro x' y' z'
    apply Quotientₓ.induction_on₃' x' y' z'
    intro x y z
    repeat'
      first |
        rw [is_quotient_mk]|
        rw [← mk_bracket]|
        rw [← Submodule.Quotient.mk_add]
    apply congr_arg
    apply add_lie
  lie_add := by
    intro x' y' z'
    apply Quotientₓ.induction_on₃' x' y' z'
    intro x y z
    repeat'
      first |
        rw [is_quotient_mk]|
        rw [← mk_bracket]|
        rw [← Submodule.Quotient.mk_add]
    apply congr_arg
    apply lie_add
  lie_self := by
    intro x'
    apply Quotientₓ.induction_on' x'
    intro x
    rw [is_quotient_mk, ← mk_bracket]
    apply congr_arg
    apply lie_self
  leibniz_lie := by
    intro x' y' z'
    apply Quotientₓ.induction_on₃' x' y' z'
    intro x y z
    repeat'
      first |
        rw [is_quotient_mk]|
        rw [← mk_bracket]|
        rw [← Submodule.Quotient.mk_add]
    apply congr_arg
    apply leibniz_lie

instance lieQuotientLieAlgebra :
    LieAlgebra R (L ⧸ I) where lie_smul := by
    intro t x' y'
    apply Quotientₓ.induction_on₂' x' y'
    intro x y
    repeat'
      first |
        rw [is_quotient_mk]|
        rw [← mk_bracket]|
        rw [← Submodule.Quotient.mk_smul]
    apply congr_arg
    apply lie_smul

/-- `lie_submodule.quotient.mk` as a `lie_module_hom`. -/
@[simps]
def mk' : M →ₗ⁅R,L⁆ M ⧸ N :=
  { N.toSubmodule.mkq with toFun := mk, map_lie' := fun r m => rfl }

@[simp]
theorem mk_eq_zero {m : M} : mk' N m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]
theorem mk'_ker : (mk' N).ker = N := by
  ext
  simp

@[simp]
theorem map_mk'_eq_bot_le : map (mk' N) N' = ⊥ ↔ N' ≤ N := by
  rw [← LieModuleHom.le_ker_iff_map, mk'_ker]

/-- Two `lie_module_hom`s from a quotient lie module are equal if their compositions with
`lie_submodule.quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem lie_module_hom_ext ⦃f g : M ⧸ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  LieModuleHom.ext fun x => Quotientₓ.induction_on' x <| LieModuleHom.congr_fun h

end Quotientₓ

end LieSubmodule

namespace LieHom

variable {R L L' : Type _}

variable [CommRingₓ R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

variable (f : L →ₗ⁅R⁆ L')

/-- The first isomorphism theorem for morphisms of Lie algebras. -/
@[simps]
noncomputable def quotKerEquivRange : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L').quotKerEquivRange with toFun := (f : L →ₗ[R] L').quotKerEquivRange,
    map_lie' := by
      rintro ⟨x⟩ ⟨y⟩
      rw [← SetLike.coe_eq_coe, LieSubalgebra.coe_bracket]
      simp only [← Submodule.Quotient.quot_mk_eq_mk, ← LinearMap.quot_ker_equiv_range_apply_mk,
        LieSubmodule.Quotient.mk_bracket, ← coe_to_linear_map, ← map_lie] }

end LieHom

