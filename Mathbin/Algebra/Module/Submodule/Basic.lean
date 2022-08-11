/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.Module.Equiv
import Mathbin.GroupTheory.GroupAction.SubMulAction

/-!

# Submodules of a module

In this file we define

* `submodule R M` : a subset of a `module` `M` that contains zero and is closed with respect to
  addition and scalar multiplication.

* `subspace k M` : an abbreviation for `submodule` assuming that `k` is a `field`.

## Tags

submodule, subspace, linear map
-/


open Function

open BigOperators

universe u'' u' u v w

variable {G : Type u''} {S : Type u'} {R : Type u} {M : Type v} {ι : Type w}

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure Submodule (R : Type u) (M : Type v) [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] extends AddSubmonoid M,
  SubMulAction R M : Type v

/-- Reinterpret a `submodule` as an `add_submonoid`. -/
add_decl_doc Submodule.toAddSubmonoid

/-- Reinterpret a `submodule` as an `sub_mul_action`. -/
add_decl_doc Submodule.toSubMulAction

namespace Submodule

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

instance : SetLike (Submodule R M) M where
  coe := Submodule.Carrier
  coe_injective' := fun p q h => by
    cases p <;> cases q <;> congr

instance : AddSubmonoidClass (Submodule R M) M where
  zero_mem := zero_mem'
  add_mem := add_mem'

@[simp]
theorem mem_to_add_submonoid (p : Submodule R M) (x : M) : x ∈ p.toAddSubmonoid ↔ x ∈ p :=
  Iff.rfl

variable {p q : Submodule R M}

@[simp]
theorem mem_mk {S : Set M} {x : M} (h₁ h₂ h₃) : x ∈ (⟨S, h₁, h₂, h₃⟩ : Submodule R M) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : Set M) (h₁ h₂ h₃) : ((⟨S, h₁, h₂, h₃⟩ : Submodule R M) : Set M) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : Set M} (h₁ h₂ h₃ h₁' h₂' h₃') :
    (⟨S, h₁, h₂, h₃⟩ : Submodule R M) ≤ (⟨S', h₁', h₂', h₃'⟩ : Submodule R M) ↔ S ⊆ S' :=
  Iff.rfl

@[ext]
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

/-- Copy of a submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (p : Submodule R M) (s : Set M) (hs : s = ↑p) : Submodule R M where
  Carrier := s
  zero_mem' := hs.symm ▸ p.zero_mem'
  add_mem' := hs.symm ▸ p.add_mem'
  smul_mem' := hs.symm ▸ p.smul_mem'

@[simp]
theorem coe_copy (S : Submodule R M) (s : Set M) (hs : s = ↑S) : (S.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (S : Submodule R M) (s : Set M) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

theorem to_add_submonoid_injective : Injective (toAddSubmonoid : Submodule R M → AddSubmonoid M) := fun p q h =>
  SetLike.ext'_iff.2 (show _ from SetLike.ext'_iff.1 h)

@[simp]
theorem to_add_submonoid_eq : p.toAddSubmonoid = q.toAddSubmonoid ↔ p = q :=
  to_add_submonoid_injective.eq_iff

@[mono]
theorem to_add_submonoid_strict_mono : StrictMono (toAddSubmonoid : Submodule R M → AddSubmonoid M) := fun _ _ => id

theorem to_add_submonoid_le : p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q :=
  Iff.rfl

@[mono]
theorem to_add_submonoid_mono : Monotone (toAddSubmonoid : Submodule R M → AddSubmonoid M) :=
  to_add_submonoid_strict_mono.Monotone

@[simp]
theorem coe_to_add_submonoid (p : Submodule R M) : (p.toAddSubmonoid : Set M) = p :=
  rfl

theorem to_sub_mul_action_injective : Injective (toSubMulAction : Submodule R M → SubMulAction R M) := fun p q h =>
  SetLike.ext'_iff.2 (show _ from SetLike.ext'_iff.1 h)

@[simp]
theorem to_sub_mul_action_eq : p.toSubMulAction = q.toSubMulAction ↔ p = q :=
  to_sub_mul_action_injective.eq_iff

@[mono]
theorem to_sub_mul_action_strict_mono : StrictMono (toSubMulAction : Submodule R M → SubMulAction R M) := fun _ _ => id

@[mono]
theorem to_sub_mul_action_mono : Monotone (toSubMulAction : Submodule R M → SubMulAction R M) :=
  to_sub_mul_action_strict_mono.Monotone

@[simp]
theorem coe_to_sub_mul_action (p : Submodule R M) : (p.toSubMulAction : Set M) = p :=
  rfl

end Submodule

namespace Submodule

section AddCommMonoidₓ

variable [Semiringₓ R] [AddCommMonoidₓ M]

-- We can infer the module structure implicitly from the bundled submodule,
-- rather than via typeclass resolution.
variable {module_M : Module R M}

variable {p q : Submodule R M}

variable {r : R} {x y : M}

variable (p)

@[simp]
theorem mem_carrier : x ∈ p.Carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl

@[simp]
protected theorem zero_mem : (0 : M) ∈ p :=
  zero_mem _

protected theorem add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p :=
  add_mem h₁ h₂

theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h

theorem smul_of_tower_mem [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] (r : S) (h : x ∈ p) : r • x ∈ p :=
  p.toSubMulAction.smul_of_tower_mem r h

protected theorem sum_mem {t : Finset ι} {f : ι → M} : (∀, ∀ c ∈ t, ∀, f c ∈ p) → (∑ i in t, f i) ∈ p :=
  sum_mem

theorem sum_smul_mem {t : Finset ι} {f : ι → M} (r : ι → R) (hyp : ∀, ∀ c ∈ t, ∀, f c ∈ p) :
    (∑ i in t, r i • f i) ∈ p :=
  sum_mem fun i hi => smul_mem _ _ (hyp i hi)

@[simp]
theorem smul_mem_iff' [Groupₓ G] [MulAction G M] [HasSmul G R] [IsScalarTower G R M] (g : G) : g • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff' g

instance : Add p :=
  ⟨fun x y => ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩

instance : Zero p :=
  ⟨⟨0, zero_mem _⟩⟩

instance : Inhabited p :=
  ⟨0⟩

instance [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] : HasSmul S p :=
  ⟨fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

instance [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] : IsScalarTower S R p :=
  p.toSubMulAction.IsScalarTower

instance [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] [HasSmul Sᵐᵒᵖ R] [HasSmul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S p :=
  p.toSubMulAction.IsCentralScalar

protected theorem nonempty : (p : Set M).Nonempty :=
  ⟨0, p.zero_mem⟩

@[simp]
theorem mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 :=
  Subtype.ext_iff_val

variable {p}

@[simp, norm_cast]
theorem coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0 :=
  (SetLike.coe_eq_coe : (x : M) = (0 : p) ↔ x = 0)

@[simp, norm_cast]
theorem coe_add (x y : p) : (↑(x + y) : M) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : p) : M) = 0 :=
  rfl

@[norm_cast]
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x :=
  rfl

@[simp, norm_cast]
theorem coe_smul_of_tower [HasSmul S R] [HasSmul S M] [IsScalarTower S R M] (r : S) (x : p) :
    ((r • x : p) : M) = r • ↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl

@[simp]
theorem coe_mem (x : p) : (x : M) ∈ p :=
  x.2

variable (p)

instance : AddCommMonoidₓ p :=
  { p.toAddSubmonoid.toAddCommMonoid with add := (· + ·), zero := 0 }

instance module' [Semiringₓ S] [HasSmul S R] [Module S M] [IsScalarTower S R M] : Module S p := by
  refine' { p.to_sub_mul_action.mul_action' with smul := (· • ·).. } <;>
    · intros
      apply SetCoe.ext
      simp [← smul_add, ← add_smul, ← mul_smul]
      

instance : Module R p :=
  p.module'

instance no_zero_smul_divisors [NoZeroSmulDivisors R M] : NoZeroSmulDivisors R p :=
  ⟨fun c x h =>
    have : c = 0 ∨ (x : M) = 0 := eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h)
    this.imp_right (@Subtype.ext_iff _ _ x 0).mpr⟩

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[R] M := by
  refine' { toFun := coe.. } <;> simp [← coe_smul]

theorem subtype_apply (x : p) : p.Subtype x = x :=
  rfl

@[simp]
theorem coe_subtype : (Submodule.subtype p : p → M) = coe :=
  rfl

theorem injective_subtype : Injective p.Subtype :=
  Subtype.coe_injective

/-- Note the `add_submonoid` version of this lemma is called `add_submonoid.coe_finset_sum`. -/
@[simp]
theorem coe_sum (x : ι → p) (s : Finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : M) :=
  p.Subtype.map_sum

section RestrictScalars

variable (S) [Semiringₓ S] [Module S M] [Module R M] [HasSmul S R] [IsScalarTower S R M]

/-- `V.restrict_scalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,
corresponding to `V`, an `R`-submodule of the original `R`-module.
-/
def restrictScalars (V : Submodule R M) : Submodule S M where
  Carrier := V
  zero_mem' := V.zero_mem
  smul_mem' := fun c m h => V.smul_of_tower_mem c h
  add_mem' := fun x y hx hy => V.add_mem hx hy

@[simp]
theorem coe_restrict_scalars (V : Submodule R M) : (V.restrictScalars S : Set M) = V :=
  rfl

@[simp]
theorem restrict_scalars_mem (V : Submodule R M) (m : M) : m ∈ V.restrictScalars S ↔ m ∈ V :=
  Iff.refl _

@[simp]
theorem restrict_scalars_self (V : Submodule R M) : V.restrictScalars R = V :=
  SetLike.coe_injective rfl

variable (R S M)

theorem restrict_scalars_injective : Function.Injective (restrictScalars S : Submodule R M → Submodule S M) :=
  fun V₁ V₂ h => ext <| Set.ext_iff.1 (SetLike.ext'_iff.1 h : _)

@[simp]
theorem restrict_scalars_inj {V₁ V₂ : Submodule R M} : restrictScalars S V₁ = restrictScalars S V₂ ↔ V₁ = V₂ :=
  (restrict_scalars_injective S _ _).eq_iff

/-- Even though `p.restrict_scalars S` has type `submodule S M`, it is still an `R`-module. -/
instance restrictScalars.origModule (p : Submodule R M) : Module R (p.restrictScalars S) :=
  (by
    infer_instance : Module R p)

instance (p : Submodule R M) :
    IsScalarTower S R (p.restrictScalars S) where smul_assoc := fun r s x => Subtype.ext <| smul_assoc r s (x : M)

/-- `restrict_scalars S` is an embedding of the lattice of `R`-submodules into
the lattice of `S`-submodules. -/
@[simps]
def restrictScalarsEmbedding : Submodule R M ↪o Submodule S M where
  toFun := restrictScalars S
  inj' := restrict_scalars_injective S R M
  map_rel_iff' := fun p q => by
    simp [← SetLike.le_def]

/-- Turning `p : submodule R M` into an `S`-submodule gives the same module structure
as turning it into a type and adding a module structure. -/
@[simps (config := { simpRhs := true })]
def restrictScalarsEquiv (p : Submodule R M) : p.restrictScalars S ≃ₗ[R] p :=
  { AddEquiv.refl p with toFun := id, invFun := id, map_smul' := fun c x => rfl }

end RestrictScalars

end AddCommMonoidₓ

section AddCommGroupₓ

variable [Ringₓ R] [AddCommGroupₓ M]

variable {module_M : Module R M}

variable (p p' : Submodule R M)

variable {r : R} {x y : M}

instance [Module R M] : AddSubgroupClass (Submodule R M) M :=
  { Submodule.addSubmonoidClass with neg_mem := fun p x => p.toSubMulAction.neg_mem }

protected theorem neg_mem (hx : x ∈ p) : -x ∈ p :=
  neg_mem hx

/-- Reinterpret a submodule as an additive subgroup. -/
def toAddSubgroup : AddSubgroup M :=
  { p.toAddSubmonoid with neg_mem' := fun _ => p.neg_mem }

@[simp]
theorem coe_to_add_subgroup : (p.toAddSubgroup : Set M) = p :=
  rfl

@[simp]
theorem mem_to_add_subgroup : x ∈ p.toAddSubgroup ↔ x ∈ p :=
  Iff.rfl

include module_M

theorem to_add_subgroup_injective : Injective (toAddSubgroup : Submodule R M → AddSubgroup M)
  | p, q, h => SetLike.ext (SetLike.ext_iff.1 h : _)

@[simp]
theorem to_add_subgroup_eq : p.toAddSubgroup = p'.toAddSubgroup ↔ p = p' :=
  to_add_subgroup_injective.eq_iff

@[mono]
theorem to_add_subgroup_strict_mono : StrictMono (toAddSubgroup : Submodule R M → AddSubgroup M) := fun _ _ => id

theorem to_add_subgroup_le : p.toAddSubgroup ≤ p'.toAddSubgroup ↔ p ≤ p' :=
  Iff.rfl

@[mono]
theorem to_add_subgroup_mono : Monotone (toAddSubgroup : Submodule R M → AddSubgroup M) :=
  to_add_subgroup_strict_mono.Monotone

omit module_M

protected theorem sub_mem : x ∈ p → y ∈ p → x - y ∈ p :=
  sub_mem

protected theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  neg_mem_iff

protected theorem add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) :=
  add_mem_cancel_right

protected theorem add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) :=
  add_mem_cancel_left

protected theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  AddSubgroupClass.coe_neg _

protected theorem coe_sub (x y : p) : (↑(x - y) : M) = ↑x - ↑y :=
  AddSubgroupClass.coe_sub _ _

theorem sub_mem_iff_left (hy : y ∈ p) : x - y ∈ p ↔ x ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]

theorem sub_mem_iff_right (hx : x ∈ p) : x - y ∈ p ↔ y ∈ p := by
  rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]

instance : AddCommGroupₓ p :=
  { p.toAddSubgroup.toAddCommGroup with add := (· + ·), zero := 0, neg := Neg.neg }

end AddCommGroupₓ

section IsDomain

variable [Ringₓ R] [IsDomain R]

variable [AddCommGroupₓ M] [Module R M] {b : ι → M}

theorem not_mem_of_ortho {x : M} {N : Submodule R M} (ortho : ∀ (c : R), ∀ y ∈ N, ∀, c • x + y = (0 : M) → c = 0) :
    x ∉ N := by
  intro hx
  simpa using ortho (-1) x hx

theorem ne_zero_of_ortho {x : M} {N : Submodule R M} (ortho : ∀ (c : R), ∀ y ∈ N, ∀, c • x + y = (0 : M) → c = 0) :
    x ≠ 0 :=
  mt (fun h => show x ∈ N from h.symm ▸ N.zero_mem) (not_mem_of_ortho ortho)

end IsDomain

section OrderedMonoid

variable [Semiringₓ R]

/-- A submodule of an `ordered_add_comm_monoid` is an `ordered_add_comm_monoid`. -/
instance toOrderedAddCommMonoid {M} [OrderedAddCommMonoid M] [Module R M] (S : Submodule R M) :
    OrderedAddCommMonoid S :=
  Subtype.coe_injective.OrderedAddCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of a `linear_ordered_add_comm_monoid` is a `linear_ordered_add_comm_monoid`. -/
instance toLinearOrderedAddCommMonoid {M} [LinearOrderedAddCommMonoid M] [Module R M] (S : Submodule R M) :
    LinearOrderedAddCommMonoid S :=
  Subtype.coe_injective.LinearOrderedAddCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ =>
    rfl

/-- A submodule of an `ordered_cancel_add_comm_monoid` is an `ordered_cancel_add_comm_monoid`. -/
instance toOrderedCancelAddCommMonoid {M} [OrderedCancelAddCommMonoid M] [Module R M] (S : Submodule R M) :
    OrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.OrderedCancelAddCommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

/-- A submodule of a `linear_ordered_cancel_add_comm_monoid` is a
`linear_ordered_cancel_add_comm_monoid`. -/
instance toLinearOrderedCancelAddCommMonoid {M} [LinearOrderedCancelAddCommMonoid M] [Module R M] (S : Submodule R M) :
    LinearOrderedCancelAddCommMonoid S :=
  Subtype.coe_injective.LinearOrderedCancelAddCommMonoid coe rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

end OrderedMonoid

section OrderedGroup

variable [Ringₓ R]

/-- A submodule of an `ordered_add_comm_group` is an `ordered_add_comm_group`. -/
instance toOrderedAddCommGroup {M} [OrderedAddCommGroup M] [Module R M] (S : Submodule R M) : OrderedAddCommGroup S :=
  Subtype.coe_injective.OrderedAddCommGroup coe rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

/-- A submodule of a `linear_ordered_add_comm_group` is a
`linear_ordered_add_comm_group`. -/
instance toLinearOrderedAddCommGroup {M} [LinearOrderedAddCommGroup M] [Module R M] (S : Submodule R M) :
    LinearOrderedAddCommGroup S :=
  Subtype.coe_injective.LinearOrderedAddCommGroup coe rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end OrderedGroup

end Submodule

namespace Submodule

variable [DivisionRing S] [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

variable [HasSmul S R] [Module S M] [IsScalarTower S R M]

variable (p : Submodule R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.toSubMulAction.smul_mem_iff s0

end Submodule

/-- Subspace of a vector space. Defined to equal `submodule`. -/
abbrev Subspace (R : Type u) (M : Type v) [Field R] [AddCommGroupₓ M] [Module R M] :=
  Submodule R M

