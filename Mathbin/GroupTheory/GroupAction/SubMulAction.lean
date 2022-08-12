/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.SetLike.Basic
import Mathbin.GroupTheory.GroupAction.Basic

/-!

# Sets invariant to a `mul_action`

In this file we define `sub_mul_action R M`; a subset of a `mul_action R M` which is closed with
respect to scalar multiplication.

For most uses, typically `submodule R M` is more powerful.

## Main definitions

* `sub_mul_action.mul_action` - the `mul_action R M` transferred to the subtype.
* `sub_mul_action.mul_action'` - the `mul_action S M` transferred to the subtype when
  `is_scalar_tower S R M`.
* `sub_mul_action.is_scalar_tower` - the `is_scalar_tower S R M` transferred to the subtype.

## Tags

submodule, mul_action
-/


open Function

universe u u' u'' v

variable {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure SubMulAction (R : Type u) (M : Type v) [HasSmul R M] : Type v where
  Carrier : Set M
  smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier

namespace SubMulAction

variable [HasSmul R M]

instance : SetLike (SubMulAction R M) M :=
  ⟨SubMulAction.Carrier, fun p q h => by
    cases p <;> cases q <;> congr⟩

@[simp]
theorem mem_carrier {p : SubMulAction R M} {x : M} : x ∈ p.Carrier ↔ x ∈ (p : Set M) :=
  Iff.rfl

@[ext]
theorem ext {p q : SubMulAction R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h

/-- Copy of a sub_mul_action with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : SubMulAction R M where
  Carrier := s
  smul_mem' := hs.symm ▸ p.smul_mem'

@[simp]
theorem coe_copy (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : (p.copy s hs : Set M) = s :=
  rfl

theorem copy_eq (p : SubMulAction R M) (s : Set M) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

instance : HasBot (SubMulAction R M) :=
  ⟨{ Carrier := ∅, smul_mem' := fun c => Set.not_mem_empty }⟩

instance : Inhabited (SubMulAction R M) :=
  ⟨⊥⟩

end SubMulAction

namespace SubMulAction

section HasSmul

variable [HasSmul R M]

variable (p : SubMulAction R M)

variable {r : R} {x : M}

theorem smul_mem (r : R) (h : x ∈ p) : r • x ∈ p :=
  p.smul_mem' r h

instance : HasSmul R p where smul := fun c x => ⟨c • x.1, smul_mem _ c x.2⟩

variable {p}

@[simp, norm_cast]
theorem coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x :=
  rfl

variable (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →[R] M := by
  refine' { toFun := coe.. } <;> simp [← coe_smul]

@[simp]
theorem subtype_apply (x : p) : p.Subtype x = x :=
  rfl

theorem subtype_eq_val : (SubMulAction.subtype p : p → M) = Subtype.val :=
  rfl

end HasSmul

section MulActionMonoid

variable [Monoidₓ R] [MulAction R M]

section

variable [HasSmul S R] [HasSmul S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

theorem smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p := by
  rw [← one_smul R x, ← smul_assoc]
  exact p.smul_mem _ h

instance hasSmul' : HasSmul S p where smul := fun c x => ⟨c • x.1, smul_of_tower_mem _ c x.2⟩

instance : IsScalarTower S R p where smul_assoc := fun s r x => Subtype.ext <| smul_assoc s r ↑x

@[simp, norm_cast]
theorem coe_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • ↑x :=
  rfl

@[simp]
theorem smul_mem_iff' {G} [Groupₓ G] [HasSmul G R] [MulAction G M] [IsScalarTower G R M] (g : G) {x : M} :
    g • x ∈ p ↔ x ∈ p :=
  ⟨fun h => inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

instance [HasSmul Sᵐᵒᵖ R] [HasSmul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S p where op_smul_eq_smul := fun r x => Subtype.ext <| op_smul_eq_smul r x

end

section

variable [Monoidₓ S] [HasSmul S R] [MulAction S M] [IsScalarTower S R M]

variable (p : SubMulAction R M)

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
instance mulAction' : MulAction S p where
  smul := (· • ·)
  one_smul := fun x => Subtype.ext <| one_smul _ x
  mul_smul := fun c₁ c₂ x => Subtype.ext <| mul_smul c₁ c₂ x

instance : MulAction R p :=
  p.mulAction'

end

/-- Orbits in a `sub_mul_action` coincide with orbits in the ambient space. -/
theorem coe_image_orbit {p : SubMulAction R M} (m : p) : coe '' MulAction.Orbit R m = MulAction.Orbit R (m : M) :=
  (Set.range_comp _ _).symm

/-- Stabilizers in monoid sub_mul_action coincide with stabilizers in the ambient space -/
/- -- Previously, the relatively useless :
lemma orbit_of_sub_mul {p : sub_mul_action R M} (m : p) :
  (mul_action.orbit R m : set M) = mul_action.orbit R (m : M) := rfl
-/
theorem StabilizerOfSubMul.submonoid {p : SubMulAction R M} (m : p) :
    MulAction.Stabilizer.submonoid R m = MulAction.Stabilizer.submonoid R (m : M) := by
  ext
  simp only [← MulAction.mem_stabilizer_submonoid_iff, SubMulAction.coe_smul, ← SetLike.coe_eq_coe]

end MulActionMonoid

section MulActionGroup

variable [Groupₓ R] [MulAction R M]

/-- Stabilizers in group sub_mul_action coincide with stabilizers in the ambient space -/
theorem stabilizer_of_sub_mul {p : SubMulAction R M} (m : p) :
    MulAction.stabilizer R m = MulAction.stabilizer R (m : M) := by
  rw [← Subgroup.to_submonoid_eq]
  exact stabilizer_of_sub_mul.submonoid m

end MulActionGroup

section Module

variable [Semiringₓ R] [AddCommMonoidₓ M]

variable [Module R M]

variable (p : SubMulAction R M)

theorem zero_mem (h : (p : Set M).Nonempty) : (0 : M) ∈ p :=
  let ⟨x, hx⟩ := h
  zero_smul R (x : M) ▸ p.smul_mem 0 hx

/-- If the scalar product forms a `module`, and the `sub_mul_action` is not `⊥`, then the
subset inherits the zero. -/
instance [n_empty : Nonempty p] : Zero p where zero := ⟨0, n_empty.elim fun x => p.zero_mem ⟨x, x.Prop⟩⟩

end Module

section AddCommGroupₓ

variable [Ringₓ R] [AddCommGroupₓ M]

variable [Module R M]

variable (p p' : SubMulAction R M)

variable {r : R} {x y : M}

theorem neg_mem (hx : x ∈ p) : -x ∈ p := by
  rw [← neg_one_smul R]
  exact p.smul_mem _ hx

@[simp]
theorem neg_mem_iff : -x ∈ p ↔ x ∈ p :=
  ⟨fun h => by
    rw [← neg_negₓ x]
    exact neg_mem _ h, neg_mem _⟩

instance : Neg p :=
  ⟨fun x => ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast]
theorem coe_neg (x : p) : ((-x : p) : M) = -x :=
  rfl

end AddCommGroupₓ

end SubMulAction

namespace SubMulAction

variable [GroupWithZeroₓ S] [Monoidₓ R] [MulAction R M]

variable [HasSmul S R] [MulAction S M] [IsScalarTower S R M]

variable (p : SubMulAction R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
  p.smul_mem_iff' (Units.mk0 s s0)

end SubMulAction

