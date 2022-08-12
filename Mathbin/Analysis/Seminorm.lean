/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Yaël Dillies, Moritz Doll
-/
import Mathbin.Analysis.LocallyConvex.Basic
import Mathbin.Data.Real.Pointwise
import Mathbin.Data.Real.Sqrt
import Mathbin.Topology.Algebra.FilterBasis
import Mathbin.Topology.Algebra.Module.LocallyConvex

/-!
# Seminorms

This file defines seminorms.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

## Main declarations

For an addditive group:
* `add_group_seminorm`: A function `f` from an add_group `G` to the reals that preserves zero,
takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x ∈ G`.

For a module over a normed ring:
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

seminorm, locally convex, LCTVS
-/


open NormedField Set

open BigOperators Nnreal Pointwise TopologicalSpace

variable {R R' 𝕜 E F G ι : Type _}

/-- A seminorm on an add_group `G` is a function A function `f : G → ℝ` that preserves zero, takes
nonnegative values, is subadditive and such that `f (-x) = f x` for all `x ∈ G`. -/
structure AddGroupSeminorm (G : Type _) [AddGroupₓ G] extends ZeroHom G ℝ where
  nonneg' : ∀ r, 0 ≤ to_fun r
  add_le' : ∀ r s, to_fun (r + s) ≤ to_fun r + to_fun s
  neg' : ∀ r, to_fun (-r) = to_fun r

attribute [nolint doc_blame] AddGroupSeminorm.toZeroHom

namespace AddGroupSeminorm

variable [AddGroupₓ E]

instance zeroHomClass : ZeroHomClass (AddGroupSeminorm E) E ℝ where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_zero := fun f => f.map_zero'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (AddGroupSeminorm E) fun _ => E → ℝ :=
  ⟨fun p => p.toFun⟩

@[ext]
theorem ext {p q : AddGroupSeminorm E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  FunLike.ext p q h

instance : Zero (AddGroupSeminorm E) :=
  ⟨{ toFun := 0, nonneg' := fun r => le_reflₓ _, map_zero' := Pi.zero_apply _,
      add_le' := fun _ _ => Eq.ge (zero_addₓ _), neg' := fun x => rfl }⟩

@[simp]
theorem coe_zero : ⇑(0 : AddGroupSeminorm E) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : E) : (0 : AddGroupSeminorm E) x = 0 :=
  rfl

instance : Inhabited (AddGroupSeminorm E) :=
  ⟨0⟩

variable (p : AddGroupSeminorm E) (x y : E) (r : ℝ)

protected theorem nonneg : 0 ≤ p x :=
  p.nonneg' _

@[simp]
protected theorem map_zero : p 0 = 0 :=
  p.map_zero'

protected theorem add_le : p (x + y) ≤ p x + p y :=
  p.add_le' _ _

@[simp]
protected theorem neg : p (-x) = p x :=
  p.neg' _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] :
    HasSmul R (AddGroupSeminorm E) where smul := fun r p =>
    { toFun := fun x => r • p x,
      nonneg' := fun x => by
        simp only [smul_one_smul ℝ≥0 r (_ : ℝ), ← Nnreal.smul_def, ← smul_eq_mul]
        exact mul_nonneg (Nnreal.coe_nonneg _) (p.nonneg _),
      map_zero' := by
        simp only [smul_one_smul ℝ≥0 r (_ : ℝ), ← Nnreal.smul_def, ← smul_eq_mul, ← p.map_zero, ← mul_zero],
      add_le' := fun _ _ => by
        simp only [smul_one_smul ℝ≥0 r (_ : ℝ), ← Nnreal.smul_def, ← smul_eq_mul]
        exact (mul_le_mul_of_nonneg_left (p.add_le _ _) (Nnreal.coe_nonneg _)).trans_eq (mul_addₓ _ _ _),
      neg' := fun x => by
        rw [p.neg] }

instance [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] [HasSmul R' ℝ] [HasSmul R' ℝ≥0 ]
    [IsScalarTower R' ℝ≥0 ℝ] [HasSmul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (AddGroupSeminorm E) where smul_assoc := fun r a p => ext fun x => smul_assoc r a (p x)

@[simp]
theorem coe_smul [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : AddGroupSeminorm E) :
    ⇑(r • p) = r • p :=
  rfl

@[simp]
theorem smul_apply [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : AddGroupSeminorm E) (x : E) :
    (r • p) x = r • p x :=
  rfl

instance :
    Add
      (AddGroupSeminorm
        E) where add := fun p q =>
    { toFun := fun x => p x + q x, nonneg' := fun x => add_nonneg (p.Nonneg _) (q.Nonneg _),
      map_zero' := by
        rw [p.map_zero, q.map_zero, zero_addₓ],
      add_le' := fun _ _ => LE.le.trans_eq (add_le_add (p.add_le _ _) (q.add_le _ _)) (add_add_add_commₓ _ _ _ _),
      neg' := fun x => by
        rw [p.neg, q.neg] }

@[simp]
theorem coe_add (p q : AddGroupSeminorm E) : ⇑(p + q) = p + q :=
  rfl

@[simp]
theorem add_apply (p q : AddGroupSeminorm E) (x : E) : (p + q) x = p x + q x :=
  rfl

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
noncomputable instance :
    HasSup (AddGroupSeminorm E) where sup := fun p q =>
    { toFun := p⊔q,
      nonneg' := fun x => by
        simp only [← Pi.sup_apply, ← le_sup_iff]
        exact Or.intro_left _ (p.nonneg _),
      map_zero' := by
        simp only [← Pi.sup_apply]
        rw [← p.map_zero, sup_eq_left, p.map_zero, q.map_zero],
      add_le' := fun x y =>
        sup_le ((p.add_le x y).trans <| add_le_add le_sup_left le_sup_left)
          ((q.add_le x y).trans <| add_le_add le_sup_right le_sup_right),
      neg' := fun x => by
        rw [Pi.sup_apply, Pi.sup_apply, p.neg, q.neg] }

@[simp]
theorem coe_sup (p q : AddGroupSeminorm E) : ⇑(p⊔q) = p⊔q :=
  rfl

theorem sup_apply (p q : AddGroupSeminorm E) (x : E) : (p⊔q) x = p x⊔q x :=
  rfl

theorem smul_sup [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : AddGroupSeminorm E) :
    r • (p⊔q) = r • p⊔r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [smul_eq_mul, Nnreal.smul_def, ← smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0 ).Prop
  ext fun x => real.smul_max _ _

instance : PartialOrderₓ (AddGroupSeminorm E) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

theorem le_def (p q : AddGroupSeminorm E) : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

theorem lt_def (p q : AddGroupSeminorm E) : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

noncomputable instance : SemilatticeSup (AddGroupSeminorm E) :=
  Function.Injective.semilatticeSup _ FunLike.coe_injective coe_sup

section AddCommGroupₓ

variable [AddCommGroupₓ G]

variable (q : AddGroupSeminorm G)

protected theorem sub_le (x y : G) : q (x - y) ≤ q x + q y :=
  calc
    q (x - y) = q (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ q x + q (-y) := q.add_le x (-y)
    _ = q x + q y := by
      rw [q.neg]
    

theorem sub_rev (x y : G) : q (x - y) = q (y - x) := by
  rw [← neg_sub, q.neg]

/-- The direct path from 0 to y is shorter than the path with x "inserted" in between. -/
theorem le_insert (x y : G) : q y ≤ q x + q (x - y) :=
  calc
    q y = q (x - (x - y)) := by
      rw [sub_sub_cancel]
    _ ≤ q x + q (x - y) := q.sub_le _ _
    

/-- The direct path from 0 to x is shorter than the path with y "inserted" in between. -/
theorem le_insert' (x y : G) : q x ≤ q y + q (x - y) := by
  rw [sub_rev]
  exact le_insert _ _ _

private theorem bdd_below_range_add (x : G) (p q : AddGroupSeminorm G) :
    BddBelow (Range fun u : G => p u + q (x - u)) := by
  use 0
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (p.nonneg _) (q.nonneg _)

noncomputable instance :
    HasInf
      (AddGroupSeminorm
        G) where inf := fun p q =>
    { toFun := fun x => ⨅ u : G, p u + q (x - u),
      map_zero' :=
        cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (fun x => add_nonneg (p.Nonneg _) (q.Nonneg _)) fun r hr =>
          ⟨0, by
            simpa [← sub_zero, ← p.map_zero, ← q.map_zero, ← add_zeroₓ] using hr⟩,
      nonneg' := fun x => le_cinfi fun x => add_nonneg (p.Nonneg _) (q.Nonneg _),
      add_le' := fun x y => by
        refine' le_cinfi_add_cinfi fun u v => _
        apply cinfi_le_of_le (bdd_below_range_add _ _ _) (v + u)
        dsimp' only
        convert add_le_add (p.add_le v u) (q.add_le (y - v) (x - u)) using 1
        · rw
            [show x + y - (v + u) = y - v + (x - u) by
              abel]
          
        · abel
          ,
      neg' := fun x => by
        have : (⨅ u : G, p u + q (x - u) : ℝ) = ⨅ u : G, p (-u) + q (x + u) := by
          apply Function.Surjective.infi_congr (fun x : G => -x) neg_surjective
          · intro u
            simp only [← neg_negₓ, ← add_right_injₓ, ← sub_eq_add_neg]
            
        rw [this]
        apply congr_arg
        ext u
        rw [p.neg, sub_eq_add_neg, ← neg_add_rev, add_commₓ u, q.neg] }

@[simp]
theorem inf_apply (p q : AddGroupSeminorm G) (x : G) : (p⊓q) x = ⨅ u : G, p u + q (x - u) :=
  rfl

noncomputable instance : Lattice (AddGroupSeminorm G) :=
  { AddGroupSeminorm.semilatticeSup with inf := (·⊓·),
    inf_le_left := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) x
      simp only [← sub_self, ← map_zero, ← add_zeroₓ],
    inf_le_right := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) (0 : G)
      simp only [← sub_self, ← map_zero, ← zero_addₓ, ← sub_zero],
    le_inf := fun a b c hab hac x => le_cinfi fun u => le_transₓ (a.le_insert' _ _) (add_le_add (hab _) (hac _)) }

end AddCommGroupₓ

section Comp

variable [AddGroupₓ F] [AddGroupₓ G]

/-- Composition of an add_group_seminorm with an add_monoid_hom is an add_group_seminorm. -/
def comp (p : AddGroupSeminorm F) (f : E →+ F) : AddGroupSeminorm E where
  toFun := fun x => p (f x)
  nonneg' := fun x => p.Nonneg _
  map_zero' := by
    rw [f.map_zero, p.map_zero]
  add_le' := fun _ _ => by
    apply Eq.trans_le (congr_arg p (f.map_add _ _)) (p.add_le _ _)
  neg' := fun x => by
    rw [map_neg, p.neg]

@[simp]
theorem coe_comp (p : AddGroupSeminorm F) (f : E →+ F) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
theorem comp_apply (p : AddGroupSeminorm F) (f : E →+ F) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
theorem comp_id (p : AddGroupSeminorm E) : p.comp (AddMonoidHom.id _) = p :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (p : AddGroupSeminorm F) : p.comp (0 : E →+ F) = 0 :=
  ext fun _ => map_zero p

@[simp]
theorem zero_comp (f : E →+ F) : (0 : AddGroupSeminorm F).comp f = 0 :=
  ext fun _ => rfl

theorem comp_comp (p : AddGroupSeminorm G) (g : F →+ G) (f : E →+ F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

theorem add_comp (p q : AddGroupSeminorm F) (f : E →+ F) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

theorem comp_add_le {A B : Type _} [AddCommGroupₓ A] [AddCommGroupₓ B] (p : AddGroupSeminorm B) (f g : A →+ B) :
    p.comp (f + g) ≤ p.comp f + p.comp g := fun _ => p.add_le _ _

theorem comp_mono {p : AddGroupSeminorm F} {q : AddGroupSeminorm F} (f : E →+ F) (hp : p ≤ q) : p.comp f ≤ q.comp f :=
  fun _ => hp _

end Comp

end AddGroupSeminorm

/-- A seminorm on a module over a normed ring is a function to the reals that is positive
semidefinite, positive homogeneous, and subadditive. -/
structure Seminorm (𝕜 : Type _) (E : Type _) [SemiNormedRing 𝕜] [AddGroupₓ E] [HasSmul 𝕜 E] extends
  AddGroupSeminorm E where
  smul' : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x

attribute [nolint doc_blame] Seminorm.toAddGroupSeminorm

private theorem map_zero.of_smul {𝕜 : Type _} {E : Type _} [SemiNormedRing 𝕜] [AddGroupₓ E] [SmulWithZero 𝕜 E]
    {f : E → ℝ} (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ∥a∥ * f x) : f 0 = 0 :=
  calc
    f 0 = f ((0 : 𝕜) • 0) := by
      rw [zero_smul]
    _ = 0 := by
      rw [smul, norm_zero, zero_mul]
    

private theorem neg.of_smul {𝕜 : Type _} {E : Type _} [SemiNormedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {f : E → ℝ}
    (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ∥a∥ * f x) (x : E) : f (-x) = f x := by
  rw [← neg_one_smul 𝕜, smul, norm_neg, ← smul, one_smul]

private theorem nonneg.of {𝕜 : Type _} {E : Type _} [SemiNormedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] {f : E → ℝ}
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ∥a∥ * f x) (x : E) : 0 ≤ f x :=
  have h : 0 ≤ 2 * f x :=
    calc
      0 = f (x + -x) := by
        rw [add_neg_selfₓ, map_zero.of_smul smul]
      _ ≤ f x + f (-x) := add_le _ _
      _ = 2 * f x := by
        rw [neg.of_smul smul, two_mul]
      
  nonneg_of_mul_nonneg_right h zero_lt_two

/-- Alternative constructor for a `seminorm` on an `add_comm_group E` that is a module over a
`semi_norm_ring 𝕜`. -/
def Seminorm.of {𝕜 : Type _} {E : Type _} [SemiNormedRing 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (f : E → ℝ)
    (add_le : ∀ x y : E, f (x + y) ≤ f x + f y) (smul : ∀ (a : 𝕜) (x : E), f (a • x) = ∥a∥ * f x) : Seminorm 𝕜 E where
  toFun := f
  map_zero' := MapZero.of_smul smul
  nonneg' := Nonneg.of add_le smul
  add_le' := add_le
  smul' := smul
  neg' := Neg.of_smul smul

namespace Seminorm

section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddGroupₓ

variable [AddGroupₓ E]

section HasSmul

variable [HasSmul 𝕜 E]

instance zeroHomClass : ZeroHomClass (Seminorm 𝕜 E) E ℝ where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_zero := fun f => f.map_zero'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (Seminorm 𝕜 E) fun _ => E → ℝ :=
  ⟨fun p => p.toFun⟩

@[ext]
theorem ext {p q : Seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q :=
  FunLike.ext p q h

instance : Zero (Seminorm 𝕜 E) :=
  ⟨{ AddGroupSeminorm.hasZero.zero with smul' := fun _ _ => (mul_zero _).symm }⟩

@[simp]
theorem coe_zero : ⇑(0 : Seminorm 𝕜 E) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : E) : (0 : Seminorm 𝕜 E) x = 0 :=
  rfl

instance : Inhabited (Seminorm 𝕜 E) :=
  ⟨0⟩

variable (p : Seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected theorem nonneg : 0 ≤ p x :=
  p.nonneg' _

protected theorem map_zero : p 0 = 0 :=
  p.map_zero'

protected theorem smul : p (c • x) = ∥c∥ * p x :=
  p.smul' _ _

protected theorem add_le : p (x + y) ≤ p x + p y :=
  p.add_le' _ _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] :
    HasSmul R
      (Seminorm 𝕜
        E) where smul := fun r p =>
    { r • p.toAddGroupSeminorm with toFun := fun x => r • p x,
      smul' := fun _ _ => by
        simp only [smul_one_smul ℝ≥0 r (_ : ℝ), ← Nnreal.smul_def, ← smul_eq_mul]
        rw [p.smul, mul_left_commₓ] }

instance [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] [HasSmul R' ℝ] [HasSmul R' ℝ≥0 ]
    [IsScalarTower R' ℝ≥0 ℝ] [HasSmul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (Seminorm 𝕜 E) where smul_assoc := fun r a p => ext fun x => smul_assoc r a (p x)

theorem coe_smul [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) : ⇑(r • p) = r • p :=
  rfl

@[simp]
theorem smul_apply [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p : Seminorm 𝕜 E) (x : E) :
    (r • p) x = r • p x :=
  rfl

instance :
    Add
      (Seminorm 𝕜
        E) where add := fun p q =>
    { p.toAddGroupSeminorm + q.toAddGroupSeminorm with toFun := fun x => p x + q x,
      smul' := fun a x => by
        simp only [← p.smul, ← q.smul, ← mul_addₓ] }

theorem coe_add (p q : Seminorm 𝕜 E) : ⇑(p + q) = p + q :=
  rfl

@[simp]
theorem add_apply (p q : Seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x :=
  rfl

instance : AddMonoidₓ (Seminorm 𝕜 E) :=
  FunLike.coe_injective.AddMonoid _ rfl coe_add fun p n => coe_smul n p

instance : OrderedCancelAddCommMonoid (Seminorm 𝕜 E) :=
  FunLike.coe_injective.OrderedCancelAddCommMonoid _ rfl coe_add fun p n => coe_smul n p

instance [Monoidₓ R] [MulAction R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : MulAction R (Seminorm 𝕜 E) :=
  FunLike.coe_injective.MulAction _ coe_smul

variable (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coeFnAddMonoidHom : AddMonoidHom (Seminorm 𝕜 E) (E → ℝ) :=
  ⟨coeFn, coe_zero, coe_add⟩

theorem coe_fn_add_monoid_hom_injective : Function.Injective (coeFnAddMonoidHom 𝕜 E) :=
  show @Function.Injective (Seminorm 𝕜 E) (E → ℝ) coeFn from FunLike.coe_injective

variable {𝕜 E}

instance [Monoidₓ R] [DistribMulAction R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] :
    DistribMulAction R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).DistribMulAction _ coe_smul

instance [Semiringₓ R] [Module R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] : Module R (Seminorm 𝕜 E) :=
  (coe_fn_add_monoid_hom_injective 𝕜 E).Module R _ coe_smul

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
noncomputable instance :
    HasSup
      (Seminorm 𝕜
        E) where sup := fun p q =>
    { p.toAddGroupSeminorm⊔q.toAddGroupSeminorm with toFun := p⊔q,
      smul' := fun x v =>
        (congr_arg2ₓ max (p.smul x v) (q.smul x v)).trans <| (mul_max_of_nonneg _ _ <| norm_nonneg x).symm }

@[simp]
theorem coe_sup (p q : Seminorm 𝕜 E) : ⇑(p⊔q) = p⊔q :=
  rfl

theorem sup_apply (p q : Seminorm 𝕜 E) (x : E) : (p⊔q) x = p x⊔q x :=
  rfl

theorem smul_sup [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p⊔q) = r • p⊔r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [smul_eq_mul, Nnreal.smul_def, ← smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0 ).Prop
  ext fun x => real.smul_max _ _

instance : PartialOrderₓ (Seminorm 𝕜 E) :=
  PartialOrderₓ.lift _ FunLike.coe_injective

theorem le_def (p q : Seminorm 𝕜 E) : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl

theorem lt_def (p q : Seminorm 𝕜 E) : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl

noncomputable instance : SemilatticeSup (Seminorm 𝕜 E) :=
  Function.Injective.semilatticeSup _ FunLike.coe_injective coe_sup

end HasSmul

end AddGroupₓ

section Module

variable [AddCommGroupₓ E] [AddCommGroupₓ F] [AddCommGroupₓ G]

variable [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]

variable [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Seminorm 𝕜 E :=
  { p.toAddGroupSeminorm.comp f.toAddMonoidHom with toFun := fun x => p (f x),
    smul' := fun _ _ => (congr_arg p (f.map_smul _ _)).trans (p.smul _ _) }

theorem coe_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑(p.comp f) = p ∘ f :=
  rfl

@[simp]
theorem comp_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) :=
  rfl

@[simp]
theorem comp_id (p : Seminorm 𝕜 E) : p.comp LinearMap.id = p :=
  ext fun _ => rfl

@[simp]
theorem comp_zero (p : Seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
  ext fun _ => map_zero p

@[simp]
theorem zero_comp (f : E →ₗ[𝕜] F) : (0 : Seminorm 𝕜 F).comp f = 0 :=
  ext fun _ => rfl

theorem comp_comp (p : Seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl

theorem add_comp (p q : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl

theorem comp_add_le (p : Seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g := fun _ => p.add_le _ _

theorem smul_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • p.comp f :=
  ext fun _ => rfl

theorem comp_mono {p : Seminorm 𝕜 F} {q : Seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ =>
  hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps]
def pullback (f : E →ₗ[𝕜] F) : AddMonoidHom (Seminorm 𝕜 F) (Seminorm 𝕜 E) :=
  ⟨fun p => p.comp f, zero_comp f, fun p q => add_comp p q f⟩

section

variable (p : Seminorm 𝕜 E)

@[simp]
protected theorem neg (x : E) : p (-x) = p x := by
  rw [← neg_one_smul 𝕜, Seminorm.smul, norm_neg, ← Seminorm.smul, one_smul]

protected theorem sub_le (x y : E) : p (x - y) ≤ p x + p y :=
  calc
    p (x - y) = p (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ p x + p (-y) := p.add_le x (-y)
    _ = p x + p y := by
      rw [p.neg]
    

theorem sub_rev (x y : E) : p (x - y) = p (y - x) := by
  rw [← neg_sub, p.neg]

/-- The direct path from 0 to y is shorter than the path with x "inserted" in between. -/
theorem le_insert (x y : E) : p y ≤ p x + p (x - y) :=
  calc
    p y = p (x - (x - y)) := by
      rw [sub_sub_cancel]
    _ ≤ p x + p (x - y) := p.sub_le _ _
    

/-- The direct path from 0 to x is shorter than the path with y "inserted" in between. -/
theorem le_insert' (x y : E) : p x ≤ p y + p (x - y) := by
  rw [sub_rev]
  exact le_insert _ _ _

end

instance : OrderBot (Seminorm 𝕜 E) :=
  ⟨0, Seminorm.nonneg⟩

@[simp]
theorem coe_bot : ⇑(⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem bot_eq_zero : (⊥ : Seminorm 𝕜 E) = 0 :=
  rfl

theorem smul_le_smul {p q : Seminorm 𝕜 E} {a b : ℝ≥0 } (hpq : p ≤ q) (hab : a ≤ b) : a • p ≤ b • q := by
  simp_rw [le_def, Pi.le_def, coe_smul]
  intro x
  simp_rw [Pi.smul_apply, Nnreal.smul_def, smul_eq_mul]
  exact mul_le_mul hab (hpq x) (p.nonneg x) (Nnreal.coe_nonneg b)

theorem finset_sup_apply (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) :
    s.sup p x = ↑(s.sup fun i => ⟨p i x, (p i).Nonneg x⟩ : ℝ≥0 ) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · rw [Finset.sup_empty, Finset.sup_empty, coe_bot, _root_.bot_eq_zero, Pi.zero_apply, Nonneg.coe_zero]
    
  · rw [Finset.sup_cons, Finset.sup_cons, coe_sup, sup_eq_max, Pi.sup_apply, sup_eq_max, Nnreal.coe_max, Subtype.coe_mk,
      ih]
    

theorem finset_sup_le_sum (p : ι → Seminorm 𝕜 E) (s : Finset ι) : s.sup p ≤ ∑ i in s, p i := by
  classical
  refine' finset.sup_le_iff.mpr _
  intro i hi
  rw [Finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left]
  exact bot_le

theorem finset_sup_apply_le {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ i, i ∈ s → p i x ≤ a) : s.sup p x ≤ a := by
  lift a to ℝ≥0 using ha
  rw [finset_sup_apply, Nnreal.coe_le_coe]
  exact Finset.sup_le h

theorem finset_sup_apply_lt {p : ι → Seminorm 𝕜 E} {s : Finset ι} {x : E} {a : ℝ} (ha : 0 < a)
    (h : ∀ i, i ∈ s → p i x < a) : s.sup p x < a := by
  lift a to ℝ≥0 using ha.le
  rw [finset_sup_apply, Nnreal.coe_lt_coe, Finset.sup_lt_iff]
  · exact h
    
  · exact nnreal.coe_pos.mpr ha
    

end Module

end SemiNormedRing

section SemiNormedCommRing

variable [SemiNormedCommRing 𝕜] [AddCommGroupₓ E] [AddCommGroupₓ F] [Module 𝕜 E] [Module 𝕜 F]

theorem comp_smul (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) : p.comp (c • f) = ∥c∥₊ • p.comp f :=
  ext fun _ => by
    rw [comp_apply, smul_apply, LinearMap.smul_apply, p.smul, Nnreal.smul_def, coe_nnnorm, smul_eq_mul, comp_apply]

theorem comp_smul_apply (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) : p.comp (c • f) x = ∥c∥ * p (f x) :=
  p.smul _ _

end SemiNormedCommRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

private theorem bdd_below_range_add (x : E) (p q : Seminorm 𝕜 E) : BddBelow (Range fun u : E => p u + q (x - u)) := by
  use 0
  rintro _ ⟨x, rfl⟩
  exact add_nonneg (p.nonneg _) (q.nonneg _)

noncomputable instance :
    HasInf
      (Seminorm 𝕜
        E) where inf := fun p q =>
    { p.toAddGroupSeminorm⊓q.toAddGroupSeminorm with toFun := fun x => ⨅ u : E, p u + q (x - u),
      smul' := by
        intro a x
        obtain rfl | ha := eq_or_ne a 0
        · rw [norm_zero, zero_mul, zero_smul]
          refine'
            cinfi_eq_of_forall_ge_of_forall_gt_exists_lt (fun i => add_nonneg (p.nonneg _) (q.nonneg _)) fun x hx =>
              ⟨0, by
                rwa [map_zero, sub_zero, map_zero, add_zeroₓ]⟩
          
        simp_rw [Real.mul_infi_of_nonneg (norm_nonneg a), mul_addₓ, ← p.smul, ← q.smul, smul_sub]
        refine' Function.Surjective.infi_congr ((· • ·) a⁻¹ : E → E) (fun u => ⟨a • u, inv_smul_smul₀ ha u⟩) fun u => _
        rw [smul_inv_smul₀ ha] }

@[simp]
theorem inf_apply (p q : Seminorm 𝕜 E) (x : E) : (p⊓q) x = ⨅ u : E, p u + q (x - u) :=
  rfl

noncomputable instance : Lattice (Seminorm 𝕜 E) :=
  { Seminorm.semilatticeSup with inf := (·⊓·),
    inf_le_left := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) x
      simp only [← sub_self, ← map_zero, ← add_zeroₓ],
    inf_le_right := fun p q x => by
      apply cinfi_le_of_le (bdd_below_range_add _ _ _) (0 : E)
      simp only [← sub_self, ← map_zero, ← zero_addₓ, ← sub_zero],
    le_inf := fun a b c hab hac x => le_cinfi fun u => le_transₓ (a.le_insert' _ _) (add_le_add (hab _) (hac _)) }

theorem smul_inf [HasSmul R ℝ] [HasSmul R ℝ≥0 ] [IsScalarTower R ℝ≥0 ℝ] (r : R) (p q : Seminorm 𝕜 E) :
    r • (p⊓q) = r • p⊓r • q := by
  ext
  simp_rw [smul_apply, inf_apply, smul_apply, ← smul_one_smul ℝ≥0 r (_ : ℝ), Nnreal.smul_def, smul_eq_mul,
    Real.mul_infi_of_nonneg (Subtype.prop _), mul_addₓ]

end NormedField

/-! ### Seminorm ball -/


section SemiNormedRing

variable [SemiNormedRing 𝕜]

section AddCommGroupₓ

variable [AddCommGroupₓ E]

section HasSmul

variable [HasSmul 𝕜 E] (p : Seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def Ball (x : E) (r : ℝ) :=
  { y : E | p (y - x) < r }

variable {x y : E} {r : ℝ}

@[simp]
theorem mem_ball : y ∈ Ball p x r ↔ p (y - x) < r :=
  Iff.rfl

theorem mem_ball_zero : y ∈ Ball p 0 r ↔ p y < r := by
  rw [mem_ball, sub_zero]

theorem ball_zero_eq : Ball p 0 r = { y : E | p y < r } :=
  Set.ext fun x => p.mem_ball_zero

@[simp]
theorem ball_zero' (x : E) (hr : 0 < r) : Ball (0 : Seminorm 𝕜 E) x r = Set.Univ := by
  rw [Set.eq_univ_iff_forall, ball]
  simp [← hr]

theorem ball_smul (p : Seminorm 𝕜 E) {c : Nnreal} (hc : 0 < c) (r : ℝ) (x : E) : (c • p).ball x r = p.ball x (r / c) :=
  by
  ext
  rw [mem_ball, mem_ball, smul_apply, Nnreal.smul_def, smul_eq_mul, mul_comm, lt_div_iff (nnreal.coe_pos.mpr hc)]

theorem ball_sup (p : Seminorm 𝕜 E) (q : Seminorm 𝕜 E) (e : E) (r : ℝ) : Ball (p⊔q) e r = Ball p e r ∩ Ball q e r := by
  simp_rw [ball, ← Set.set_of_and, coe_sup, Pi.sup_apply, sup_lt_iff]

theorem ball_finset_sup' (p : ι → Seminorm 𝕜 E) (s : Finset ι) (H : s.Nonempty) (e : E) (r : ℝ) :
    Ball (s.sup' H p) e r = s.inf' H fun i => Ball (p i) e r := by
  induction' H using Finset.Nonempty.cons_induction with a a s ha hs ih
  · classical
    simp
    
  · rw [Finset.sup'_cons hs, Finset.inf'_cons hs, ball_sup, inf_eq_inter, ih]
    

theorem ball_mono {p : Seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ := fun _ (hx : _ < _) =>
  hx.trans_le h

theorem ball_antitone {p q : Seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r := fun _ => (h _).trans_lt

theorem ball_add_ball_subset (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E) :
    p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) := by
  rintro x ⟨y₁, y₂, hy₁, hy₂, rfl⟩
  rw [mem_ball, add_sub_add_comm]
  exact (p.add_le _ _).trans_lt (add_lt_add hy₁ hy₂)

end HasSmul

section Module

variable [Module 𝕜 E]

variable [AddCommGroupₓ F] [Module 𝕜 F]

theorem ball_comp (p : Seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) : (p.comp f).ball x r = f ⁻¹' p.ball (f x) r := by
  ext
  simp_rw [ball, mem_preimage, comp_apply, Set.mem_set_of_eq, map_sub]

variable (p : Seminorm 𝕜 E)

theorem ball_zero_eq_preimage_ball {r : ℝ} : p.ball 0 r = p ⁻¹' Metric.Ball 0 r := by
  ext x
  simp only [← mem_ball, ← sub_zero, ← mem_preimage, ← mem_ball_zero_iff]
  rw [Real.norm_of_nonneg]
  exact p.nonneg _

@[simp]
theorem ball_bot {r : ℝ} (x : E) (hr : 0 < r) : Ball (⊥ : Seminorm 𝕜 E) x r = Set.Univ :=
  ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
theorem balanced_ball_zero (r : ℝ) : Balanced 𝕜 (Ball p 0 r) := by
  rintro a ha x ⟨y, hy, hx⟩
  rw [mem_ball_zero, ← hx, p.smul]
  calc _ ≤ p y := mul_le_of_le_one_left (p.nonneg _) ha _ < r := by
      rwa [mem_ball_zero] at hy

theorem ball_finset_sup_eq_Inter (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    Ball (s.sup p) x r = ⋂ i ∈ s, Ball (p i) x r := by
  lift r to Nnreal using hr.le
  simp_rw [ball, Inter_set_of, finset_sup_apply, Nnreal.coe_lt_coe, Finset.sup_lt_iff (show ⊥ < r from hr), ←
    Nnreal.coe_lt_coe, Subtype.coe_mk]

theorem ball_finset_sup (p : ι → Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
    Ball (s.sup p) x r = s.inf fun i => Ball (p i) x r := by
  rw [Finset.inf_eq_infi]
  exact ball_finset_sup_eq_Inter _ _ _ hr

theorem ball_smul_ball (p : Seminorm 𝕜 E) (r₁ r₂ : ℝ) : Metric.Ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) := by
  rw [Set.subset_def]
  intro x hx
  rw [Set.mem_smul] at hx
  rcases hx with ⟨a, y, ha, hy, hx⟩
  rw [← hx, mem_ball_zero, Seminorm.smul]
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (p.nonneg y)

@[simp]
theorem ball_eq_emptyset (p : Seminorm 𝕜 E) {x : E} {r : ℝ} (hr : r ≤ 0) : p.ball x r = ∅ := by
  ext
  rw [Seminorm.mem_ball, Set.mem_empty_eq, iff_falseₓ, not_ltₓ]
  exact hr.trans (p.nonneg _)

end Module

end AddCommGroupₓ

end SemiNormedRing

section NormedField

variable [NormedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] (p : Seminorm 𝕜 E) {A B : Set E} {a : 𝕜} {r : ℝ} {x : E}

theorem smul_ball_zero {p : Seminorm 𝕜 E} {k : 𝕜} {r : ℝ} (hk : 0 < ∥k∥) : k • p.ball 0 r = p.ball 0 (∥k∥ * r) := by
  ext
  rw [Set.mem_smul_set, Seminorm.mem_ball_zero]
  constructor <;> intro h
  · rcases h with ⟨y, hy, h⟩
    rw [← h, Seminorm.smul]
    rw [Seminorm.mem_ball_zero] at hy
    exact (mul_lt_mul_left hk).mpr hy
    
  refine' ⟨k⁻¹ • x, _, _⟩
  · rw [Seminorm.mem_ball_zero, Seminorm.smul, norm_inv, ← mul_lt_mul_left hk, ← mul_assoc, ← div_eq_mul_inv ∥k∥ ∥k∥,
      div_self (ne_of_gtₓ hk), one_mulₓ]
    exact h
    
  rw [← smul_assoc, smul_eq_mul, ← div_eq_mul_inv, div_self (norm_pos_iff.mp hk), one_smul]

theorem ball_zero_absorbs_ball_zero (p : Seminorm 𝕜 E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) :
    Absorbs 𝕜 (p.ball 0 r₁) (p.ball 0 r₂) := by
  by_cases' hr₂ : r₂ ≤ 0
  · rw [ball_eq_emptyset p hr₂]
    exact absorbs_empty
    
  rw [not_leₓ] at hr₂
  rcases exists_between hr₁ with ⟨r, hr, hr'⟩
  refine' ⟨r₂ / r, div_pos hr₂ hr, _⟩
  simp_rw [Set.subset_def]
  intro a ha x hx
  have ha' : 0 < ∥a∥ := lt_of_lt_of_leₓ (div_pos hr₂ hr) ha
  rw [smul_ball_zero ha', p.mem_ball_zero]
  rw [p.mem_ball_zero] at hx
  rw [div_le_iff hr] at ha
  exact hx.trans (lt_of_le_of_ltₓ ha ((mul_lt_mul_left ha').mpr hr'))

/-- Seminorm-balls at the origin are absorbent. -/
protected theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Ball p (0 : E) r) := by
  rw [absorbent_iff_nonneg_lt]
  rintro x
  have hxr : 0 ≤ p x / r := div_nonneg (p.nonneg _) hr.le
  refine' ⟨p x / r, hxr, fun a ha => _⟩
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha
  refine' ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ← div_lt_iff hr]

/-- Seminorm-balls containing the origin are absorbent. -/
protected theorem absorbent_ball (hpr : p x < r) : Absorbent 𝕜 (Ball p x r) := by
  refine' (p.absorbent_ball_zero <| sub_pos.2 hpr).Subset fun y hy => _
  rw [p.mem_ball_zero] at hy
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt <| add_lt_of_lt_sub_right hy)

theorem symmetric_ball_zero (r : ℝ) (hx : x ∈ Ball p 0 r) : -x ∈ Ball p 0 r :=
  balanced_ball_zero p r (-1)
    (by
      rw [norm_neg, norm_one])
    ⟨x, hx, by
      rw [neg_smul, one_smul]⟩

@[simp]
theorem neg_ball (p : Seminorm 𝕜 E) (r : ℝ) (x : E) : -Ball p x r = Ball p (-x) r := by
  ext
  rw [mem_neg, mem_ball, mem_ball, ← neg_add', sub_neg_eq_add, p.neg]

@[simp]
theorem smul_ball_preimage (p : Seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
    (· • ·) a ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
  Set.ext fun _ => by
    rw [mem_preimage, mem_ball, mem_ball, lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ← p.smul, smul_sub,
      smul_inv_smul₀ ha]

end NormedField

section Convex

variable [NormedField 𝕜] [AddCommGroupₓ E] [NormedSpace ℝ 𝕜] [Module 𝕜 E]

section HasSmul

variable [HasSmul ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected theorem convex_on : ConvexOn ℝ Univ p := by
  refine' ⟨convex_univ, fun x y _ _ a b ha hb hab => _⟩
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) := p.add_le _ _ _ = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y := by
      rw [← p.smul, ← p.smul, smul_one_smul, smul_one_smul]_ = a * p x + b * p y := by
      rw [norm_smul, norm_smul, norm_one, mul_oneₓ, mul_oneₓ, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]

end HasSmul

section Module

variable [Module ℝ E] [IsScalarTower ℝ 𝕜 E] (p : Seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
theorem convex_ball : Convex ℝ (Ball p x r) := by
  convert (p.convex_on.translate_left (-x)).convex_lt r
  ext y
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg]
  rfl

end Module

end Convex

end Seminorm

/-! ### The norm as a seminorm -/


section normSeminorm

variable (𝕜) (E) [NormedField 𝕜] [SemiNormedGroup E] [NormedSpace 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as an add_monoid seminorm. -/
def normAddGroupSeminorm : AddGroupSeminorm E :=
  ⟨norm, norm_zero, norm_nonneg, norm_add_le, norm_neg⟩

@[simp]
theorem coe_norm_add_group_seminorm : ⇑(normAddGroupSeminorm E) = norm :=
  rfl

/-- The norm of a seminormed group as a seminorm. -/
def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

@[simp]
theorem coe_norm_seminorm : ⇑(normSeminorm 𝕜 E) = norm :=
  rfl

@[simp]
theorem ball_norm_seminorm : (normSeminorm 𝕜 E).ball = Metric.Ball := by
  ext x r y
  simp only [← Seminorm.mem_ball, ← Metric.mem_ball, ← coe_norm_seminorm, ← dist_eq_norm]

variable {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ∥x∥ < r) : Absorbent 𝕜 (Metric.Ball x r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.Ball (0 : E) r) := by
  rw [← ball_norm_seminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

end normSeminorm

