/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.Group.Pi
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Pi instances for multiplicative actions

This file defines instances for mul_action and related structures on Pi types.

## See also

* `group_theory.group_action.option`
* `group_theory.group_action.prod`
* `group_theory.group_action.sigma`
* `group_theory.group_action.sum`
-/


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

namespace Pi

@[to_additive Pi.hasVadd]
instance hasSmul {α : Type _} [∀ i, HasSmul α <| f i] : HasSmul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

@[to_additive]
theorem smul_def {α : Type _} [∀ i, HasSmul α <| f i] (s : α) : s • x = fun i => s • x i :=
  rfl

@[simp, to_additive]
theorem smul_apply {α : Type _} [∀ i, HasSmul α <| f i] (s : α) : (s • x) i = s • x i :=
  rfl

@[to_additive Pi.hasVadd']
instance hasSmul' {g : I → Type _} [∀ i, HasSmul (f i) (g i)] : HasSmul (∀ i, f i) (∀ i : I, g i) :=
  ⟨fun s x => fun i => s i • x i⟩

@[simp, to_additive]
theorem smul_apply' {g : I → Type _} [∀ i, HasSmul (f i) (g i)] (s : ∀ i, f i) (x : ∀ i, g i) : (s • x) i = s i • x i :=
  rfl

instance is_scalar_tower {α β : Type _} [HasSmul α β] [∀ i, HasSmul β <| f i] [∀ i, HasSmul α <| f i]
    [∀ i, IsScalarTower α β (f i)] : IsScalarTower α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_assoc x y (z i)⟩

instance is_scalar_tower' {g : I → Type _} {α : Type _} [∀ i, HasSmul α <| f i] [∀ i, HasSmul (f i) (g i)]
    [∀ i, HasSmul α <| g i] [∀ i, IsScalarTower α (f i) (g i)] : IsScalarTower α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_assoc x (y i) (z i)⟩

instance is_scalar_tower'' {g : I → Type _} {h : I → Type _} [∀ i, HasSmul (f i) (g i)] [∀ i, HasSmul (g i) (h i)]
    [∀ i, HasSmul (f i) (h i)] [∀ i, IsScalarTower (f i) (g i) (h i)] :
    IsScalarTower (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_assoc (x i) (y i) (z i)⟩

@[to_additive]
instance smul_comm_class {α β : Type _} [∀ i, HasSmul α <| f i] [∀ i, HasSmul β <| f i] [∀ i, SmulCommClass α β (f i)] :
    SmulCommClass α β (∀ i : I, f i) :=
  ⟨fun x y z => funext fun i => smul_comm x y (z i)⟩

@[to_additive]
instance smul_comm_class' {g : I → Type _} {α : Type _} [∀ i, HasSmul α <| g i] [∀ i, HasSmul (f i) (g i)]
    [∀ i, SmulCommClass α (f i) (g i)] : SmulCommClass α (∀ i : I, f i) (∀ i : I, g i) :=
  ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩

@[to_additive]
instance smul_comm_class'' {g : I → Type _} {h : I → Type _} [∀ i, HasSmul (g i) (h i)] [∀ i, HasSmul (f i) (h i)]
    [∀ i, SmulCommClass (f i) (g i) (h i)] : SmulCommClass (∀ i, f i) (∀ i, g i) (∀ i, h i) :=
  ⟨fun x y z => funext fun i => smul_comm (x i) (y i) (z i)⟩

instance {α : Type _} [∀ i, HasSmul α <| f i] [∀ i, HasSmul αᵐᵒᵖ <| f i] [∀ i, IsCentralScalar α (f i)] :
    IsCentralScalar α (∀ i, f i) :=
  ⟨fun r m => funext fun i => op_smul_eq_smul _ _⟩

/-- If `f i` has a faithful scalar action for a given `i`, then so does `Π i, f i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive Pi.has_faithful_vadd_at]
theorem has_faithful_smul_at {α : Type _} [∀ i, HasSmul α <| f i] [∀ i, Nonempty (f i)] (i : I)
    [HasFaithfulSmul α (f i)] : HasFaithfulSmul α (∀ i, f i) :=
  ⟨fun x y h =>
    eq_of_smul_eq_smul fun a : f i => by
      classical
      have := congr_fun (h <| Function.update (fun j => Classical.choice (‹∀ i, Nonempty (f i)› j)) i a) i
      simpa using this⟩

@[to_additive Pi.has_faithful_vadd]
instance has_faithful_smul {α : Type _} [Nonempty I] [∀ i, HasSmul α <| f i] [∀ i, Nonempty (f i)]
    [∀ i, HasFaithfulSmul α (f i)] : HasFaithfulSmul α (∀ i, f i) :=
  let ⟨i⟩ := ‹Nonempty I›
  has_faithful_smul_at i

@[to_additive]
instance mulAction (α) {m : Monoidₓ α} [∀ i, MulAction α <| f i] : @MulAction α (∀ i : I, f i) m where
  smul := (· • ·)
  mul_smul := fun r s f => funext fun i => mul_smul _ _ _
  one_smul := fun f => funext fun i => one_smul α _

@[to_additive]
instance mulAction' {g : I → Type _} {m : ∀ i, Monoidₓ (f i)} [∀ i, MulAction (f i) (g i)] :
    @MulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) where
  smul := (· • ·)
  mul_smul := fun r s f => funext fun i => mul_smul _ _ _
  one_smul := fun f => funext fun i => one_smul _ _

instance distribMulAction (α) {m : Monoidₓ α} {n : ∀ i, AddMonoidₓ <| f i} [∀ i, DistribMulAction α <| f i] :
    @DistribMulAction α (∀ i : I, f i) m (@Pi.addMonoid I f n) :=
  { Pi.mulAction _ with smul_zero := fun c => funext fun i => smul_zero _,
    smul_add := fun c f g => funext fun i => smul_add _ _ _ }

instance distribMulAction' {g : I → Type _} {m : ∀ i, Monoidₓ (f i)} {n : ∀ i, AddMonoidₓ <| g i}
    [∀ i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n) where
  smul_add := by
    intros
    ext x
    apply smul_add
  smul_zero := by
    intros
    ext x
    apply smul_zero

theorem single_smul {α} [Monoidₓ α] [∀ i, AddMonoidₓ <| f i] [∀ i, DistribMulAction α <| f i] [DecidableEq I] (i : I)
    (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => ((· • ·) r : f i → f i)) (fun j => smul_zero _) _ _

/-- A version of `pi.single_smul` for non-dependent functions. It is useful in cases Lean fails
to apply `pi.single_smul`. -/
theorem single_smul' {α β} [Monoidₓ α] [AddMonoidₓ β] [DistribMulAction α β] [DecidableEq I] (i : I) (r : α) (x : β) :
    single i (r • x) = r • single i x :=
  single_smul i r x

theorem single_smul₀ {g : I → Type _} [∀ i, MonoidWithZeroₓ (f i)] [∀ i, AddMonoidₓ (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x :=
  single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun j => smul_zero _) _ _ _

instance mulDistribMulAction (α) {m : Monoidₓ α} {n : ∀ i, Monoidₓ <| f i} [∀ i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (∀ i : I, f i) m (@Pi.monoid I f n) :=
  { Pi.mulAction _ with smul_one := fun c => funext fun i => smul_one _,
    smul_mul := fun c f g => funext fun i => smul_mul' _ _ _ }

instance mulDistribMulAction' {g : I → Type _} {m : ∀ i, Monoidₓ (f i)} {n : ∀ i, Monoidₓ <| g i}
    [∀ i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g n) where
  smul_mul := by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one

end Pi

namespace Function

/-- Non-dependent version of `pi.has_smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive]
instance hasSmul {ι R M : Type _} [HasSmul R M] : HasSmul R (ι → M) :=
  Pi.hasSmul

/-- Non-dependent version of `pi.smul_comm_class`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive]
instance smul_comm_class {ι α β M : Type _} [HasSmul α M] [HasSmul β M] [SmulCommClass α β M] :
    SmulCommClass α β (ι → M) :=
  Pi.smul_comm_class

@[to_additive]
theorem update_smul {α : Type _} [∀ i, HasSmul α (f i)] [DecidableEq I] (c : α) (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (fun i => (· • ·) c) f₁ i x₁ j).symm

end Function

namespace Set

@[to_additive]
theorem piecewise_smul {α : Type _} [∀ i, HasSmul α (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (c : α)
    (f₁ g₁ : ∀ i, f i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op _ _ fun _ => (· • ·) c

end Set

section Extend

@[to_additive]
theorem Function.extend_smul {R α β γ : Type _} [HasSmul R γ] (r : R) (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extendₓ f (r • g) (r • e) = r • Function.extendₓ f g e :=
  funext fun _ => by
    convert (apply_dite ((· • ·) r) _ _ _).symm

end Extend

