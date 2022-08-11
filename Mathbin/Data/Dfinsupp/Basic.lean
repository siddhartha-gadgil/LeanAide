/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.Module.LinearMap
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Submonoid.Membership
import Mathbin.Data.Finset.Preimage

/-!
# Dependent functions with finite support

For a non-dependent version see `data/finsupp.lean`.
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open BigOperators

variable (ι : Type u) {γ : Type w} (β : ι → Type v) {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace Dfinsupp

variable [∀ i, Zero (β i)]

/-- An auxiliary structure used in the definition of of `dfinsupp`,
the type used to make infinite direct sum of modules over a ring. -/
structure Pre : Type max u v where
  toFun : ∀ i, β i
  preSupport : Multiset ι
  zero : ∀ i, i ∈ pre_support ∨ to_fun i = 0

instance inhabitedPre : Inhabited (Pre ι β) :=
  ⟨⟨fun i => 0, ∅, fun i => Or.inr rfl⟩⟩

instance : Setoidₓ (Pre ι β) where
  R := fun x y => ∀ i, x.toFun i = y.toFun i
  iseqv := ⟨fun f i => rfl, fun f g H i => (H i).symm, fun f g h H1 H2 i => (H1 i).trans (H2 i)⟩

end Dfinsupp

variable {ι}

/-- A dependent function `Π i, β i` with finite support. -/
@[reducible]
def Dfinsupp [∀ i, Zero (β i)] : Type _ :=
  Quotientₓ (Dfinsupp.Pre.setoid ι β)

variable {β}

-- mathport name: «exprΠ₀ , »
notation3"Π₀ "(...)", "r:(scoped f => Dfinsupp f) => r

-- mathport name: «expr →ₚ »
infixl:25 " →ₚ " => Dfinsupp

namespace Dfinsupp

section Basic

variable [∀ i, Zero (β i)] [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

instance funLike : FunLike (Π₀ i, β i) ι β :=
  ⟨fun f => (Quotientₓ.liftOn f Pre.toFun) fun _ _ => funext, fun f g H =>
    Quotientₓ.induction_on₂ f g (fun _ _ H => Quotientₓ.sound H) (congr_fun H)⟩

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Π₀ i, β i) fun _ => ∀ i, β i :=
  FunLike.hasCoeToFun

@[ext]
theorem ext {f g : Π₀ i, β i} (h : ∀ i, f i = g i) : f = g :=
  FunLike.ext _ _ h

/-- Deprecated. Use `fun_like.ext_iff` instead. -/
theorem ext_iff {f g : Π₀ i, β i} : f = g ↔ ∀ i, f i = g i :=
  FunLike.ext_iff

/-- Deprecated. Use `fun_like.coe_injective` instead. -/
theorem coe_fn_injective : @Function.Injective (Π₀ i, β i) (∀ i, β i) coeFn :=
  FunLike.coe_injective

instance : Zero (Π₀ i, β i) :=
  ⟨⟦⟨0, ∅, fun i => Or.inr rfl⟩⟧⟩

instance : Inhabited (Π₀ i, β i) :=
  ⟨0⟩

@[simp]
theorem coe_pre_mk (f : ∀ i, β i) (s : Multiset ι) (hf) : ⇑(⟦⟨f, s, hf⟩⟧ : Π₀ i, β i) = f :=
  rfl

@[simp]
theorem coe_zero : ⇑(0 : Π₀ i, β i) = 0 :=
  rfl

theorem zero_apply (i : ι) : (0 : Π₀ i, β i) i = 0 :=
  rfl

/-- The composition of `f : β₁ → β₂` and `g : Π₀ i, β₁ i` is
  `map_range f hf g : Π₀ i, β₂ i`, well defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `dfinsupp.map_range.add_monoid_hom`
* `dfinsupp.map_range.add_equiv`
* `dfinsupp.map_range.linear_map`
* `dfinsupp.map_range.linear_equiv`
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) : (Π₀ i, β₁ i) → Π₀ i, β₂ i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => f i (x.1 i), x.2, fun i =>
        (x.3 i).imp_right fun H => by
          rw [H, hf]⟩)
    fun x y H i => by
    simp only [← H i]

@[simp]
theorem map_range_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) :
    mapRange f hf g i = f i (g i) :=
  (Quotientₓ.induction_on g) fun x => rfl

@[simp]
theorem map_range_id (h : ∀ i, id (0 : β₁ i) = 0 := fun i => rfl) (g : Π₀ i : ι, β₁ i) :
    mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  simp only [← map_range_apply, ← id.def]

theorem map_range_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i) (hf : ∀ i, f i 0 = 0) (hf₂ : ∀ i, f₂ i 0 = 0)
    (h : ∀ i, (f i ∘ f₂ i) 0 = 0) (g : Π₀ i : ι, β i) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [← map_range_apply]

@[simp]
theorem map_range_zero (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) : mapRange f hf (0 : Π₀ i, β₁ i) = 0 := by
  ext
  simp only [← map_range_apply, ← coe_zero, ← Pi.zero_apply, ← hf]

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i 0 0 = 0`.
Then `zip_with f hf` is a binary operation `Π₀ i, β₁ i → Π₀ i, β₂ i → Π₀ i, β i`. -/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) : (Π₀ i, β₁ i) → (Π₀ i, β₂ i) → Π₀ i, β i := by
  refine' Quotientₓ.map₂ (fun x y => ⟨fun i => f i (x.1 i) (y.1 i), x.2 + y.2, fun i => _⟩) _
  · cases' x.3 i with h1 h1
    · left
      rw [Multiset.mem_add]
      left
      exact h1
      
    cases' y.3 i with h2 h2
    · left
      rw [Multiset.mem_add]
      right
      exact h2
      
    right
    rw [h1, h2, hf]
    
  exact fun x₁ x₂ H1 y₁ y₂ H2 i => by
    simp only [← H1 i, ← H2 i]

@[simp]
theorem zip_with_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i 0 0 = 0) (g₁ : Π₀ i, β₁ i) (g₂ : Π₀ i, β₂ i)
    (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  (Quotientₓ.induction_on₂ g₁ g₂) fun _ _ => rfl

end Basic

section Algebra

instance [∀ i, AddZeroClassₓ (β i)] : Add (Π₀ i, β i) :=
  ⟨zipWith (fun _ => (· + ·)) fun _ => add_zeroₓ 0⟩

theorem add_apply [∀ i, AddZeroClassₓ (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  zip_with_apply _ _ g₁ g₂ i

@[simp]
theorem coe_add [∀ i, AddZeroClassₓ (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ + g₂) = g₁ + g₂ :=
  funext <| add_apply g₁ g₂

instance [∀ i, AddZeroClassₓ (β i)] : AddZeroClassₓ (Π₀ i, β i) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

/-- Note the general `dfinsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar [∀ i, AddMonoidₓ (β i)] : HasSmul ℕ (Π₀ i, β i) :=
  ⟨fun c v => v.map_range (fun _ => (· • ·) c) fun _ => nsmul_zero _⟩

theorem nsmul_apply [∀ i, AddMonoidₓ (β i)] (b : ℕ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  map_range_apply _ _ v i

@[simp]
theorem coe_nsmul [∀ i, AddMonoidₓ (β i)] (b : ℕ) (v : Π₀ i, β i) : ⇑(b • v) = b • v :=
  funext <| nsmul_apply b v

instance [∀ i, AddMonoidₓ (β i)] : AddMonoidₓ (Π₀ i, β i) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- Coercion from a `dfinsupp` to a pi type is an `add_monoid_hom`. -/
def coeFnAddMonoidHom [∀ i, AddZeroClassₓ (β i)] : (Π₀ i, β i) →+ ∀ i, β i where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add

/-- Evaluation at a point is an `add_monoid_hom`. This is the finitely-supported version of
`pi.eval_add_monoid_hom`. -/
def evalAddMonoidHom [∀ i, AddZeroClassₓ (β i)] (i : ι) : (Π₀ i, β i) →+ β i :=
  (Pi.evalAddMonoidHom β i).comp coeFnAddMonoidHom

instance [∀ i, AddCommMonoidₓ (β i)] : AddCommMonoidₓ (Π₀ i, β i) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

@[simp]
theorem coe_finset_sum {α} [∀ i, AddCommMonoidₓ (β i)] (s : Finset α) (g : α → Π₀ i, β i) :
    ⇑(∑ a in s, g a) = ∑ a in s, g a :=
  (coeFnAddMonoidHom : _ →+ ∀ i, β i).map_sum g s

@[simp]
theorem finset_sum_apply {α} [∀ i, AddCommMonoidₓ (β i)] (s : Finset α) (g : α → Π₀ i, β i) (i : ι) :
    (∑ a in s, g a) i = ∑ a in s, g a i :=
  (evalAddMonoidHom i : _ →+ β i).map_sum g s

instance [∀ i, AddGroupₓ (β i)] : Neg (Π₀ i, β i) :=
  ⟨fun f => f.map_range (fun _ => Neg.neg) fun _ => neg_zero⟩

theorem neg_apply [∀ i, AddGroupₓ (β i)] (g : Π₀ i, β i) (i : ι) : (-g) i = -g i :=
  map_range_apply _ _ g i

@[simp]
theorem coe_neg [∀ i, AddGroupₓ (β i)] (g : Π₀ i, β i) : ⇑(-g) = -g :=
  funext <| neg_apply g

instance [∀ i, AddGroupₓ (β i)] : Sub (Π₀ i, β i) :=
  ⟨zipWith (fun _ => Sub.sub) fun _ => sub_zero 0⟩

theorem sub_apply [∀ i, AddGroupₓ (β i)] (g₁ g₂ : Π₀ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  zip_with_apply _ _ g₁ g₂ i

@[simp]
theorem coe_sub [∀ i, AddGroupₓ (β i)] (g₁ g₂ : Π₀ i, β i) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  funext <| sub_apply g₁ g₂

/-- Note the general `dfinsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [∀ i, AddGroupₓ (β i)] : HasSmul ℤ (Π₀ i, β i) :=
  ⟨fun c v => v.map_range (fun _ => (· • ·) c) fun _ => zsmul_zero _⟩

theorem zsmul_apply [∀ i, AddGroupₓ (β i)] (b : ℤ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  map_range_apply _ _ v i

@[simp]
theorem coe_zsmul [∀ i, AddGroupₓ (β i)] (b : ℤ) (v : Π₀ i, β i) : ⇑(b • v) = b • v :=
  funext <| zsmul_apply b v

instance [∀ i, AddGroupₓ (β i)] : AddGroupₓ (Π₀ i, β i) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _) fun _ _ => coe_zsmul _ _

instance [∀ i, AddCommGroupₓ (β i)] : AddCommGroupₓ (Π₀ i, β i) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _) fun _ _ =>
    coe_zsmul _ _

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
instance [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] : HasSmul γ (Π₀ i, β i) :=
  ⟨fun c v => v.map_range (fun _ => (· • ·) c) fun _ => smul_zero _⟩

theorem smul_apply [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) :
    (b • v) i = b • v i :=
  map_range_apply _ _ v i

@[simp]
theorem coe_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (b : γ) (v : Π₀ i, β i) :
    ⇑(b • v) = b • v :=
  funext <| smul_apply b v

instance {δ : Type _} [Monoidₓ γ] [Monoidₓ δ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction δ (β i)] [∀ i, SmulCommClass γ δ (β i)] :
    SmulCommClass γ δ (Π₀ i, β i) where smul_comm := fun r s m =>
    ext fun i => by
      simp only [← smul_apply, ← smul_comm r s (m i)]

instance {δ : Type _} [Monoidₓ γ] [Monoidₓ δ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]
    [∀ i, DistribMulAction δ (β i)] [HasSmul γ δ] [∀ i, IsScalarTower γ δ (β i)] :
    IsScalarTower γ δ (Π₀ i, β i) where smul_assoc := fun r s m =>
    ext fun i => by
      simp only [← smul_apply, ← smul_assoc r s (m i)]

instance [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] [∀ i, DistribMulAction γᵐᵒᵖ (β i)]
    [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where op_smul_eq_smul := fun r m =>
    ext fun i => by
      simp only [← smul_apply, ← op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `distrib_mul_action` structure from such a
structure on each coordinate. -/
instance [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] : DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom FunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
instance [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] : Module γ (Π₀ i, β i) :=
  { Dfinsupp.distribMulAction with
    zero_smul := fun c =>
      ext fun i => by
        simp only [← smul_apply, ← zero_smul, ← zero_apply],
    add_smul := fun c x y =>
      ext fun i => by
        simp only [← add_apply, ← smul_apply, ← add_smul] }

end Algebra

section FilterAndSubtypeDomain

/-- `filter p f` is the function which is `f i` if `p i` is true and 0 otherwise. -/
def filter [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) → Π₀ i, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => if p i then x.1 i else 0, x.2, fun i =>
        (x.3 i).imp_right fun H => by
          rw [H, if_t_t]⟩)
    fun x y H i => by
    simp only [← H i]

@[simp]
theorem filter_apply [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀ i, β i) :
    f.filter p i = if p i then f i else 0 :=
  (Quotientₓ.induction_on f) fun x => rfl

theorem filter_apply_pos [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι} (h : p i) :
    f.filter p i = f i := by
  simp only [← filter_apply, ← if_pos h]

theorem filter_apply_neg [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] (f : Π₀ i, β i) {i : ι} (h : ¬p i) :
    f.filter p i = 0 := by
  simp only [← filter_apply, ← if_neg h]

theorem filter_pos_add_filter_neg [∀ i, AddZeroClassₓ (β i)] (f : Π₀ i, β i) (p : ι → Prop) [DecidablePred p] :
    (f.filter p + f.filter fun i => ¬p i) = f :=
  ext fun i => by
    simp only [← add_apply, ← filter_apply] <;> split_ifs <;> simp only [← add_zeroₓ, ← zero_addₓ]

@[simp]
theorem filter_zero [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] : (0 : Π₀ i, β i).filter p = 0 := by
  ext
  simp

@[simp]
theorem filter_add [∀ i, AddZeroClassₓ (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f + g).filter p = f.filter p + g.filter p := by
  ext
  simp [← ite_add_zero]

@[simp]
theorem filter_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (p : ι → Prop) [DecidablePred p]
    (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p := by
  ext
  simp [← smul_ite]

variable (γ β)

/-- `dfinsupp.filter` as an `add_monoid_hom`. -/
@[simps]
def filterAddMonoidHom [∀ i, AddZeroClassₓ (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := filter_add p

/-- `dfinsupp.filter` as a `linear_map`. -/
@[simps]
def filterLinearMap [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i, β i) →ₗ[γ] Π₀ i, β i where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

variable {γ β}

@[simp]
theorem filter_neg [∀ i, AddGroupₓ (β i)] (p : ι → Prop) [DecidablePred p] (f : Π₀ i, β i) :
    (-f).filter p = -f.filter p :=
  (filterAddMonoidHom β p).map_neg f

@[simp]
theorem filter_sub [∀ i, AddGroupₓ (β i)] (p : ι → Prop) [DecidablePred p] (f g : Π₀ i, β i) :
    (f - g).filter p = f.filter p - g.filter p :=
  (filterAddMonoidHom β p).map_sub f g

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain [∀ i, Zero (β i)] (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) → Π₀ i : Subtype p, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun i => x.1 (i : ι), (x.2.filter p).attach.map fun j => ⟨j, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (x.3 i).imp_left fun H =>
          Multiset.mem_map.2 ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩)
    fun x y H i => H i

@[simp]
theorem subtype_domain_zero [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] : subtypeDomain p (0 : Π₀ i, β i) = 0 :=
  rfl

@[simp]
theorem subtype_domain_apply [∀ i, Zero (β i)] {p : ι → Prop} [DecidablePred p] {i : Subtype p} {v : Π₀ i, β i} :
    (subtypeDomain p v) i = v i :=
  (Quotientₓ.induction_on v) fun x => rfl

@[simp]
theorem subtype_domain_add [∀ i, AddZeroClassₓ (β i)] {p : ι → Prop} [DecidablePred p] (v v' : Π₀ i, β i) :
    (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun i => by
    simp only [← add_apply, ← subtype_domain_apply]

@[simp]
theorem subtype_domain_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] {p : ι → Prop}
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  (Quotientₓ.induction_on f) fun x => rfl

variable (γ β)

/-- `subtype_domain` but as an `add_monoid_hom`. -/
@[simps]
def subtypeDomainAddMonoidHom [∀ i, AddZeroClassₓ (β i)] (p : ι → Prop) [DecidablePred p] :
    (Π₀ i : ι, β i) →+ Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_zero' := subtype_domain_zero
  map_add' := subtype_domain_add

/-- `dfinsupp.subtype_domain` as a `linear_map`. -/
@[simps]
def subtypeDomainLinearMap [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_add' := subtype_domain_add
  map_smul' := subtype_domain_smul

variable {γ β}

@[simp]
theorem subtype_domain_neg [∀ i, AddGroupₓ (β i)] {p : ι → Prop} [DecidablePred p] {v : Π₀ i, β i} :
    (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun i => by
    simp only [← neg_apply, ← subtype_domain_apply]

@[simp]
theorem subtype_domain_sub [∀ i, AddGroupₓ (β i)] {p : ι → Prop} [DecidablePred p] {v v' : Π₀ i, β i} :
    (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun i => by
    simp only [← sub_apply, ← subtype_domain_apply]

end FilterAndSubtypeDomain

variable [dec : DecidableEq ι]

include dec

section Basic

variable [∀ i, Zero (β i)]

omit dec

theorem finite_support (f : Π₀ i, β i) : Set.Finite { i | f i ≠ 0 } := by
  classical
  exact
    Quotientₓ.induction_on f fun x =>
      x.2.toFinset.finite_to_set.Subset fun i H => Multiset.mem_to_finset.2 ((x.3 i).resolve_right H)

include dec

/-- Create an element of `Π₀ i, β i` from a finset `s` and a function `x`
defined on this `finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀ i, β i :=
  ⟦⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else 0, s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟧

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else 0 :=
  rfl

theorem mk_of_mem (hi : i ∈ s) : (mk s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi

theorem mk_of_not_mem (hi : i ∉ s) : (mk s x : ∀ i, β i) i = 0 :=
  dif_neg hi

theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β _ _ s) := by
  intro x y H
  ext i
  have h1 : (mk s x : ∀ i, β i) i = (mk s y : ∀ i, β i) i := by
    rw [H]
  cases' i with i hi
  change i ∈ s at hi
  dsimp' only [← mk_apply, ← Subtype.coe_mk]  at h1
  simpa only [← dif_pos hi] using h1

omit dec

instance [IsEmpty ι] : Unique (Π₀ i, β i) :=
  ⟨⟨0⟩, fun a => by
    ext
    exact isEmptyElim i⟩

/-- Given `fintype ι`, `equiv_fun_on_fintype` is the `equiv` between `Π₀ i, β i` and `Π i, β i`.
  (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀ i, β i) ≃ ∀ i, β i where
  toFun := coeFn
  invFun := fun f => ⟦⟨f, Finset.univ.1, fun i => Or.inl <| Finset.mem_univ_val _⟩⟧
  left_inv := fun x => coe_fn_injective rfl
  right_inv := fun x => rfl

@[simp]
theorem equiv_fun_on_fintype_symm_coe [Fintype ι] (f : Π₀ i, β i) : equivFunOnFintype.symm f = f :=
  Equivₓ.symm_apply_apply _ _

include dec

/-- The function `single i b : Π₀ i, β i` sends `i` to `b`
and all other points to `0`. -/
def single (i : ι) (b : β i) : Π₀ i, β i :=
  (mk {i}) fun j => Eq.recOnₓ (Finset.mem_singleton.1 j.Prop).symm b

@[simp]
theorem single_apply {i i' b} : (single i b : Π₀ i, β i) i' = if h : i = i' then Eq.recOnₓ h b else 0 := by
  dsimp' only [← single]
  by_cases' h : i = i'
  · have h1 : i' ∈ ({i} : Finset ι) := Finset.mem_singleton.2 h.symm
    simp only [← mk_apply, ← dif_pos h, ← dif_pos h1]
    rfl
    
  · have h1 : i' ∉ ({i} : Finset ι) := Finset.not_mem_singleton.2 (Ne.symm h)
    simp only [← mk_apply, ← dif_neg h, ← dif_neg h1]
    

theorem single_eq_pi_single {i b} : ⇑(single i b : Π₀ i, β i) = Pi.single i b := by
  ext i'
  simp only [← Pi.single, ← Function.update]
  split_ifs
  · simp [← h]
    
  · simp [← Ne.symm h]
    

@[simp]
theorem single_zero (i) : (single i 0 : Π₀ i, β i) = 0 :=
  Quotientₓ.sound fun j =>
    if H : j ∈ ({i} : Finset _) then by
      dsimp' only <;> rw [dif_pos H] <;> cases Finset.mem_singleton.1 H <;> rfl
    else dif_neg H

@[simp]
theorem single_eq_same {i b} : (single i b : Π₀ i, β i) i = b := by
  simp only [← single_apply, ← dif_pos rfl]

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : (single i b : Π₀ i, β i) i' = 0 := by
  simp only [← single_apply, ← dif_neg h]

theorem single_injective {i} : Function.Injective (single i : β i → Π₀ i, β i) := fun x y H =>
  congr_fun (mk_injective _ H)
    ⟨i, by
      simp ⟩

/-- Like `finsupp.single_eq_single_iff`, but with a `heq` due to dependent types -/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    Dfinsupp.single i xi = Dfinsupp.single j xj ↔ i = j ∧ HEq xi xj ∨ xi = 0 ∧ xj = 0 := by
  constructor
  · intro h
    by_cases' hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (Dfinsupp.single_injective h)⟩
      
    · have h_coe : ⇑(Dfinsupp.single i xi) = Dfinsupp.single j xj := congr_arg coeFn h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [Dfinsupp.single_eq_same] at hci hcj
      rw [Dfinsupp.single_eq_of_ne (Ne.symm hij)] at hci
      rw [Dfinsupp.single_eq_of_ne hij] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
      
    
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
      
    · rw [hi, hj, Dfinsupp.single_zero, Dfinsupp.single_zero]
      
    

@[simp]
theorem single_eq_zero {i : ι} {xi : β i} : single i xi = 0 ↔ xi = 0 := by
  rw [← single_zero i, single_eq_single_iff]
  simp

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single i x).filter p = if p i then single i x else 0 := by
  ext j
  have := apply_ite (fun x : Π₀ i, β i => x j) (p i) (single i x) 0
  dsimp'  at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
    
  · rw [single_eq_of_ne hij, if_t_t, if_t_t]
    

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single i x).filter p = single i x := by
  rw [filter_single, if_pos h]

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) : (single i x).filter p = 0 :=
  by
  rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `dfinsupp`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    Dfinsupp.single i xi = Dfinsupp.single j xj := by
  cases h
  rfl

@[simp]
theorem equiv_fun_on_fintype_single [Fintype ι] (i : ι) (m : β i) :
    (@Dfinsupp.equivFunOnFintype ι β _ _) (Dfinsupp.single i m) = Pi.single i m := by
  ext
  simp [← Dfinsupp.single_eq_pi_single]

@[simp]
theorem equiv_fun_on_fintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@Dfinsupp.equivFunOnFintype ι β _ _).symm (Pi.single i m) = Dfinsupp.single i m := by
  ext i'
  simp only [single_eq_pi_single, ← equiv_fun_on_fintype_symm_coe]

/-- Redefine `f i` to be `0`. -/
def erase (i : ι) : (Π₀ i, β i) → Π₀ i, β i :=
  Quotientₓ.map
    (fun x =>
      ⟨fun j => if j = i then 0 else x.1 j, x.2, fun j =>
        (x.3 j).imp_right fun H => by
          simp only [← H, ← if_t_t]⟩)
    fun x y H j =>
    if h : j = i then by
      simp only [← if_pos h]
    else by
      simp only [← if_neg h, ← H j]

@[simp]
theorem erase_apply {i j : ι} {f : Π₀ i, β i} : (f.erase i) j = if j = i then 0 else f j :=
  (Quotientₓ.induction_on f) fun x => rfl

@[simp]
theorem erase_same {i : ι} {f : Π₀ i, β i} : (f.erase i) i = 0 := by
  simp

theorem erase_ne {i i' : ι} {f : Π₀ i, β i} (h : i' ≠ i) : (f.erase i) i' = f i' := by
  simp [← h]

theorem erase_eq_sub_single {β : ι → Type _} [∀ i, AddGroupₓ (β i)] (f : Π₀ i, β i) (i : ι) :
    f.erase i = f - single i (f i) := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
    
  · simp [← erase_ne h.symm, ← single_eq_of_ne h]
    

@[simp]
theorem erase_zero (i : ι) : erase i (0 : Π₀ i, β i) = 0 :=
  ext fun _ => if_t_t _ _

@[simp]
theorem filter_ne_eq_erase (f : Π₀ i, β i) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  ext1 j
  simp only [← Dfinsupp.filter_apply, ← Dfinsupp.erase_apply, ← ite_not]

@[simp]
theorem filter_ne_eq_erase' (f : Π₀ i, β i) (i : ι) : f.filter ((· ≠ ·) i) = f.erase i := by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm

theorem erase_single (j : ι) (i : ι) (x : β i) : (single i x).erase j = if i = j then 0 else single i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single i x).erase i = 0 := by
  rw [erase_single, if_pos rfl]

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) : (single i x).erase j = single i x := by
  rw [erase_single, if_neg h]

section Update

variable (f : Π₀ i, β i) (i) (b : β i) [Decidable (b = 0)]

/-- Replace the value of a `Π₀ i, β i` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `function.update`. -/
def update : Π₀ i, β i :=
  Quotientₓ.map
    (fun x : Pre _ _ =>
      ⟨Function.update x.toFun i b, if b = 0 then x.preSupport.erase i else i ::ₘ x.preSupport, by
        intro j
        rcases eq_or_ne i j with (rfl | hi)
        · split_ifs with hb
          · simp [← hb]
            
          · simp
            
          
        · cases' x.zero j with hj hj
          · split_ifs <;> simp [← Multiset.mem_erase_of_ne hi.symm, ← hj]
            
          · simp [← Function.update_noteq hi.symm, ← hj]
            
          ⟩)
    (fun x y h j =>
      show Function.update x.toFun i b j = Function.update y.toFun i b j by
        rw [(funext h : x.to_fun = y.to_fun)])
    f

variable (j : ι)

@[simp]
theorem coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b :=
  Quotientₓ.induction_on f fun _ => rfl

@[simp]
theorem update_self [Decidable (f i = 0)] : f.update i (f i) = f := by
  ext
  simp

@[simp]
theorem update_eq_erase [Decidable ((0 : β i) = 0)] : f.update i 0 = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
    
  · simp [← hi.symm]
    

theorem update_eq_single_add_erase {β : ι → Type _} [∀ i, AddZeroClassₓ (β i)] (f : Π₀ i, β i) (i : ι) (b : β i)
    [Decidable (b = 0)] : f.update i b = single i b + f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
    
  · simp [← Function.update_noteq h.symm, ← h, ← erase_ne, ← h.symm]
    

theorem update_eq_erase_add_single {β : ι → Type _} [∀ i, AddZeroClassₓ (β i)] (f : Π₀ i, β i) (i : ι) (b : β i)
    [Decidable (b = 0)] : f.update i b = f.erase i + single i b := by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
    
  · simp [← Function.update_noteq h.symm, ← h, ← erase_ne, ← h.symm]
    

theorem update_eq_sub_add_single {β : ι → Type _} [∀ i, AddGroupₓ (β i)] (f : Π₀ i, β i) (i : ι) (b : β i)
    [Decidable (b = 0)] : f.update i b = f - single i (f i) + single i b := by
  rw [update_eq_erase_add_single f i b, erase_eq_sub_single f i]

end Update

end Basic

section AddMonoidₓ

variable [∀ i, AddZeroClassₓ (β i)]

@[simp]
theorem single_add (i : ι) (b₁ b₂ : β i) : single i (b₁ + b₂) = single i b₁ + single i b₂ :=
  ext fun i' => by
    by_cases' h : i = i'
    · subst h
      simp only [← add_apply, ← single_eq_same]
      
    · simp only [← add_apply, ← single_eq_of_ne h, ← zero_addₓ]
      

@[simp]
theorem erase_add (i : ι) (f₁ f₂ : Π₀ i, β i) : erase i (f₁ + f₂) = erase i f₁ + erase i f₂ :=
  ext fun _ => by
    simp [← ite_zero_add]

variable (β)

/-- `dfinsupp.single` as an `add_monoid_hom`. -/
@[simps]
def singleAddHom (i : ι) : β i →+ Π₀ i, β i where
  toFun := single i
  map_zero' := single_zero i
  map_add' := single_add i

/-- `dfinsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def eraseAddHom (i : ι) : (Π₀ i, β i) →+ Π₀ i, β i where
  toFun := erase i
  map_zero' := erase_zero i
  map_add' := erase_add i

variable {β}

@[simp]
theorem single_neg {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (x : β i) : single i (-x) = -single i x :=
  (singleAddHom β i).map_neg x

@[simp]
theorem single_sub {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (x y : β i) :
    single i (x - y) = single i x - single i y :=
  (singleAddHom β i).map_sub x y

@[simp]
theorem erase_neg {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (f : Π₀ i, β i) : (-f).erase i = -f.erase i :=
  (eraseAddHom β i).map_neg f

@[simp]
theorem erase_sub {β : ι → Type v} [∀ i, AddGroupₓ (β i)] (i : ι) (f g : Π₀ i, β i) :
    (f - g).erase i = f.erase i - g.erase i :=
  (eraseAddHom β i).map_sub f g

theorem single_add_erase (i : ι) (f : Π₀ i, β i) : single i (f i) + f.erase i = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h <;> simp only [← add_apply, ← single_apply, ← erase_apply, ← dif_pos rfl, ← if_pos, ← add_zeroₓ]
    else by
      simp only [← add_apply, ← single_apply, ← erase_apply, ← dif_neg h, ← if_neg (Ne.symm h), ← zero_addₓ]

theorem erase_add_single (i : ι) (f : Π₀ i, β i) : f.erase i + single i (f i) = f :=
  ext fun i' =>
    if h : i = i' then by
      subst h <;> simp only [← add_apply, ← single_apply, ← erase_apply, ← dif_pos rfl, ← if_pos, ← zero_addₓ]
    else by
      simp only [← add_apply, ← single_apply, ← erase_apply, ← dif_neg h, ← if_neg (Ne.symm h), ← add_zeroₓ]

protected theorem induction {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (single i b + f)) : p f := by
  refine' Quotientₓ.induction_on f fun x => _
  cases' x with f s H
  revert f H
  apply Multiset.induction_on s
  · intro f H
    convert h0
    ext i
    exact (H i).resolve_left id
    
  intro i s ih f H
  have H2 : p (erase i ⟦{ toFun := f, preSupport := i ::ₘ s, zero := H }⟧) := by
    dsimp' only [← erase, ← Quotientₓ.map_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) 0 (f j) = 0 := by
      intro j
      cases' H j with H2 H2
      · cases' Multiset.mem_cons.1 H2 with H3 H3
        · right
          exact if_pos H3
          
        · left
          exact H3
          
        
      right
      split_ifs <;> [rfl, exact H2]
    have H3 :
      (⟦{ toFun := fun j : ι => ite (j = i) 0 (f j), preSupport := i ::ₘ s, zero := _ }⟧ : Π₀ i, β i) =
        ⟦{ toFun := fun j : ι => ite (j = i) 0 (f j), preSupport := s, zero := H2 }⟧ :=
      Quotientₓ.sound fun i => rfl
    rw [H3]
    apply ih
  have H3 : single i _ + _ = (⟦{ toFun := f, preSupport := i ::ₘ s, zero := H }⟧ : Π₀ i, β i) := single_add_erase _ _
  rw [← H3]
  change p (single i (f i) + _)
  cases' Classical.em (f i = 0) with h h
  · rw [h, single_zero, zero_addₓ]
    exact H2
    
  refine' ha _ _ _ _ h H2
  rw [erase_same]

theorem induction₂ {p : (Π₀ i, β i) → Prop} (f : Π₀ i, β i) (h0 : p 0)
    (ha : ∀ (i b) (f : Π₀ i, β i), f i = 0 → b ≠ 0 → p f → p (f + single i b)) : p f :=
  (Dfinsupp.induction f h0) fun i b f h1 h2 h3 =>
    have h4 : f + single i b = single i b + f := by
      ext j
      by_cases' H : i = j
      · subst H
        simp [← h1]
        
      · simp [← H]
        
    Eq.recOnₓ h4 <| ha i b f h1 h2 h3

@[simp]
theorem add_closure_Union_range_single : AddSubmonoid.closure (⋃ i : ι, Set.Range (single i : β i → Π₀ i, β i)) = ⊤ :=
  top_unique fun x hx => by
    apply Dfinsupp.induction x
    exact AddSubmonoid.zero_mem _
    exact fun a b f ha hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| Set.mem_Union.2 ⟨a, Set.mem_range_self _⟩) hf

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext {γ : Type w} [AddZeroClassₓ γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (single i y) = g (single i y)) : f = g := by
  refine' AddMonoidHom.eq_of_eq_on_mdense add_closure_Union_range_single fun f hf => _
  simp only [← Set.mem_Union, ← Set.mem_range] at hf
  rcases hf with ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `Π₀ i, β i` are equal on each `single a b`, then
they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem add_hom_ext' {γ : Type w} [AddZeroClassₓ γ] ⦃f g : (Π₀ i, β i) →+ γ⦄
    (H : ∀ x, f.comp (singleAddHom β x) = g.comp (singleAddHom β x)) : f = g :=
  add_hom_ext fun x => AddMonoidHom.congr_fun (H x)

end AddMonoidₓ

@[simp]
theorem mk_add [∀ i, AddZeroClassₓ (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i} :
    mk s (x + y) = mk s x + mk s y :=
  ext fun i => by
    simp only [← add_apply, ← mk_apply] <;> split_ifs <;> [rfl, rw [zero_addₓ]]

@[simp]
theorem mk_zero [∀ i, Zero (β i)] {s : Finset ι} : mk s (0 : ∀ i : (↑s : Set ι), β i.1) = 0 :=
  ext fun i => by
    simp only [← mk_apply] <;> split_ifs <;> rfl

@[simp]
theorem mk_neg [∀ i, AddGroupₓ (β i)] {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : mk s (-x) = -mk s x :=
  ext fun i => by
    simp only [← neg_apply, ← mk_apply] <;> split_ifs <;> [rfl, rw [neg_zero]]

@[simp]
theorem mk_sub [∀ i, AddGroupₓ (β i)] {s : Finset ι} {x y : ∀ i : (↑s : Set ι), β i.1} :
    mk s (x - y) = mk s x - mk s y :=
  ext fun i => by
    simp only [← sub_apply, ← mk_apply] <;> split_ifs <;> [rfl, rw [sub_zero]]

/-- If `s` is a subset of `ι` then `mk_add_group_hom s` is the canonical additive
group homomorphism from $\prod_{i\in s}\beta_i$ to $\prod_{\mathtt{i : \iota}}\beta_i.$-/
def mkAddGroupHom [∀ i, AddGroupₓ (β i)] (s : Finset ι) : (∀ i : (s : Set ι), β ↑i) →+ Π₀ i : ι, β i where
  toFun := mk s
  map_zero' := mk_zero
  map_add' := fun _ _ => mk_add

section

variable [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)]

@[simp]
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : (↑s : Set ι), β (i : ι)) : mk s (c • x) = c • mk s x :=
  ext fun i => by
    simp only [← smul_apply, ← mk_apply] <;> split_ifs <;> [rfl, rw [smul_zero]]

@[simp]
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [← smul_apply, ← single_apply] <;> split_ifs <;> [cases h, rw [smul_zero]] <;> rfl

end

section SupportBasic

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

/-- Set `{i | f x ≠ 0}` as a `finset`. -/
def support (f : Π₀ i, β i) : Finset ι :=
  (Quotientₓ.liftOn f fun x => x.2.toFinset.filter fun i => x.1 i ≠ 0) <| by
    intro x y Hxy
    ext i
    constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
      rw [Hxy i] at h2
      exact Finset.mem_filter.2 ⟨Multiset.mem_to_finset.2 <| (y.3 i).resolve_right h2, h2⟩
      
    · intro H
      rcases Finset.mem_filter.1 H with ⟨h1, h2⟩
      rw [← Hxy i] at h2
      exact Finset.mem_filter.2 ⟨Multiset.mem_to_finset.2 <| (x.3 i).resolve_right h2, h2⟩
      

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk s x).support ⊆ s := fun i H =>
  Multiset.mem_to_finset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem mem_support_to_fun (f : Π₀ i, β i) (i) : i ∈ f.support ↔ f i ≠ 0 := by
  refine' Quotientₓ.induction_on f fun x => _
  dsimp' only [← support, ← Quotientₓ.lift_on_mk]
  rw [Finset.mem_filter, Multiset.mem_to_finset]
  exact and_iff_right_of_imp (x.3 i).resolve_right

theorem eq_mk_support (f : Π₀ i, β i) : f = mk f.support fun i => f i := by
  change f = mk f.support fun i => f i.1
  ext i
  by_cases' h : f i ≠ 0 <;> [skip, rw [not_not] at h] <;> simp [← h]

@[simp]
theorem support_zero : (0 : Π₀ i, β i).support = ∅ :=
  rfl

theorem mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∈ f.support ↔ f i ≠ 0 :=
  f.mem_support_to_fun _

theorem not_mem_support_iff {f : Π₀ i, β i} {i : ι} : i ∉ f.support ↔ f i = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp]
theorem support_eq_empty {f : Π₀ i, β i} : f.support = ∅ ↔ f = 0 :=
  ⟨fun H =>
    ext <| by
      simpa [← Finset.ext_iff] using H,
    by
    simp (config := { contextual := true })⟩

instance decidableZero : DecidablePred (Eq (0 : Π₀ i, β i)) := fun f =>
  decidableOfIff _ <| support_eq_empty.trans eq_comm

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ∉ » s)
theorem support_subset_iff {s : Set ι} {f : Π₀ i, β i} : ↑f.support ⊆ s ↔ ∀ (i) (_ : i ∉ s), f i = 0 := by
  simp [← Set.subset_def] <;> exact forall_congrₓ fun i => not_imp_comm

theorem support_single_ne_zero {i : ι} {b : β i} (hb : b ≠ 0) : (single i b).support = {i} := by
  ext j
  by_cases' h : i = j
  · subst h
    simp [← hb]
    
  simp [← Ne.symm h, ← h]

theorem support_single_subset {i : ι} {b : β i} : (single i b).support ⊆ {i} :=
  support_mk_subset

section MapRangeAndZipWith

variable [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]

theorem map_range_def [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0}
    {g : Π₀ i, β₁ i} : mapRange f hf g = mk g.support fun i => f i.1 (g i.1) := by
  ext i
  by_cases' h : g i ≠ 0 <;> simp at h <;> simp [← h, ← hf]

@[simp]
theorem map_range_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {i : ι} {b : β₁ i} :
    mapRange f hf (single i b) = single i (f i b) :=
  Dfinsupp.ext fun i' => by
    by_cases' i = i' <;>
      [· subst i'
        simp
        ,
      simp [← h, ← hf]]

variable [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]

theorem support_map_range {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} :
    (mapRange f hf g).support ⊆ g.support := by
  simp [← map_range_def]

theorem zip_with_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [dec : DecidableEq ι]
    [∀ i : ι, Zero (β i)] [∀ i : ι, Zero (β₁ i)] [∀ i : ι, Zero (β₂ i)] [∀ (i : ι) (x : β₁ i), Decidable (x ≠ 0)]
    [∀ (i : ι) (x : β₂ i), Decidable (x ≠ 0)] {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i}
    {g₂ : Π₀ i, β₂ i} : zipWith f hf g₁ g₂ = mk (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  ext i
  by_cases' h1 : g₁ i ≠ 0 <;>
    by_cases' h2 : g₂ i ≠ 0 <;> simp only [← not_not, ← Ne.def] at h1 h2 <;> simp [← h1, ← h2, ← hf]

theorem support_zip_with {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i 0 0 = 0} {g₁ : Π₀ i, β₁ i} {g₂ : Π₀ i, β₂ i} :
    (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [← zip_with_def]

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀ i, β i) : f.erase i = mk (f.support.erase i) fun j => f j.1 := by
  ext j
  by_cases' h1 : j = i <;> by_cases' h2 : f j ≠ 0 <;> simp at h2 <;> simp [← h1, ← h2]

@[simp]
theorem support_erase (i : ι) (f : Π₀ i, β i) : (f.erase i).support = f.support.erase i := by
  ext j
  by_cases' h1 : j = i
  simp [← h1]
  by_cases' h2 : f j ≠ 0 <;> simp at h2 <;> simp [← h1, ← h2]

theorem support_update_ne_zero (f : Π₀ i, β i) (i : ι) {b : β i} [Decidable (b = 0)] (h : b ≠ 0) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [← h]
    
  · simp [← hi.symm]
    

theorem support_update (f : Π₀ i, β i) (i : ι) (b : β i) [Decidable (b = 0)] :
    support (f.update i b) = if b = 0 then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [← update_eq_erase, ← support_erase]
    
  · rw [support_update_ne_zero f _ hb]
    

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀ i, β i) : f.filter p = mk (f.support.filter p) fun i => f i.1 := by
  ext i <;> by_cases' h1 : p i <;> by_cases' h2 : f i ≠ 0 <;> simp at h2 <;> simp [← h1, ← h2]

@[simp]
theorem support_filter (f : Π₀ i, β i) : (f.filter p).support = f.support.filter p := by
  ext i <;> by_cases' h : p i <;> simp [← h]

theorem subtype_domain_def (f : Π₀ i, β i) : f.subtypeDomain p = mk (f.support.Subtype p) fun i => f i := by
  ext i <;>
    by_cases' h2 : f i ≠ 0 <;>
      try
          simp at h2 <;>
        dsimp' <;> simp [← h2]

@[simp]
theorem support_subtype_domain {f : Π₀ i, β i} : (subtypeDomain p f).support = f.support.Subtype p := by
  ext i
  simp

end FilterAndSubtypeDomain

end SupportBasic

theorem support_add [∀ i, AddZeroClassₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {g₁ g₂ : Π₀ i, β i} :
    (g₁ + g₂).support ⊆ g₁.support ∪ g₂.support :=
  support_zip_with

@[simp]
theorem support_neg [∀ i, AddGroupₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    support (-f) = support f := by
  ext i <;> simp

theorem support_smul {γ : Type w} [Semiringₓ γ] [∀ i, AddCommMonoidₓ (β i)] [∀ i, Module γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) : (b • v).support ⊆ v.support :=
  support_map_range

instance [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] : DecidableEq (Π₀ i, β i) := fun f g =>
  decidableOfIff (f.support = g.support ∧ ∀, ∀ i ∈ f.support, ∀, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ =>
      ext fun i =>
        if h : i ∈ f.support then h₂ i h
        else by
          have hf : f i = 0 := by
            rwa [mem_support_iff, not_not] at h
          have hg : g i = 0 := by
            rwa [h₁, mem_support_iff, not_not] at h
          rw [hf, hg],
      by
      rintro rfl
      simp ⟩

section Equivₓ

open Finset

variable {κ : Type _}

/-- Reindexing (and possibly removing) terms of a dfinsupp.-/
noncomputable def comapDomain [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) : (Π₀ i, β i) → Π₀ k, β (h k) :=
  by
  refine' Quotientₓ.lift (fun f => ⟦_⟧) fun f f' h => _
  exact
    { toFun := fun x => f.to_fun (h x), preSupport := (f.pre_support.to_finset.preimage h (hh.inj_on _)).val,
      zero := fun x => (f.zero (h x)).imp_left fun hx => mem_preimage.mpr <| multiset.mem_to_finset.mpr hx }
  exact Quot.sound fun x => h _

@[simp]
theorem comap_domain_apply [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (f : Π₀ i, β i) (k : κ) :
    comapDomain h hh f k = f (h k) := by
  rcases f with ⟨⟩
  rfl

@[simp]
theorem comap_domain_zero [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comap_domain_apply, zero_apply]

@[simp]
theorem comap_domain_add [∀ i, AddZeroClassₓ (β i)] (h : κ → ι) (hh : Function.Injective h) (f g : Π₀ i, β i) :
    comapDomain h hh (f + g) = comapDomain h hh f + comapDomain h hh g := by
  ext
  rw [add_apply, comap_domain_apply, comap_domain_apply, comap_domain_apply, add_apply]

@[simp]
theorem comap_domain_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (h : κ → ι)
    (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) : comapDomain h hh (r • f) = r • comapDomain h hh f := by
  ext
  rw [smul_apply, comap_domain_apply, smul_apply, comap_domain_apply]

@[simp]
theorem comap_domain_single [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι) (hh : Function.Injective h) (k : κ)
    (x : β (h k)) : comapDomain h hh (single (h k) x) = single k x := by
  ext
  rw [comap_domain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
    
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]
    

omit dec

/-- A computable version of comap_domain when an explicit left inverse is provided.-/
def comapDomain' [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) :
    (Π₀ i, β i) → Π₀ k, β (h k) := by
  refine' Quotientₓ.lift (fun f => ⟦_⟧) fun f f' h => _
  exact
    { toFun := fun x => f.to_fun (h x), preSupport := f.pre_support.map h',
      zero := fun x => (f.zero (h x)).imp_left fun hx => multiset.mem_map.mpr ⟨_, hx, hh' _⟩ }
  exact Quot.sound fun x => h _

@[simp]
theorem comap_domain'_apply [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) (f : Π₀ i, β i)
    (k : κ) : comapDomain' h hh' f k = f (h k) := by
  rcases f with ⟨⟩
  rfl

@[simp]
theorem comap_domain'_zero [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) :
    comapDomain' h hh' (0 : Π₀ i, β i) = 0 := by
  ext
  rw [zero_apply, comap_domain'_apply, zero_apply]

@[simp]
theorem comap_domain'_add [∀ i, AddZeroClassₓ (β i)] (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f g : Π₀ i, β i) : comapDomain' h hh' (f + g) = comapDomain' h hh' f + comapDomain' h hh' g := by
  ext
  rw [add_apply, comap_domain'_apply, comap_domain'_apply, comap_domain'_apply, add_apply]

@[simp]
theorem comap_domain'_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (β i)] [∀ i, DistribMulAction γ (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) : comapDomain' h hh' (r • f) = r • comapDomain' h hh' f :=
  by
  ext
  rw [smul_apply, comap_domain'_apply, smul_apply, comap_domain'_apply]

@[simp]
theorem comap_domain'_single [DecidableEq ι] [DecidableEq κ] [∀ i, Zero (β i)] (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (k : κ) (x : β (h k)) : comapDomain' h hh' (single (h k) x) = single k x := by
  ext
  rw [comap_domain'_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
    
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh'.injective.ne hik.symm)]
    

/-- Reindexing terms of a dfinsupp.

This is the dfinsupp version of `equiv.Pi_congr_left'`. -/
@[simps apply]
def equivCongrLeft [∀ i, Zero (β i)] (h : ι ≃ κ) : (Π₀ i, β i) ≃ Π₀ k, β (h.symm k) where
  toFun := comapDomain' h.symm h.right_inv
  invFun := fun f =>
    mapRange (fun i => Equivₓ.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i =>
        (Equivₓ.cast_eq_iff_heq _).mpr <| by
          convert HEq.rfl
          repeat'
            exact (h.symm_apply_apply i).symm)
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv := fun f => by
    ext i
    rw [map_range_apply, comap_domain'_apply, comap_domain'_apply, Equivₓ.cast_eq_iff_heq, h.symm_apply_apply]
  right_inv := fun f => by
    ext k
    rw [comap_domain'_apply, map_range_apply, comap_domain'_apply, Equivₓ.cast_eq_iff_heq, h.apply_symm_apply]

section Curry

variable {α : ι → Type _} {δ : ∀ i, α i → Type v}

-- lean can't find these instances
instance hasAdd₂ [∀ i j, AddZeroClassₓ (δ i j)] : Add (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.hasAdd ι (fun i => Π₀ j, δ i j) _

instance addZeroClass₂ [∀ i j, AddZeroClassₓ (δ i j)] : AddZeroClassₓ (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.addZeroClass ι (fun i => Π₀ j, δ i j) _

instance addMonoid₂ [∀ i j, AddMonoidₓ (δ i j)] : AddMonoidₓ (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.addMonoid ι (fun i => Π₀ j, δ i j) _

instance distribMulAction₂ [Monoidₓ γ] [∀ i j, AddMonoidₓ (δ i j)] [∀ i j, DistribMulAction γ (δ i j)] :
    DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @Dfinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- The natural map between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.  -/
noncomputable def sigmaCurry [∀ i j, Zero (δ i j)] (f : Π₀ i : Σi, _, δ i.1 i.2) : Π₀ (i) (j), δ i j := by
  classical
  exact
    mk (f.support.image fun i => i.1) fun i =>
      (mk (f.support.preimage (Sigma.mk i) <| sigma_mk_injective.inj_on _)) fun j => f ⟨i, j⟩

@[simp]
theorem sigma_curry_apply [∀ i j, Zero (δ i j)] (f : Π₀ i : Σi, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ := by
  dunfold sigma_curry
  by_cases' h : f ⟨i, j⟩ = 0
  · rw [h, mk_apply]
    split_ifs
    · rw [mk_apply]
      split_ifs
      · exact h
        
      · rfl
        
      
    · rfl
      
    
  · rw [mk_of_mem, mk_of_mem]
    · rfl
      
    · rw [mem_preimage, mem_support_to_fun]
      exact h
      
    · rw [mem_image]
      refine' ⟨⟨i, j⟩, _, rfl⟩
      rw [mem_support_to_fun]
      exact h
      
    

@[simp]
theorem sigma_curry_zero [∀ i j, Zero (δ i j)] : sigmaCurry (0 : Π₀ i : Σi, _, δ i.1 i.2) = 0 := by
  ext i j
  rw [sigma_curry_apply]
  rfl

@[simp]
theorem sigma_curry_add [∀ i j, AddZeroClassₓ (δ i j)] (f g : Π₀ i : Σi, α i, δ i.1 i.2) :
    @sigmaCurry _ _ δ _ (f + g) = @sigmaCurry _ _ δ _ f + @sigmaCurry ι α δ _ g := by
  ext i j
  rw [@add_apply _ (fun i => Π₀ j, δ i j) _ (sigma_curry _), add_apply, sigma_curry_apply, sigma_curry_apply,
    sigma_curry_apply, add_apply]

@[simp]
theorem sigma_curry_smul [Monoidₓ γ] [∀ i j, AddMonoidₓ (δ i j)] [∀ i j, DistribMulAction γ (δ i j)] (r : γ)
    (f : Π₀ i : Σi, α i, δ i.1 i.2) : @sigmaCurry _ _ δ _ (r • f) = r • @sigmaCurry _ _ δ _ f := by
  ext i j
  rw [@smul_apply _ _ (fun i => Π₀ j, δ i j) _ _ _ _ (sigma_curry _), smul_apply, sigma_curry_apply, sigma_curry_apply,
    smul_apply]

@[simp]
theorem sigma_curry_single [∀ i j, Zero (δ i j)] (ij : Σi, α i) (x : δ ij.1 ij.2) :
    sigmaCurry (single ij x) = single ij.1 (single ij.2 x : Π₀ j, δ ij.1 j) := by
  obtain ⟨i, j⟩ := ij
  ext i' j'
  dsimp' only
  rw [sigma_curry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
      
    · rw [single_eq_of_ne, single_eq_of_ne hj]
      simpa using hj
      
    
  · rw [single_eq_of_ne, single_eq_of_ne hi, zero_apply]
    simpa using hi
    

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- The natural map between `Π₀ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`.-/
noncomputable def sigmaUncurry [∀ i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) : Π₀ i : Σi, _, δ i.1 i.2 := by
  classical
  exact mk (f.support.bUnion fun i => (f i).support.Image <| Sigma.mk i) fun ⟨⟨i, j⟩, _⟩ => f i j

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem sigma_uncurry_apply [∀ i j, Zero (δ i j)] (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j := by
  dunfold sigma_uncurry
  by_cases' h : f i j = 0
  · rw [mk_apply]
    split_ifs
    · rfl
      
    · exact h.symm
      
    
  · apply mk_of_mem
    rw [mem_bUnion]
    refine' ⟨i, _, _⟩
    · rw [mem_support_to_fun]
      intro H
      rw [ext_iff] at H
      exact h (H j)
      
    · apply mem_image_of_mem
      rw [mem_support_to_fun]
      exact h
      
    

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem sigma_uncurry_zero [∀ i j, Zero (δ i j)] : sigmaUncurry (0 : Π₀ (i) (j), δ i j) = 0 := by
  ext ⟨i, j⟩
  rw [sigma_uncurry_apply]
  rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem sigma_uncurry_add [∀ i j, AddZeroClassₓ (δ i j)] (f g : Π₀ (i) (j), δ i j) :
    sigmaUncurry (f + g) = sigmaUncurry f + sigmaUncurry g := by
  ext ⟨i, j⟩
  rw [add_apply, sigma_uncurry_apply, sigma_uncurry_apply, sigma_uncurry_apply, @add_apply _ (fun i => Π₀ j, δ i j) _,
    add_apply]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem sigma_uncurry_smul [Monoidₓ γ] [∀ i j, AddMonoidₓ (δ i j)] [∀ i j, DistribMulAction γ (δ i j)] (r : γ)
    (f : Π₀ (i) (j), δ i j) : sigmaUncurry (r • f) = r • sigmaUncurry f := by
  ext ⟨i, j⟩
  rw [smul_apply, sigma_uncurry_apply, sigma_uncurry_apply, @smul_apply _ _ (fun i => Π₀ j, δ i j) _ _ _, smul_apply]

@[simp]
theorem sigma_uncurry_single [∀ i j, Zero (δ i j)] (i) (j : α i) (x : δ i j) :
    sigmaUncurry (single i (single j x : Π₀ j : α i, δ i j)) = single ⟨i, j⟩ x := by
  ext ⟨i', j'⟩
  dsimp' only
  rw [sigma_uncurry_apply]
  obtain rfl | hi := eq_or_ne i i'
  · rw [single_eq_same]
    obtain rfl | hj := eq_or_ne j j'
    · rw [single_eq_same, single_eq_same]
      
    · rw [single_eq_of_ne hj, single_eq_of_ne]
      simpa using hj
      
    
  · rw [single_eq_of_ne hi, single_eq_of_ne, zero_apply]
    simpa using hi
    

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- The natural bijection between `Π₀ (i : Σ i, α i), δ i.1 i.2` and `Π₀ i (j : α i), δ i j`.

This is the dfinsupp version of `equiv.Pi_curry`. -/
noncomputable def sigmaCurryEquiv [∀ i j, Zero (δ i j)] : (Π₀ i : Σi, _, δ i.1 i.2) ≃ Π₀ (i) (j), δ i j where
  toFun := sigmaCurry
  invFun := sigmaUncurry
  left_inv := fun f => by
    ext ⟨i, j⟩
    rw [sigma_uncurry_apply, sigma_curry_apply]
  right_inv := fun f => by
    ext i j
    rw [sigma_curry_apply, sigma_uncurry_apply]

end Curry

variable {α : Option ι → Type v}

/-- Adds a term to a dfinsupp, making a dfinsupp indexed by an `option`.

This is the dfinsupp version of `option.rec`. -/
def extendWith [∀ i, Zero (α i)] (a : α none) : (Π₀ i, α (some i)) → Π₀ i, α i := by
  refine' Quotientₓ.lift (fun f => ⟦_⟧) fun f f' h => _
  exact
    { toFun := Option.rec a f.to_fun, preSupport := none ::ₘ f.pre_support.map some,
      zero := fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i => (f.zero i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h) i }
  · refine' Quot.sound ((Option.rec _) fun x => _)
    rfl
    exact h x
    

@[simp]
theorem extend_with_none [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) : f.extendWith a none = a := by
  rcases f with ⟨⟩
  rfl

@[simp]
theorem extend_with_some [∀ i, Zero (α i)] (f : Π₀ i, α (some i)) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i := by
  rcases f with ⟨⟩
  rfl

@[simp]
theorem extend_with_single_zero [DecidableEq ι] [∀ i, Zero (α i)] (i : ι) (x : α (some i)) :
    (single i x).extendWith 0 = single (some i) x := by
  ext (_ | j)
  · rw [extend_with_none, single_eq_of_ne (Option.some_ne_none _)]
    
  · rw [extend_with_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
      
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).Ne hij)]
      
    

@[simp]
theorem extend_with_zero [DecidableEq ι] [∀ i, Zero (α i)] (x : α none) :
    (0 : Π₀ i, α (some i)).extendWith x = single none x := by
  ext (_ | j)
  · rw [extend_with_none, single_eq_same]
    
  · rw [extend_with_some, single_eq_of_ne (Option.some_ne_none _).symm, zero_apply]
    

include dec

/-- Bijection obtained by separating the term of index `none` of a dfinsupp over `option ι`.

This is the dfinsupp version of `equiv.pi_option_equiv_prod`. -/
@[simps]
noncomputable def equivProdDfinsupp [∀ i, Zero (α i)] : (Π₀ i, α i) ≃ α none × Π₀ i, α (some i) where
  toFun := fun f => (f none, comapDomain some (Option.some_injective _) f)
  invFun := fun f => f.2.extendWith f.1
  left_inv := fun f => by
    ext i
    cases' i with i
    · rw [extend_with_none]
      
    · rw [extend_with_some, comap_domain_apply]
      
  right_inv := fun _ => by
    ext
    · exact extend_with_none _ _
      
    · rw [comap_domain_apply, extend_with_some]
      

theorem equiv_prod_dfinsupp_add [∀ i, AddZeroClassₓ (α i)] (f g : Π₀ i, α i) :
    equivProdDfinsupp (f + g) = equivProdDfinsupp f + equivProdDfinsupp g :=
  Prod.extₓ (add_apply _ _ _) (comap_domain_add _ _ _ _)

theorem equiv_prod_dfinsupp_smul [Monoidₓ γ] [∀ i, AddMonoidₓ (α i)] [∀ i, DistribMulAction γ (α i)] (r : γ)
    (f : Π₀ i, α i) : equivProdDfinsupp (r • f) = r • equivProdDfinsupp f :=
  Prod.extₓ (smul_apply _ _ _) (comap_domain_smul _ _ _ _)

end Equivₓ

section ProdAndSum

/-- `prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] (f : Π₀ i, β i) (g : ∀ i, β i → γ) :
    γ :=
  ∏ i in f.support, g i (f i)

@[to_additive]
theorem prod_map_range_index {β₁ : ι → Type v₁} {β₂ : ι → Type v₂} [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i 0 = 0} {g : Π₀ i, β₁ i} {h : ∀ i, β₂ i → γ} (h0 : ∀ i, h i 0 = 1) :
    (mapRange f hf g).Prod h = g.Prod fun i b => h i (f i b) := by
  rw [map_range_def]
  refine' (Finset.prod_subset support_mk_subset _).trans _
  · intro i h1 h2
    dsimp'
    simp [← h1] at h2
    dsimp'  at h2
    simp [← h1, ← h2, ← h0]
    
  · refine' Finset.prod_congr rfl _
    intro i h1
    simp [← h1]
    

@[to_additive]
theorem prod_zero_index [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ]
    {h : ∀ i, β i → γ} : (0 : Π₀ i, β i).Prod h = 1 :=
  rfl

@[to_additive]
theorem prod_single_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {i : ι} {b : β i}
    {h : ∀ i, β i → γ} (h_zero : h i 0 = 1) : (single i b).Prod h = h i b := by
  by_cases' h : b ≠ 0
  · simp [← Dfinsupp.prod, ← support_single_ne_zero h]
    
  · rw [not_not] at h
    simp [← h, ← prod_zero_index, ← h_zero]
    rfl
    

@[to_additive]
theorem prod_neg_index [∀ i, AddGroupₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {g : Π₀ i, β i}
    {h : ∀ i, β i → γ} (h0 : ∀ i, h i 0 = 1) : (-g).Prod h = g.Prod fun i b => h i (-b) :=
  prod_map_range_index h0

omit dec

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} [DecidableEq ι₁] [DecidableEq ι₂]
    [∀ i, Zero (β₁ i)] [∀ i, Zero (β₂ i)] [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ (i) (x : β₂ i), Decidable (x ≠ 0)]
    [CommMonoidₓ γ] (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.Prod fun i₁ x₁ => f₂.Prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.Prod fun i₂ x₂ => f₁.Prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[simp]
theorem sum_apply {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i}
    {i₂ : ι} : (f.Sum g) i₂ = f.Sum fun i₁ b => g i₁ b i₂ :=
  (evalAddMonoidHom i₂ : (Π₀ i, β i) →+ β i₂).map_sum _ f.support

include dec

theorem support_sum {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} :
    (f.Sum g).support ⊆ f.support.bUnion fun i => (g i (f i)).support := by
  have : ∀ i₁ : ι, (f.Sum fun (i : ι₁) (b : β₁ i) => (g i b) i₁) ≠ 0 → ∃ i : ι₁, f i ≠ 0 ∧ ¬(g i (f i)) i₁ = 0 :=
    fun i₁ h =>
    let ⟨i, hi, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨i, mem_support_iff.1 hi, Ne⟩
  simpa [← Finset.subset_iff, ← mem_support_iff, ← Finset.mem_bUnion, ← sum_apply] using this

@[simp, to_additive]
theorem prod_one [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : Π₀ i, β i} :
    (f.Prod fun i b => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[simp, to_additive]
theorem prod_mul [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : Π₀ i, β i}
    {h₁ h₂ : ∀ i, β i → γ} : (f.Prod fun i b => h₁ i b * h₂ i b) = f.Prod h₁ * f.Prod h₂ :=
  Finset.prod_mul_distrib

@[simp, to_additive]
theorem prod_inv [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommGroupₓ γ] {f : Π₀ i, β i}
    {h : ∀ i, β i → γ} : (f.Prod fun i b => (h i b)⁻¹) = (f.Prod h)⁻¹ :=
  ((invMonoidHom : γ →* γ).map_prod _ f.support).symm

@[to_additive]
theorem prod_eq_one [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {f : Π₀ i, β i}
    {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.Prod h = 1 :=
  Finset.prod_eq_one fun i hi => hyp i

theorem smul_sum {α : Type _} [Monoidₓ α] [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommMonoidₓ γ]
    [DistribMulAction α γ] {f : Π₀ i, β i} {h : ∀ i, β i → γ} {c : α} : c • f.Sum h = f.Sum fun a b => c • h a b :=
  Finset.smul_sum

@[to_additive]
theorem prod_add_index [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ]
    {f g : Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f + g).Prod h = f.Prod h * g.Prod h :=
  have f_eq : (∏ i in f.support ∪ g.support, h i (f i)) = f.Prod h :=
    (Finset.prod_subset (Finset.subset_union_left _ _) <| by
        simp (config := { contextual := true })[← mem_support_iff, ← h_zero]).symm
  have g_eq : (∏ i in f.support ∪ g.support, h i (g i)) = g.Prod h :=
    (Finset.prod_subset (Finset.subset_union_right _ _) <| by
        simp (config := { contextual := true })[← mem_support_iff, ← h_zero]).symm
  calc
    (∏ i in (f + g).support, h i ((f + g) i)) = ∏ i in f.support ∪ g.support, h i ((f + g) i) :=
      Finset.prod_subset support_add <| by
        simp (config := { contextual := true })[← mem_support_iff, ← h_zero]
    _ = (∏ i in f.support ∪ g.support, h i (f i)) * ∏ i in f.support ∪ g.support, h i (g i) := by
      simp [← h_add, ← Finset.prod_mul_distrib]
    _ = _ := by
      rw [f_eq, g_eq]
    

@[to_additive]
theorem _root_.dfinsupp_prod_mem [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {S : Type _}
    [SetLike S γ] [SubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i → γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) :
    f.Prod g ∈ s :=
  prod_mem fun i hi => h _ <| mem_support_iff.1 hi

@[simp, to_additive]
theorem prod_eq_prod_fintype [Fintype ι] [∀ i, Zero (β i)] [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ]
    (v : Π₀ i, β i) [f : ∀ i, β i → γ] (hf : ∀ i, f i 0 = 1) : v.Prod f = ∏ i, f i (Dfinsupp.equivFunOnFintype v i) :=
  by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by
    simp [← Dfinsupp.prod, ← this]
  apply Finset.prod_subset v.support.subset_univ
  intro i hi' hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]

/-- When summing over an `add_monoid_hom`, the decidability assumption is not needed, and the result is
also an `add_monoid_hom`.
-/
def sumAddHom [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (φ : ∀ i, β i →+ γ) : (Π₀ i, β i) →+ γ where
  toFun := fun f =>
    (Quotientₓ.liftOn f fun x => ∑ i in x.2.toFinset, φ i (x.1 i)) fun x y H => by
      have H1 : x.2.toFinset ∩ y.2.toFinset ⊆ x.2.toFinset := Finset.inter_subset_left _ _
      have H2 : x.2.toFinset ∩ y.2.toFinset ⊆ y.2.toFinset := Finset.inter_subset_right _ _
      refine' (Finset.sum_subset H1 _).symm.trans ((Finset.sum_congr rfl _).trans (Finset.sum_subset H2 _))
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        rw [H i]
        simp only [← Multiset.mem_to_finset] at H1 H2
        rw [(y.3 i).resolve_left (mt (And.intro H1) H2), AddMonoidHom.map_zero]
        
      · intro i H1
        rw [H i]
        
      · intro i H1 H2
        rw [Finset.mem_inter] at H2
        rw [← H i]
        simp only [← Multiset.mem_to_finset] at H1 H2
        rw [(x.3 i).resolve_left (mt (fun H3 => And.intro H3 H1) H2), AddMonoidHom.map_zero]
        
  map_add' := fun f g => by
    refine' Quotientₓ.induction_on f fun x => _
    refine' Quotientₓ.induction_on g fun y => _
    change (∑ i in _, _) = (∑ i in _, _) + ∑ i in _, _
    simp only
    conv => lhs congr skip ext rw [AddMonoidHom.map_add]
    simp only [← Finset.sum_add_distrib]
    congr 1
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [← Multiset.mem_to_finset, ← Multiset.mem_add]
        exact Or.inl
        
      · intro i H1 H2
        simp only [← Multiset.mem_to_finset, ← Multiset.mem_add] at H2
        rw [(x.3 i).resolve_left H2, AddMonoidHom.map_zero]
        
      
    · refine' (Finset.sum_subset _ _).symm
      · intro i
        simp only [← Multiset.mem_to_finset, ← Multiset.mem_add]
        exact Or.inr
        
      · intro i H1 H2
        simp only [← Multiset.mem_to_finset, ← Multiset.mem_add] at H2
        rw [(y.3 i).resolve_left H2, AddMonoidHom.map_zero]
        
      
  map_zero' := rfl

@[simp]
theorem sum_add_hom_single [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (φ : ∀ i, β i →+ γ) (i) (x : β i) :
    sumAddHom φ (single i x) = φ i x :=
  (add_zeroₓ _).trans <|
    congr_arg (φ i) <| show (if H : i ∈ ({i} : Finset _) then x else 0) = x from dif_pos <| Finset.mem_singleton_self i

@[simp]
theorem sum_add_hom_comp_single [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) :
    (sumAddHom f).comp (singleAddHom β i) = f i :=
  AddMonoidHom.ext fun x => sum_add_hom_single f i x

/-- While we didn't need decidable instances to define it, we do to reduce it to a sum -/
theorem sum_add_hom_apply [∀ i, AddZeroClassₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommMonoidₓ γ]
    (φ : ∀ i, β i →+ γ) (f : Π₀ i, β i) : sumAddHom φ f = f.Sum fun x => φ x := by
  refine' Quotientₓ.induction_on f fun x => _
  change (∑ i in _, _) = ∑ i in Finset.filter _ _, _
  rw [Finset.sum_filter, Finset.sum_congr rfl]
  intro i _
  dsimp' only
  split_ifs
  rfl
  rw [not_not.mp h, AddMonoidHom.map_zero]

theorem _root_.dfinsupp_sum_add_hom_mem [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] {S : Type _} [SetLike S γ]
    [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : ∀ i, β i →+ γ) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) :
    Dfinsupp.sumAddHom g f ∈ s := by
  classical
  rw [Dfinsupp.sum_add_hom_apply]
  convert dfinsupp_sum_mem _ _ _ _
  · infer_instance
    
  exact h

/-- The supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom`; that is, every element in the `supr` can be produced from taking a finite
number of non-zero elements of `S i`, coercing them to `γ`, and summing them. -/
theorem _root_.add_submonoid.supr_eq_mrange_dfinsupp_sum_add_hom [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ) :
    supr S = (Dfinsupp.sumAddHom fun i => (S i).Subtype).mrange := by
  apply le_antisymmₓ
  · apply supr_le _
    intro i y hy
    exact ⟨Dfinsupp.single i ⟨y, hy⟩, Dfinsupp.sum_add_hom_single _ _ _⟩
    
  · rintro x ⟨v, rfl⟩
    exact dfinsupp_sum_add_hom_mem _ v _ fun i _ => (le_supr S i : S i ≤ _) (v i).Prop
    

/-- The bounded supremum of a family of commutative additive submonoids is equal to the range of
`dfinsupp.sum_add_hom` composed with `dfinsupp.filter_add_monoid_hom`; that is, every element in the
bounded `supr` can be produced from taking a finite number of non-zero elements from the `S i` that
satisfy `p i`, coercing them to `γ`, and summing them. -/
theorem _root_.add_submonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom (p : ι → Prop) [DecidablePred p] [AddCommMonoidₓ γ]
    (S : ι → AddSubmonoid γ) :
    (⨆ (i) (h : p i), S i) = ((sumAddHom fun i => (S i).Subtype).comp (filterAddMonoidHom _ p)).mrange := by
  apply le_antisymmₓ
  · refine' supr₂_le fun i hi y hy => ⟨Dfinsupp.single i ⟨y, hy⟩, _⟩
    rw [AddMonoidHom.comp_apply, filter_add_monoid_hom_apply, filter_single_pos _ _ hi]
    exact sum_add_hom_single _ _ _
    
  · rintro x ⟨v, rfl⟩
    refine' dfinsupp_sum_add_hom_mem _ _ _ fun i hi => _
    refine' AddSubmonoid.mem_supr_of_mem i _
    by_cases' hp : p i
    · simp [← hp]
      
    · simp [← hp]
      
    

theorem _root_.add_submonoid.mem_supr_iff_exists_dfinsupp [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ) (x : γ) :
    x ∈ supr S ↔ ∃ f : Π₀ i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.supr_eq_mrange_dfinsupp_sum_add_hom S) x

/-- A variant of `add_submonoid.mem_supr_iff_exists_dfinsupp` with the RHS fully unfolded. -/
theorem _root_.add_submonoid.mem_supr_iff_exists_dfinsupp' [AddCommMonoidₓ γ] (S : ι → AddSubmonoid γ)
    [∀ (i) (x : S i), Decidable (x ≠ 0)] (x : γ) : x ∈ supr S ↔ ∃ f : Π₀ i, S i, (f.Sum fun i xi => ↑xi) = x := by
  rw [AddSubmonoid.mem_supr_iff_exists_dfinsupp]
  simp_rw [sum_add_hom_apply]
  congr

theorem _root_.add_submonoid.mem_bsupr_iff_exists_dfinsupp (p : ι → Prop) [DecidablePred p] [AddCommMonoidₓ γ]
    (S : ι → AddSubmonoid γ) (x : γ) :
    (x ∈ ⨆ (i) (h : p i), S i) ↔ ∃ f : Π₀ i, S i, Dfinsupp.sumAddHom (fun i => (S i).Subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsupp_sum_add_hom p S) x

omit dec

theorem sum_add_hom_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type _} {β₂ : ι₂ → Type _} {γ : Type _} [DecidableEq ι₁]
    [DecidableEq ι₂] [∀ i, AddZeroClassₓ (β₁ i)] [∀ i, AddZeroClassₓ (β₂ i)] [AddCommMonoidₓ γ] (f₁ : Π₀ i, β₁ i)
    (f₂ : Π₀ i, β₂ i) (h : ∀ i j, β₁ i →+ β₂ j →+ γ) :
    sumAddHom (fun i₂ => sumAddHom (fun i₁ => h i₁ i₂) f₁) f₂ =
      sumAddHom (fun i₁ => sumAddHom (fun i₂ => (h i₁ i₂).flip) f₂) f₁ :=
  by
  refine' Quotientₓ.induction_on₂ f₁ f₂ fun x₁ x₂ => _
  simp only [← sum_add_hom, ← AddMonoidHom.finset_sum_apply, ← Quotientₓ.lift_on_mk, ← AddMonoidHom.coe_mk, ←
    AddMonoidHom.flip_apply]
  exact Finset.sum_comm

include dec

/-- The `dfinsupp` version of `finsupp.lift_add_hom`,-/
@[simps apply symmApply]
def liftAddHom [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] : (∀ i, β i →+ γ) ≃+ ((Π₀ i, β i) →+ γ) where
  toFun := sumAddHom
  invFun := fun F i => F.comp (singleAddHom β i)
  left_inv := fun x => by
    ext
    simp
  right_inv := fun ψ => by
    ext
    simp
  map_add' := fun F G => by
    ext
    simp

/-- The `dfinsupp` version of `finsupp.lift_add_hom_single_add_hom`,-/
@[simp]
theorem lift_add_hom_single_add_hom [∀ i, AddCommMonoidₓ (β i)] :
    liftAddHom (singleAddHom β) = AddMonoidHom.id (Π₀ i, β i) :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

/-- The `dfinsupp` version of `finsupp.lift_add_hom_apply_single`,-/
theorem lift_add_hom_apply_single [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) (x : β i) :
    liftAddHom f (single i x) = f i x := by
  simp

/-- The `dfinsupp` version of `finsupp.lift_add_hom_comp_single`,-/
theorem lift_add_hom_comp_single [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (f : ∀ i, β i →+ γ) (i : ι) :
    (liftAddHom f).comp (singleAddHom β i) = f i := by
  simp

/-- The `dfinsupp` version of `finsupp.comp_lift_add_hom`,-/
theorem comp_lift_add_hom {δ : Type _} [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] [AddCommMonoidₓ δ] (g : γ →+ δ)
    (f : ∀ i, β i →+ γ) : g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]

@[simp]
theorem sum_add_hom_zero [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] : (sumAddHom fun i => (0 : β i →+ γ)) = 0 :=
  (liftAddHom : (∀ i, β i →+ γ) ≃+ _).map_zero

@[simp]
theorem sum_add_hom_add [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] (g : ∀ i, β i →+ γ) (h : ∀ i, β i →+ γ) :
    (sumAddHom fun i => g i + h i) = sumAddHom g + sumAddHom h :=
  liftAddHom.map_add _ _

@[simp]
theorem sum_add_hom_single_add_hom [∀ i, AddCommMonoidₓ (β i)] : sumAddHom (singleAddHom β) = AddMonoidHom.id _ :=
  lift_add_hom_single_add_hom

theorem comp_sum_add_hom {δ : Type _} [∀ i, AddZeroClassₓ (β i)] [AddCommMonoidₓ γ] [AddCommMonoidₓ δ] (g : γ →+ δ)
    (f : ∀ i, β i →+ γ) : g.comp (sumAddHom f) = sumAddHom fun a => g.comp (f a) :=
  comp_lift_add_hom _ _

theorem sum_sub_index [∀ i, AddGroupₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [AddCommGroupₓ γ] {f g : Π₀ i, β i}
    {h : ∀ i, β i → γ} (h_sub : ∀ i b₁ b₂, h i (b₁ - b₂) = h i b₁ - h i b₂) : (f - g).Sum h = f.Sum h - g.Sum h := by
  have := (lift_add_hom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g
  rw [lift_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply, sum_add_hom_apply] at this
  exact this

@[to_additive]
theorem prod_finset_sum_index {γ : Type w} {α : Type x} [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoidₓ γ] {s : Finset α} {g : α → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (∏ i in s, (g i).Prod h) = (∑ i in s, g i).Prod h := by
  classical
  exact
    Finset.induction_on s
      (by
        simp [← prod_zero_index])
      (by
        simp (config := { contextual := true })[← prod_add_index, ← h_zero, ← h_add])

@[to_additive]
theorem prod_sum_index {ι₁ : Type u₁} [DecidableEq ι₁] {β₁ : ι₁ → Type v₁} [∀ i₁, Zero (β₁ i₁)]
    [∀ (i) (x : β₁ i), Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]
    [CommMonoidₓ γ] {f : Π₀ i₁, β₁ i₁} {g : ∀ i₁, β₁ i₁ → Π₀ i, β i} {h : ∀ i, β i → γ} (h_zero : ∀ i, h i 0 = 1)
    (h_add : ∀ i b₁ b₂, h i (b₁ + b₂) = h i b₁ * h i b₂) : (f.Sum g).Prod h = f.Prod fun i b => (g i b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm

@[simp]
theorem sum_single [∀ i, AddCommMonoidₓ (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] {f : Π₀ i, β i} :
    f.Sum single = f := by
  have := AddMonoidHom.congr_fun lift_add_hom_single_add_hom f
  rw [lift_add_hom_apply, sum_add_hom_apply] at this
  exact this

@[to_additive]
theorem prod_subtype_domain_index [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)] [CommMonoidₓ γ] {v : Π₀ i, β i}
    {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ} (hp : ∀, ∀ x ∈ v.support, ∀, p x) :
    ((v.subtypeDomain p).Prod fun i b => h i b) = v.Prod h :=
  Finset.prod_bij (fun p _ => p)
    (by
      simp )
    (by
      simp )
    (fun ⟨a₀, ha₀⟩ ⟨a₁, ha₁⟩ => by
      simp )
    fun i hi =>
    ⟨⟨i, hp i hi⟩, by
      simpa using hi, rfl⟩

omit dec

theorem subtype_domain_sum [∀ i, AddCommMonoidₓ (β i)] {s : Finset γ} {h : γ → Π₀ i, β i} {p : ι → Prop}
    [DecidablePred p] : (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  (subtypeDomainAddMonoidHom β p).map_sum _ s

theorem subtype_domain_finsupp_sum {δ : γ → Type x} [DecidableEq γ] [∀ c, Zero (δ c)]
    [∀ (c) (x : δ c), Decidable (x ≠ 0)] [∀ i, AddCommMonoidₓ (β i)] {p : ι → Prop} [DecidablePred p] {s : Π₀ c, δ c}
    {h : ∀ c, δ c → Π₀ i, β i} : (s.Sum h).subtypeDomain p = s.Sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum

end ProdAndSum

/-! ### Bundled versions of `dfinsupp.map_range`

The names should match the equivalent bundled `finsupp.map_range` definitions.
-/


section MapRange

omit dec

variable [∀ i, AddZeroClassₓ (β i)] [∀ i, AddZeroClassₓ (β₁ i)] [∀ i, AddZeroClassₓ (β₂ i)]

theorem map_range_add (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i 0 = 0) (hf' : ∀ i x y, f i (x + y) = f i x + f i y)
    (g₁ g₂ : Π₀ i, β₁ i) : mapRange f hf (g₁ + g₂) = mapRange f hf g₁ + mapRange f hf g₂ := by
  ext
  simp only [← map_range_apply f, ← coe_add, ← Pi.add_apply, ← hf']

/-- `dfinsupp.map_range` as an `add_monoid_hom`. -/
@[simps apply]
def mapRange.addMonoidHom (f : ∀ i, β₁ i →+ β₂ i) : (Π₀ i, β₁ i) →+ Π₀ i, β₂ i where
  toFun := mapRange (fun i x => f i x) fun i => (f i).map_zero
  map_zero' := map_range_zero _ _
  map_add' := map_range_add _ _ fun i => (f i).map_add

@[simp]
theorem mapRange.add_monoid_hom_id : (mapRange.addMonoidHom fun i => AddMonoidHom.id (β₂ i)) = AddMonoidHom.id _ :=
  AddMonoidHom.ext map_range_id

theorem mapRange.add_monoid_hom_comp (f : ∀ i, β₁ i →+ β₂ i) (f₂ : ∀ i, β i →+ β₁ i) :
    (mapRange.addMonoidHom fun i => (f i).comp (f₂ i)) = (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <| map_range_comp (fun i x => f i x) (fun i x => f₂ i x) _ _ _

/-- `dfinsupp.map_range.add_monoid_hom` as an `add_equiv`. -/
@[simps apply]
def mapRange.addEquiv (e : ∀ i, β₁ i ≃+ β₂ i) : (Π₀ i, β₁ i) ≃+ Π₀ i, β₂ i :=
  { mapRange.addMonoidHom fun i => (e i).toAddMonoidHom with
    toFun := mapRange (fun i x => e i x) fun i => (e i).map_zero,
    invFun := mapRange (fun i x => (e i).symm x) fun i => (e i).symm.map_zero,
    left_inv := fun x => by
      rw [← map_range_comp] <;>
        · simp_rw [AddEquiv.symm_comp_self]
          simp
          ,
    right_inv := fun x => by
      rw [← map_range_comp] <;>
        · simp_rw [AddEquiv.self_comp_symm]
          simp
           }

@[simp]
theorem mapRange.add_equiv_refl : (map_range.add_equiv fun i => AddEquiv.refl (β₁ i)) = AddEquiv.refl _ :=
  AddEquiv.ext map_range_id

theorem mapRange.add_equiv_trans (f : ∀ i, β i ≃+ β₁ i) (f₂ : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv fun i => (f i).trans (f₂ i)) = (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext <| map_range_comp (fun i x => f₂ i x) (fun i x => f i x) _ _ _

@[simp]
theorem mapRange.add_equiv_symm (e : ∀ i, β₁ i ≃+ β₂ i) :
    (mapRange.addEquiv e).symm = mapRange.addEquiv fun i => (e i).symm :=
  rfl

end MapRange

end Dfinsupp

/-! ### Product and sum lemmas for bundled morphisms.

In this section, we provide analogues of `add_monoid_hom.map_sum`, `add_monoid_hom.coe_finset_sum`,
and `add_monoid_hom.finset_sum_apply` for `dfinsupp.sum` and `dfinsupp.sum_add_hom` instead of
`finset.sum`.

We provide these for `add_monoid_hom`, `monoid_hom`, `ring_hom`, `add_equiv`, and `mul_equiv`.

Lemmas for `linear_map` and `linear_equiv` are in another file.
-/


section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp, to_additive]
theorem map_dfinsupp_prod [CommMonoidₓ R] [CommMonoidₓ S] (h : R →* S) (f : Π₀ i, β i) (g : ∀ i, β i → R) :
    h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _

@[to_additive]
theorem coe_dfinsupp_prod [Monoidₓ R] [CommMonoidₓ S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) :
    ⇑(f.Prod g) = f.Prod fun a b => g a b :=
  coe_finset_prod _ _

@[simp, to_additive]
theorem dfinsupp_prod_apply [Monoidₓ R] [CommMonoidₓ S] (f : Π₀ i, β i) (g : ∀ i, β i → R →* S) (r : R) :
    (f.Prod g) r = f.Prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _

end MonoidHom

namespace RingHom

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp]
theorem map_dfinsupp_prod [CommSemiringₓ R] [CommSemiringₓ S] (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i → R) :
    h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _

@[simp]
theorem map_dfinsupp_sum [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] (h : R →+* S) (f : Π₀ i, β i) (g : ∀ i, β i → R) :
    h (f.Sum g) = f.Sum fun a b => h (g a b) :=
  h.map_sum _ _

end RingHom

namespace MulEquiv

variable {R S : Type _}

variable [∀ i, Zero (β i)] [∀ (i) (x : β i), Decidable (x ≠ 0)]

@[simp, to_additive]
theorem map_dfinsupp_prod [CommMonoidₓ R] [CommMonoidₓ S] (h : R ≃* S) (f : Π₀ i, β i) (g : ∀ i, β i → R) :
    h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  h.map_prod _ _

end MulEquiv

/-! The above lemmas, repeated for `dfinsupp.sum_add_hom`. -/


namespace AddMonoidHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [AddCommMonoidₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClassₓ (β i)] (h : R →+ S)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R) : h (sumAddHom g f) = sumAddHom (fun i => h.comp (g i)) f :=
  congr_fun (comp_lift_add_hom h g) f

@[simp]
theorem dfinsupp_sum_add_hom_apply [AddZeroClassₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClassₓ (β i)] (f : Π₀ i, β i)
    (g : ∀ i, β i →+ R →+ S) (r : R) : (sumAddHom g f) r = sumAddHom (fun i => (eval r).comp (g i)) f :=
  map_dfinsupp_sum_add_hom (eval r) f g

theorem coe_dfinsupp_sum_add_hom [AddZeroClassₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClassₓ (β i)] (f : Π₀ i, β i)
    (g : ∀ i, β i →+ R →+ S) : ⇑(sumAddHom g f) = sumAddHom (fun i => (coeFn R S).comp (g i)) f :=
  map_dfinsupp_sum_add_hom (coeFn R S) f g

end AddMonoidHom

namespace RingHom

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] [∀ i, AddZeroClassₓ (β i)] (h : R →+* S)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R) : h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_lift_add_hom h.toAddMonoidHom g) f

end RingHom

namespace AddEquiv

variable {R S : Type _}

open Dfinsupp

@[simp]
theorem map_dfinsupp_sum_add_hom [AddCommMonoidₓ R] [AddCommMonoidₓ S] [∀ i, AddZeroClassₓ (β i)] (h : R ≃+ S)
    (f : Π₀ i, β i) (g : ∀ i, β i →+ R) : h (sumAddHom g f) = sumAddHom (fun i => h.toAddMonoidHom.comp (g i)) f :=
  AddMonoidHom.congr_fun (comp_lift_add_hom h.toAddMonoidHom g) f

end AddEquiv

end

