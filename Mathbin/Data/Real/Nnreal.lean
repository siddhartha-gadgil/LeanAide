/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Real.Pointwise
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Module
import Mathbin.Algebra.Order.Nonneg

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.

## TODO

`semifield` instance
-/


open Classical BigOperators

/-- Nonnegative real numbers. -/
-- to ensure these instance are computable
def Nnreal :=
  { r : ℝ // 0 ≤ r }deriving OrderedSemiring, CommMonoidWithZero, FloorSemiring, SemilatticeInf, DenselyOrdered,
  OrderBot, CanonicallyLinearOrderedAddMonoid, LinearOrderedCommGroupWithZero, Archimedean, LinearOrderedSemiring,
  OrderedCommSemiring, CanonicallyOrderedCommSemiring, Sub, HasOrderedSub, Div, Inhabited

-- mathport name: «exprℝ≥0»
localized [Nnreal] notation " ℝ≥0 " => Nnreal

namespace Nnreal

instance : Coe ℝ≥0 ℝ :=
  ⟨Subtype.val⟩

-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥0 ) : n.val = n :=
  rfl

instance : CanLift ℝ ℝ≥0 :=
  Subtype.canLift _

protected theorem eq {n m : ℝ≥0 } : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq

protected theorem eq_iff {n m : ℝ≥0 } : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Iff.intro Nnreal.eq (congr_arg coe)

theorem ne_iff {x y : ℝ≥0 } : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_iff_not_of_iff <| Nnreal.eq_iff

protected theorem forall {p : ℝ≥0 → Prop} : (∀ x : ℝ≥0 , p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.forall

protected theorem exists {p : ℝ≥0 → Prop} : (∃ x : ℝ≥0 , p x) ↔ ∃ (x : ℝ)(hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.exists

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def _root_.real.to_nnreal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_rightₓ _ _⟩

theorem _root_.real.coe_to_nnreal (r : ℝ) (hr : 0 ≤ r) : (Real.toNnreal r : ℝ) = r :=
  max_eq_leftₓ hr

theorem _root_.real.le_coe_to_nnreal (r : ℝ) : r ≤ Real.toNnreal r :=
  le_max_leftₓ r 0

theorem coe_nonneg (r : ℝ≥0 ) : (0 : ℝ) ≤ r :=
  r.2

@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0 ) : ℝ) = a :=
  rfl

example : Zero ℝ≥0 := by
  infer_instance

example : One ℝ≥0 := by
  infer_instance

example : Add ℝ≥0 := by
  infer_instance

noncomputable example : Sub ℝ≥0 := by
  infer_instance

example : Mul ℝ≥0 := by
  infer_instance

noncomputable example : Inv ℝ≥0 := by
  infer_instance

noncomputable example : Div ℝ≥0 := by
  infer_instance

example : LE ℝ≥0 := by
  infer_instance

example : HasBot ℝ≥0 := by
  infer_instance

example : Inhabited ℝ≥0 := by
  infer_instance

example : Nontrivial ℝ≥0 := by
  infer_instance

protected theorem coe_injective : Function.Injective (coe : ℝ≥0 → ℝ) :=
  Subtype.coe_injective

@[simp, norm_cast]
protected theorem coe_eq {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  Nnreal.coe_injective.eq_iff

protected theorem coe_zero : ((0 : ℝ≥0 ) : ℝ) = 0 :=
  rfl

protected theorem coe_one : ((1 : ℝ≥0 ) : ℝ) = 1 :=
  rfl

protected theorem coe_add (r₁ r₂ : ℝ≥0 ) : ((r₁ + r₂ : ℝ≥0 ) : ℝ) = r₁ + r₂ :=
  rfl

protected theorem coe_mul (r₁ r₂ : ℝ≥0 ) : ((r₁ * r₂ : ℝ≥0 ) : ℝ) = r₁ * r₂ :=
  rfl

protected theorem coe_inv (r : ℝ≥0 ) : ((r⁻¹ : ℝ≥0 ) : ℝ) = r⁻¹ :=
  rfl

protected theorem coe_div (r₁ r₂ : ℝ≥0 ) : ((r₁ / r₂ : ℝ≥0 ) : ℝ) = r₁ / r₂ :=
  rfl

@[simp, norm_cast]
protected theorem coe_bit0 (r : ℝ≥0 ) : ((bit0 r : ℝ≥0 ) : ℝ) = bit0 r :=
  rfl

@[simp, norm_cast]
protected theorem coe_bit1 (r : ℝ≥0 ) : ((bit1 r : ℝ≥0 ) : ℝ) = bit1 r :=
  rfl

protected theorem coe_two : ((2 : ℝ≥0 ) : ℝ) = 2 :=
  rfl

@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0 } (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0 ) : ℝ) = r₁ - r₂ :=
  max_eq_leftₓ <|
    le_sub.2 <| by
      simp [← show (r₂ : ℝ) ≤ r₁ from h]

-- TODO: setup semifield!
@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0 ) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← Nnreal.coe_zero, Nnreal.coe_eq]

@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0 ) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← Nnreal.coe_one, Nnreal.coe_eq]

theorem coe_ne_zero {r : ℝ≥0 } : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by
  norm_cast

example : CommSemiringₓ ℝ≥0 := by
  infer_instance

/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def toRealHom : ℝ≥0 →+* ℝ :=
  ⟨coe, Nnreal.coe_one, Nnreal.coe_mul, Nnreal.coe_zero, Nnreal.coe_add⟩

@[simp]
theorem coe_to_real_hom : ⇑to_real_hom = coe :=
  rfl

section Actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type _} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M toRealHom.toMonoidHom

theorem smul_def {M : Type _} [MulAction ℝ M] (c : ℝ≥0 ) (x : M) : c • x = (c : ℝ) • x :=
  rfl

instance {M N : Type _} [MulAction ℝ M] [MulAction ℝ N] [HasSmul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc := fun r => (smul_assoc (r : ℝ) : _)

instance smul_comm_class_left {M N : Type _} [MulAction ℝ N] [HasSmul M N] [SmulCommClass ℝ M N] :
    SmulCommClass ℝ≥0 M N where smul_comm := fun r => (smul_comm (r : ℝ) : _)

instance smul_comm_class_right {M N : Type _} [MulAction ℝ N] [HasSmul M N] [SmulCommClass M ℝ N] :
    SmulCommClass M ℝ≥0 N where smul_comm := fun m r => (smul_comm m (r : ℝ) : _)

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type _} [AddMonoidₓ M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type _} [AddCommMonoidₓ M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M toRealHom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type _} [Semiringₓ A] [Algebra ℝ A] : Algebra ℝ≥0 A where
  smul := (· • ·)
  commutes' := fun r x => by
    simp [← Algebra.commutes]
  smul_def' := fun r x => by
    simp [Algebra.smul_def (r : ℝ) x, ← smul_def]
  toRingHom := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
example : Algebra ℝ≥0 ℝ := by
  infer_instance

example : DistribMulAction ℝ≥0 ˣ ℝ := by
  infer_instance

end Actions

example : MonoidWithZeroₓ ℝ≥0 := by
  infer_instance

example : CommMonoidWithZero ℝ≥0 := by
  infer_instance

noncomputable example : CommGroupWithZero ℝ≥0 := by
  infer_instance

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0 ) (a : α) :
    ((s.indicator f a : ℝ≥0 ) : ℝ) = s.indicator (fun x => f x) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _

@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0 ) (n : ℕ) : ((r ^ n : ℝ≥0 ) : ℝ) = r ^ n :=
  toRealHom.map_pow r n

@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0 ) (n : ℤ) : ((r ^ n : ℝ≥0 ) : ℝ) = r ^ n := by
  cases n <;> simp

@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0 ) : ((l.Sum : ℝ≥0 ) : ℝ) = (l.map coe).Sum :=
  toRealHom.map_list_sum l

@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0 ) : ((l.Prod : ℝ≥0 ) : ℝ) = (l.map coe).Prod :=
  toRealHom.map_list_prod l

@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0 ) : ((s.Sum : ℝ≥0 ) : ℝ) = (s.map coe).Sum :=
  toRealHom.map_multiset_sum s

@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0 ) : ((s.Prod : ℝ≥0 ) : ℝ) = (s.map coe).Prod :=
  toRealHom.map_multiset_prod s

@[norm_cast]
theorem coe_sum {α} {s : Finset α} {f : α → ℝ≥0 } : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
  toRealHom.map_sum _ _

theorem _root_.real.to_nnreal_sum_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNnreal (∑ a in s, f a) = ∑ a in s, Real.toNnreal (f a) := by
  rw [← Nnreal.coe_eq, Nnreal.coe_sum, Real.coe_to_nnreal _ (Finset.sum_nonneg hf)]
  exact
    Finset.sum_congr rfl fun x hxs => by
      rw [Real.coe_to_nnreal _ (hf x hxs)]

@[norm_cast]
theorem coe_prod {α} {s : Finset α} {f : α → ℝ≥0 } : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
  toRealHom.map_prod _ _

theorem _root_.real.to_nnreal_prod_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNnreal (∏ a in s, f a) = ∏ a in s, Real.toNnreal (f a) := by
  rw [← Nnreal.coe_eq, Nnreal.coe_prod, Real.coe_to_nnreal _ (Finset.prod_nonneg hf)]
  exact
    Finset.prod_congr rfl fun x hxs => by
      rw [Real.coe_to_nnreal _ (hf x hxs)]

theorem nsmul_coe (r : ℝ≥0 ) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := by
  norm_cast

@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0 ) : ℝ) = n :=
  map_nat_cast toRealHom n

noncomputable example : LinearOrderₓ ℝ≥0 := by
  infer_instance

@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl

@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0 } : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl

@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0 } : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl

protected theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ) := fun _ _ => Nnreal.coe_le_coe.2

protected theorem _root_.real.to_nnreal_mono : Monotone Real.toNnreal := fun x y h => max_le_max h (le_reflₓ 0)

@[simp]
theorem _root_.real.to_nnreal_coe {r : ℝ≥0 } : Real.toNnreal r = r :=
  Nnreal.eq <| max_eq_leftₓ r.2

@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0 ) n :=
  Nnreal.eq (Nnreal.coe_nat_cast n).symm

@[simp]
theorem to_nnreal_coe_nat (n : ℕ) : Real.toNnreal n = n :=
  Nnreal.eq <| by
    simp [← Real.coe_to_nnreal]

/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNnreal coe :=
  GaloisInsertion.monotoneIntro Nnreal.coe_mono Real.to_nnreal_mono Real.le_coe_to_nnreal fun _ => Real.to_nnreal_coe

-- note that anything involving the (decidability of the) linear order, including `⊔`/`⊓` (min, max)
-- will be noncomputable, everything else should not be.
example : OrderBot ℝ≥0 := by
  infer_instance

example : PartialOrderₓ ℝ≥0 := by
  infer_instance

noncomputable example : CanonicallyLinearOrderedAddMonoid ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by
  infer_instance

noncomputable example : DistribLattice ℝ≥0 := by
  infer_instance

noncomputable example : SemilatticeInf ℝ≥0 := by
  infer_instance

noncomputable example : SemilatticeSup ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedSemiring ℝ≥0 := by
  infer_instance

example : OrderedCommSemiring ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by
  infer_instance

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by
  infer_instance

example : CanonicallyOrderedCommSemiring ℝ≥0 := by
  infer_instance

example : DenselyOrdered ℝ≥0 := by
  infer_instance

example : NoMaxOrder ℝ≥0 := by
  infer_instance

/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `set.Iic a`. -/
@[simps apply_coe_coe]
def orderIsoIccZeroCoe (a : ℝ≥0 ) : Set.Icc (0 : ℝ) a ≃o Set.Iic a where
  toEquiv := Equivₓ.Set.sep (Set.Ici 0) fun x => x ≤ a
  map_rel_iff' := fun x y => Iff.rfl

@[simp]
theorem order_iso_Icc_zero_coe_symm_apply_coe (a : ℝ≥0 ) (b : Set.Iic a) : ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl

-- note we need the `@` to make the `has_mem.mem` have a sensible type
theorem coe_image {s : Set ℝ≥0 } : coe '' s = { x : ℝ | ∃ h : 0 ≤ x, @HasMem.Mem ℝ≥0 _ _ ⟨x, h⟩ s } :=
  Subtype.coe_image

theorem bdd_above_coe {s : Set ℝ≥0 } : BddAbove ((coe : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNnreal b, fun ⟨y, hy⟩ hys => show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩

theorem bdd_below_coe (s : Set ℝ≥0 ) : BddBelow ((coe : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun r ⟨q, _, Eq⟩ => Eq ▸ q.2⟩

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.Sup_empty.le

@[norm_cast]
theorem coe_Sup (s : Set ℝ≥0 ) : (↑(sup s) : ℝ) = sup ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <| @subset_Sup_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0 )⟩ s <| (Real.Sup_nonneg _) fun y ⟨x, _, hy⟩ => hy ▸ x.2

@[norm_cast]
theorem coe_supr {ι : Sort _} (s : ι → ℝ≥0 ) : (↑(⨆ i, s i) : ℝ) = ⨆ i, s i := by
  rw [supr, supr, coe_Sup, Set.range_comp]

@[norm_cast]
theorem coe_Inf (s : Set ℝ≥0 ) : (↑(inf s) : ℝ) = inf ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <| @subset_Inf_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0 )⟩ s <| (Real.Inf_nonneg _) fun y ⟨x, _, hy⟩ => hy ▸ x.2

@[simp]
theorem Inf_empty : inf (∅ : Set ℝ≥0 ) = 0 := by
  rw [← Nnreal.coe_eq_zero, coe_Inf, Set.image_empty, Real.Inf_empty]

@[norm_cast]
theorem coe_infi {ι : Sort _} (s : ι → ℝ≥0 ) : (↑(⨅ i, s i) : ℝ) = ⨅ i, s i := by
  rw [infi, infi, coe_Inf, Set.range_comp]

theorem le_infi_add_infi {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0 } {g : ι' → ℝ≥0 } {a : ℝ≥0 }
    (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j := by
  rw [← Nnreal.coe_le_coe, Nnreal.coe_add, coe_infi, coe_infi]
  exact le_cinfi_add_cinfi h

example : Archimedean ℝ≥0 := by
  infer_instance

-- TODO: why are these three instances necessary? why aren't they inferred?
instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariant_class_left ℝ≥0

instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (· + ·) (· < ·) :=
  OrderedCancelAddCommMonoid.to_contravariant_class_left ℝ≥0

instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (· * ·) (· ≤ ·) :=
  OrderedCommMonoid.to_covariant_class_left ℝ≥0

theorem le_of_forall_pos_le_add {a b : ℝ≥0 } (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
  le_of_forall_le_of_dense fun x hxb => by
    rcases le_iff_exists_add.1 (le_of_ltₓ hxb) with ⟨ε, rfl⟩
    exact h _ ((lt_add_iff_pos_right b).1 hxb)

theorem lt_iff_exists_rat_btwn (a b : ℝ≥0 ) : a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNnreal q ∧ Real.toNnreal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_transₓ a.2 <| le_of_ltₓ haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [← Real.coe_to_nnreal _ this, ← nnreal.coe_lt_coe.symm, ← haq, ← hqb]⟩)
    fun ⟨q, _, haq, hqb⟩ => lt_transₓ haq hqb

theorem bot_eq_zero : (⊥ : ℝ≥0 ) = 0 :=
  rfl

theorem mul_sup (a b c : ℝ≥0 ) : a * (b⊔c) = a * b⊔a * c :=
  mul_max_of_nonneg _ _ <| zero_le a

theorem sup_mul (a b c : ℝ≥0 ) : (a⊔b) * c = a * c⊔b * c :=
  max_mul_of_nonneg _ _ <| zero_le c

theorem mul_finset_sup {α} (r : ℝ≥0 ) (s : Finset α) (f : α → ℝ≥0 ) : r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (Nnreal.mul_sup r) (mul_zero r)

theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0 ) (r : ℝ≥0 ) : s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => Nnreal.sup_mul x y r) (zero_mul r)

theorem finset_sup_div {α} {f : α → ℝ≥0 } {s : Finset α} (r : ℝ≥0 ) : s.sup f / r = s.sup fun a => f a / r := by
  simp only [← div_eq_inv_mul, ← mul_finset_sup]

@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0 ) : ((max x y : ℝ≥0 ) : ℝ) = max (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_max

@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0 ) : ((min x y : ℝ≥0 ) : ℝ) = min (x : ℝ) (y : ℝ) :=
  Nnreal.coe_mono.map_min

@[simp]
theorem zero_le_coe {q : ℝ≥0 } : 0 ≤ (q : ℝ) :=
  q.2

end Nnreal

namespace Real

section ToNnreal

@[simp]
theorem to_nnreal_zero : Real.toNnreal 0 = 0 := by
  simp [← Real.toNnreal] <;> rfl

@[simp]
theorem to_nnreal_one : Real.toNnreal 1 = 1 := by
  simp [← Real.toNnreal, ← max_eq_leftₓ (zero_le_one : (0 : ℝ) ≤ 1)] <;> rfl

@[simp]
theorem to_nnreal_pos {r : ℝ} : 0 < Real.toNnreal r ↔ 0 < r := by
  simp [← Real.toNnreal, ← nnreal.coe_lt_coe.symm, ← lt_irreflₓ]

@[simp]
theorem to_nnreal_eq_zero {r : ℝ} : Real.toNnreal r = 0 ↔ r ≤ 0 := by
  simpa [-to_nnreal_pos] using not_iff_not.2 (@to_nnreal_pos r)

theorem to_nnreal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNnreal r = 0 :=
  to_nnreal_eq_zero.2

@[simp]
theorem coe_to_nnreal' (r : ℝ) : (Real.toNnreal r : ℝ) = max r 0 :=
  rfl

@[simp]
theorem to_nnreal_le_to_nnreal_iff {r p : ℝ} (hp : 0 ≤ p) : Real.toNnreal r ≤ Real.toNnreal p ↔ r ≤ p := by
  simp [← nnreal.coe_le_coe.symm, ← Real.toNnreal, ← hp]

@[simp]
theorem to_nnreal_lt_to_nnreal_iff' {r p : ℝ} : Real.toNnreal r < Real.toNnreal p ↔ r < p ∧ 0 < p :=
  Nnreal.coe_lt_coe.symm.trans max_lt_max_left_iff

theorem to_nnreal_lt_to_nnreal_iff {r p : ℝ} (h : 0 < p) : Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  to_nnreal_lt_to_nnreal_iff'.trans (and_iff_left h)

theorem to_nnreal_lt_to_nnreal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) : Real.toNnreal r < Real.toNnreal p ↔ r < p :=
  to_nnreal_lt_to_nnreal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_ltₓ hr h⟩⟩

@[simp]
theorem to_nnreal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) : Real.toNnreal (r + p) = Real.toNnreal r + Real.toNnreal p :=
  Nnreal.eq <| by
    simp [← Real.toNnreal, ← hr, ← hp, ← add_nonneg]

theorem to_nnreal_add_to_nnreal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNnreal r + Real.toNnreal p = Real.toNnreal (r + p) :=
  (Real.to_nnreal_add hr hp).symm

theorem to_nnreal_le_to_nnreal {r p : ℝ} (h : r ≤ p) : Real.toNnreal r ≤ Real.toNnreal p :=
  Real.to_nnreal_mono h

theorem to_nnreal_add_le {r p : ℝ} : Real.toNnreal (r + p) ≤ Real.toNnreal r + Real.toNnreal p :=
  Nnreal.coe_le_coe.1 <| max_leₓ (add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _)) Nnreal.zero_le_coe

theorem to_nnreal_le_iff_le_coe {r : ℝ} {p : ℝ≥0 } : Real.toNnreal r ≤ p ↔ r ≤ ↑p :=
  Nnreal.gi.gc r p

theorem le_to_nnreal_iff_coe_le {r : ℝ≥0 } {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNnreal p ↔ ↑r ≤ p := by
  rw [← Nnreal.coe_le_coe, Real.coe_to_nnreal p hp]

theorem le_to_nnreal_iff_coe_le' {r : ℝ≥0 } {p : ℝ} (hr : 0 < r) : r ≤ Real.toNnreal p ↔ ↑r ≤ p :=
  ((le_or_ltₓ 0 p).elim le_to_nnreal_iff_coe_le) fun hp => by
    simp only [← (hp.trans_le r.coe_nonneg).not_le, ← to_nnreal_eq_zero.2 hp.le, ← hr.not_le]

theorem to_nnreal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0 } (ha : 0 ≤ r) : Real.toNnreal r < p ↔ r < ↑p := by
  rw [← Nnreal.coe_lt_coe, Real.coe_to_nnreal r ha]

theorem lt_to_nnreal_iff_coe_lt {r : ℝ≥0 } {p : ℝ} : r < Real.toNnreal p ↔ ↑r < p := by
  cases le_totalₓ 0 p
  · rw [← Nnreal.coe_lt_coe, Real.coe_to_nnreal p h]
    
  · rw [to_nnreal_eq_zero.2 h]
    constructor
    · intro
      have := not_lt_of_le (zero_le r)
      contradiction
      
    · intro rp
      have : ¬p ≤ 0 := not_le_of_lt (lt_of_le_of_ltₓ (Nnreal.coe_nonneg _) rp)
      contradiction
      
    

@[simp]
theorem to_nnreal_bit0 (r : ℝ) : Real.toNnreal (bit0 r) = bit0 (Real.toNnreal r) := by
  cases' le_totalₓ r 0 with hr hr
  · rw [to_nnreal_of_nonpos hr, to_nnreal_of_nonpos, bit0_zero]
    exact add_nonpos hr hr
    
  · exact to_nnreal_add hr hr
    

@[simp]
theorem to_nnreal_bit1 {r : ℝ} (hr : 0 ≤ r) : Real.toNnreal (bit1 r) = bit1 (Real.toNnreal r) :=
  (Real.to_nnreal_add
        (by
          simp [← hr])
        zero_le_one).trans
    (by
      simp [← bit1])

end ToNnreal

end Real

open Real

namespace Nnreal

section Mul

theorem mul_eq_mul_left {a b c : ℝ≥0 } (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [← Nnreal.eq_iff, ← Nnreal.eq_iff, Nnreal.coe_mul, Nnreal.coe_mul]
  constructor
  · exact mul_left_cancel₀ (mt (@Nnreal.eq_iff a 0).1 h)
    
  · intro h
    rw [h]
    

theorem _root_.real.to_nnreal_mul {p q : ℝ} (hp : 0 ≤ p) : Real.toNnreal (p * q) = Real.toNnreal p * Real.toNnreal q :=
  by
  cases' le_totalₓ 0 q with hq hq
  · apply Nnreal.eq
    simp [← Real.toNnreal, ← hp, ← hq, ← max_eq_leftₓ, ← mul_nonneg]
    
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero]
    

end Mul

section Pow

theorem pow_antitone_exp {a : ℝ≥0 } (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn

theorem exists_pow_lt_of_lt_one {a b : ℝ≥0 } (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a := by
  simpa only [coe_pow, ← Nnreal.coe_lt_coe] using exists_pow_lt_of_lt_one (Nnreal.coe_pos.2 ha) (Nnreal.coe_lt_coe.2 hb)

theorem exists_mem_Ico_zpow {x : ℝ≥0 } {y : ℝ≥0 } (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) := by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ (n + 1) :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩

theorem exists_mem_Ioc_zpow {x : ℝ≥0 } {y : ℝ≥0 } (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) := by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ (n + 1) :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← Nnreal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/


theorem sub_def {r p : ℝ≥0 } : r - p = Real.toNnreal (r - p) :=
  rfl

theorem coe_sub_def {r p : ℝ≥0 } : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl

noncomputable example : HasOrderedSub ℝ≥0 := by
  infer_instance

theorem sub_div (a b c : ℝ≥0 ) : (a - b) / c = a / c - b / c := by
  simp only [← div_eq_mul_inv, ← tsub_mul]

end Sub

section Inv

theorem sum_div {ι} (s : Finset ι) (f : ι → ℝ≥0 ) (b : ℝ≥0 ) : (∑ i in s, f i) / b = ∑ i in s, f i / b := by
  simp only [← div_eq_mul_inv, ← Finset.sum_mul]

@[simp]
theorem inv_pos {r : ℝ≥0 } : 0 < r⁻¹ ↔ 0 < r := by
  simp [← pos_iff_ne_zero]

theorem div_pos {r p : ℝ≥0 } (hr : 0 < r) (hp : 0 < p) : 0 < r / p := by
  simpa only [← div_eq_mul_inv] using mul_pos hr (inv_pos.2 hp)

theorem div_self_le (r : ℝ≥0 ) : r / r ≤ 1 :=
  div_self_le_one (r : ℝ)

@[simp]
theorem inv_le {r p : ℝ≥0 } (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

theorem inv_le_of_le_mul {r p : ℝ≥0 } (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases' r = 0 <;> simp [*, ← inv_le]

@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0 } (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0 } (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

theorem mul_le_iff_le_inv {a b r : ℝ≥0 } (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  have : 0 < r := lt_of_le_of_neₓ (zero_le r) hr.symm
  rw [← @mul_le_mul_left _ _ a _ r this, ← mul_assoc, mul_inv_cancel hr, one_mulₓ]

theorem le_div_iff_mul_le {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b := by
  rw [div_eq_inv_mul, ← mul_le_iff_le_inv hr, mul_comm]

theorem div_le_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  @div_le_iff ℝ _ a r b <| pos_iff_ne_zero.2 hr

theorem div_le_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
  @div_le_iff' ℝ _ a r b <| pos_iff_ne_zero.2 hr

theorem div_le_of_le_mul {a b c : ℝ≥0 } (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by
    simp [← h0]
  else (div_le_iff h0).2 h

theorem div_le_of_le_mul' {a b c : ℝ≥0 } (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h

theorem le_div_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  @le_div_iff ℝ _ a b r <| pos_iff_ne_zero.2 hr

theorem le_div_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
  @le_div_iff' ℝ _ a b r <| pos_iff_ne_zero.2 hr

theorem div_lt_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)

theorem div_lt_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)

theorem lt_div_iff {a b r : ℝ≥0 } (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)

theorem lt_div_iff' {a b r : ℝ≥0 } (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)

theorem mul_lt_of_lt_div {a b r : ℝ≥0 } (h : a < b / r) : a * r < b := by
  refine' (lt_div_iff fun hr => False.elim _).1 h
  subst r
  simpa using h

theorem div_le_div_left_of_le {a b c : ℝ≥0 } (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) : a / b ≤ a / c := by
  by_cases' a0 : a = 0
  · rw [a0, zero_div, zero_div]
    
  · cases' a with a ha
    replace a0 : 0 < a := lt_of_le_of_neₓ ha (ne_of_ltₓ (zero_lt_iff.mpr a0))
    exact (div_le_div_left a0 b0 c0).mpr cb
    

theorem div_le_div_left {a b c : ℝ≥0 } (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) : a / b ≤ a / c ↔ c ≤ b := by
  rw [Nnreal.div_le_iff b0.ne.symm, div_mul_eq_mul_div, Nnreal.le_div_iff_mul_le c0.ne.symm, mul_le_mul_left a0]

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0 } (h : ∀, ∀ a < 1, ∀, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha => by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_ltₓ (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by
      rwa [(· ≠ ·), inv_eq_zero]
    have : a * x⁻¹ < 1 := by
      rwa [← lt_inv_iff_mul_lt hx', inv_invₓ]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel hx, mul_oneₓ] at this

theorem div_add_div_same (a b c : ℝ≥0 ) : a / c + b / c = (a + b) / c :=
  Eq.symm <| right_distrib a b c⁻¹

theorem half_pos {a : ℝ≥0 } (h : 0 < a) : 0 < a / 2 :=
  div_pos h zero_lt_two

theorem add_halves (a : ℝ≥0 ) : a / 2 + a / 2 = a :=
  Nnreal.eq (add_halves a)

theorem half_le_self (a : ℝ≥0 ) : a / 2 ≤ a :=
  Nnreal.coe_le_coe.mp <| half_le_self a.coe_nonneg

theorem half_lt_self {a : ℝ≥0 } (h : a ≠ 0) : a / 2 < a := by
  rw [← Nnreal.coe_lt_coe, Nnreal.coe_div] <;> exact half_lt_self (bot_lt_iff_ne_bot.2 h)

theorem two_inv_lt_one : (2⁻¹ : ℝ≥0 ) < 1 := by
  simpa using half_lt_self zero_ne_one.symm

theorem div_lt_one_of_lt {a b : ℝ≥0 } (h : a < b) : a / b < 1 := by
  rwa [div_lt_iff, one_mulₓ]
  exact ne_of_gtₓ (lt_of_le_of_ltₓ (zero_le _) h)

@[field_simps]
theorem div_add_div (a : ℝ≥0 ) {b : ℝ≥0 } (c : ℝ≥0 ) {d : ℝ≥0 } (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [← Nnreal.eq_iff]
  simp only [← Nnreal.coe_add, ← Nnreal.coe_div, ← Nnreal.coe_mul]
  exact div_add_div _ _ (coe_ne_zero.2 hb) (coe_ne_zero.2 hd)

@[field_simps]
theorem add_div' (a b c : ℝ≥0 ) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  simpa using div_add_div b a one_ne_zero hc

@[field_simps]
theorem div_add' (a b c : ℝ≥0 ) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_commₓ, add_div', add_commₓ]

theorem _root_.real.to_nnreal_inv {x : ℝ} : Real.toNnreal x⁻¹ = (Real.toNnreal x)⁻¹ := by
  by_cases' hx : 0 ≤ x
  · nth_rw 0[← Real.coe_to_nnreal x hx]
    rw [← Nnreal.coe_inv, Real.to_nnreal_coe]
    
  · have hx' := le_of_not_geₓ hx
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')]
    

theorem _root_.real.to_nnreal_div {x y : ℝ} (hx : 0 ≤ x) : Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y :=
  by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.to_nnreal_inv, ← Real.to_nnreal_mul hx]

theorem _root_.real.to_nnreal_div' {x y : ℝ} (hy : 0 ≤ y) : Real.toNnreal (x / y) = Real.toNnreal x / Real.toNnreal y :=
  by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.to_nnreal_mul (inv_nonneg.2 hy), Real.to_nnreal_inv]

theorem inv_lt_one_iff {x : ℝ≥0 } (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rwa [← one_div, div_lt_iff hx, one_mulₓ]

theorem inv_lt_one {x : ℝ≥0 } (hx : 1 < x) : x⁻¹ < 1 :=
  (inv_lt_one_iff (zero_lt_one.trans hx).ne').2 hx

theorem zpow_pos {x : ℝ≥0 } (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n := by
  cases n
  · simp [← pow_pos hx.bot_lt _]
    
  · simp [← pow_pos hx.bot_lt _]
    

theorem inv_lt_inv_iff {x y : ℝ≥0 } (hx : x ≠ 0) (hy : y ≠ 0) : y⁻¹ < x⁻¹ ↔ x < y := by
  rw [← one_div, div_lt_iff hy, ← div_eq_inv_mul, lt_div_iff hx, one_mulₓ]

theorem inv_lt_inv {x y : ℝ≥0 } (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  (inv_lt_inv_iff hx (bot_le.trans_lt h).ne').2 h

end Inv

@[simp]
theorem abs_eq (x : ℝ≥0 ) : abs (x : ℝ) = x :=
  abs_of_nonneg x.property

section Csupr

open Set

variable {ι : Sort _} {f : ι → ℝ≥0 }

theorem le_to_nnreal_of_coe_le {x : ℝ≥0 } {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNnreal :=
  (le_to_nnreal_iff_coe_le <| x.2.trans h).2 h

theorem Sup_of_not_bdd_above {s : Set ℝ≥0 } (hs : ¬BddAbove s) : HasSupₓ.sup s = 0 := by
  rw [← bdd_above_coe] at hs
  rw [← Nnreal.coe_eq, coe_Sup]
  exact Sup_of_not_bdd_above hs

theorem supr_of_not_bdd_above (hf : ¬BddAbove (Range f)) : (⨆ i, f i) = 0 :=
  Sup_of_not_bdd_above hf

theorem infi_empty [IsEmpty ι] (f : ι → ℝ≥0 ) : (⨅ i, f i) = 0 := by
  rw [← Nnreal.coe_eq, coe_infi]
  exact Real.cinfi_empty _

@[simp]
theorem infi_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ≥0 )) = 0 := by
  rw [← Nnreal.coe_eq, coe_infi]
  exact Real.cinfi_const_zero

theorem infi_mul (f : ι → ℝ≥0 ) (a : ℝ≥0 ) : infi f * a = ⨅ i, f i * a := by
  rw [← Nnreal.coe_eq, Nnreal.coe_mul, coe_infi, coe_infi]
  exact Real.infi_mul_of_nonneg (Nnreal.coe_nonneg _) _

theorem mul_infi (f : ι → ℝ≥0 ) (a : ℝ≥0 ) : a * infi f = ⨅ i, a * f i := by
  simpa only [← mul_comm] using infi_mul f a

theorem mul_supr (f : ι → ℝ≥0 ) (a : ℝ≥0 ) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← Nnreal.coe_eq, Nnreal.coe_mul, Nnreal.coe_supr, Nnreal.coe_supr]
  exact Real.mul_supr_of_nonneg (Nnreal.coe_nonneg _) _

theorem supr_mul (f : ι → ℝ≥0 ) (a : ℝ≥0 ) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_supr]
  simp_rw [mul_comm]

theorem supr_div (f : ι → ℝ≥0 ) (a : ℝ≥0 ) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [← div_eq_mul_inv, ← supr_mul]

variable [Nonempty ι]

theorem le_mul_infi {a : ℝ≥0 } {g : ℝ≥0 } {h : ι → ℝ≥0 } (H : ∀ j, a ≤ g * h j) : a ≤ g * infi h := by
  rw [mul_infi]
  exact le_cinfi H

theorem mul_supr_le {a : ℝ≥0 } {g : ℝ≥0 } {h : ι → ℝ≥0 } (H : ∀ j, g * h j ≤ a) : g * supr h ≤ a := by
  rw [mul_supr]
  exact csupr_le H

theorem le_infi_mul {a : ℝ≥0 } {g : ι → ℝ≥0 } {h : ℝ≥0 } (H : ∀ i, a ≤ g i * h) : a ≤ infi g * h := by
  rw [infi_mul]
  exact le_cinfi H

theorem supr_mul_le {a : ℝ≥0 } {g : ι → ℝ≥0 } {h : ℝ≥0 } (H : ∀ i, g i * h ≤ a) : supr g * h ≤ a := by
  rw [supr_mul]
  exact csupr_le H

theorem le_infi_mul_infi {a : ℝ≥0 } {g h : ι → ℝ≥0 } (H : ∀ i j, a ≤ g i * h j) : a ≤ infi g * infi h :=
  le_infi_mul fun i => le_mul_infi <| H i

theorem supr_mul_supr_le {a : ℝ≥0 } {g h : ι → ℝ≥0 } (H : ∀ i j, g i * h j ≤ a) : supr g * supr h ≤ a :=
  supr_mul_le fun i => mul_supr_le <| H _

end Csupr

end Nnreal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0 }

theorem preimage_coe_nnreal_real (h : s.OrdConnected) : (coe ⁻¹' s : Set ℝ≥0 ).OrdConnected :=
  h.preimage_mono Nnreal.coe_mono

theorem image_coe_nnreal_real (h : t.OrdConnected) : (coe '' t : Set ℝ).OrdConnected :=
  ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩

theorem image_real_to_nnreal (h : s.OrdConnected) : (Real.toNnreal '' s).OrdConnected := by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  cases' le_totalₓ y 0 with hy₀ hy₀
  · rw [mem_Icc, Real.to_nnreal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (to_nnreal_of_nonpos hy₀).trans hz.2.symm⟩
    
  · lift y to ℝ≥0 using hy₀
    rw [to_nnreal_coe] at hz
    exact ⟨z, h.out hx hy ⟨to_nnreal_le_iff_le_coe.1 hz.1, hz.2⟩, to_nnreal_coe⟩
    

theorem preimage_real_to_nnreal (h : t.OrdConnected) : (Real.toNnreal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.to_nnreal_mono

end OrdConnected

end Set

namespace Real

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
noncomputable def nnabs : ℝ →*₀ ℝ≥0 where
  toFun := fun x => ⟨abs x, abs_nonneg x⟩
  map_zero' := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := fun x y => by
    ext
    simp [← abs_mul]

@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = abs x :=
  rfl

@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNnreal x := by
  ext
  simp [← coe_to_nnreal x h, ← abs_of_nonneg h]

theorem coe_to_nnreal_le (x : ℝ) : (toNnreal x : ℝ) ≤ abs x :=
  max_leₓ (le_abs_self _) (abs_nonneg _)

theorem cast_nat_abs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0 ) = nnabs n := by
  ext
  rw [Nnreal.coe_nat_cast, Int.cast_nat_abs, Real.coe_nnabs]

end Real

