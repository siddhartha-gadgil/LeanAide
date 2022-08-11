/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import Mathbin.Data.Real.Nnreal

/-!
# Extended non-negative reals

We define `ennreal = ℝ≥0∞ := with_top ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `measure_theory.measure`,
and of the extended distance `edist` in a `emetric_space`.
In this file we define some algebraic operations and a linear order on `ℝ≥0∞`
and prove basic properties of these operations, order, and conversions to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `with_top ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and `a *
    ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `has_coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ennreal.to_nnreal` sends `↑p` to `p` and `∞` to `0`;

  - `ennreal.to_real := coe ∘ ennreal.to_nnreal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ennreal.of_real := coe ∘ real.to_nnreal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ennreal.ne_top_equiv_nnreal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `can_lift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/


open Classical Set

open Classical BigOperators Nnreal

variable {α : Type _} {β : Type _}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
def Ennreal :=
  WithTop ℝ≥0 deriving Zero, AddCommMonoidWithOne, CanonicallyOrderedCommSemiring, CompleteLinearOrder, DenselyOrdered,
  Nontrivial, CanonicallyLinearOrderedAddMonoid, Sub, HasOrderedSub, LinearOrderedAddCommMonoidWithTop

-- mathport name: «exprℝ≥0∞»
localized [Ennreal] notation "ℝ≥0∞" => Ennreal

-- mathport name: «expr∞»
localized [Ennreal] notation "∞" => (⊤ : Ennreal)

namespace Ennreal

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0 }

-- TODO: why are the two covariant instances necessary? why aren't they inferred?
instance covariant_class_mul_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· * ·) (· ≤ ·) :=
  CanonicallyOrderedCommSemiring.to_covariant_mul_le

instance covariant_class_add_le : CovariantClass ℝ≥0∞ ℝ≥0∞ (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariant_class_left ℝ≥0∞

instance : Inhabited ℝ≥0∞ :=
  ⟨0⟩

instance : Coe ℝ≥0 ℝ≥0∞ :=
  ⟨Option.some⟩

instance : CanLift ℝ≥0∞ ℝ≥0 where
  coe := coe
  cond := fun r => r ≠ ∞
  prf := fun x hx => ⟨Option.getₓ <| Option.ne_none_iff_is_some.1 hx, Option.some_getₓ _⟩

@[simp]
theorem none_eq_top : (none : ℝ≥0∞) = ∞ :=
  rfl

@[simp]
theorem some_eq_coe (a : ℝ≥0 ) : (some a : ℝ≥0∞) = (↑a : ℝ≥0∞) :=
  rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def toNnreal : ℝ≥0∞ → ℝ≥0
  | some r => r
  | none => 0

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def toReal (a : ℝ≥0∞) : Real :=
  coe a.toNnreal

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected noncomputable def ofReal (r : Real) : ℝ≥0∞ :=
  coe (Real.toNnreal r)

@[simp, norm_cast]
theorem to_nnreal_coe : (r : ℝ≥0∞).toNnreal = r :=
  rfl

@[simp]
theorem coe_to_nnreal : ∀ {a : ℝ≥0∞}, a ≠ ∞ → ↑a.toNnreal = a
  | some r, h => rfl
  | none, h => (h rfl).elim

@[simp]
theorem of_real_to_real {a : ℝ≥0∞} (h : a ≠ ∞) : Ennreal.ofReal a.toReal = a := by
  simp [← Ennreal.toReal, ← Ennreal.ofReal, ← h]

@[simp]
theorem to_real_of_real {r : ℝ} (h : 0 ≤ r) : Ennreal.toReal (Ennreal.ofReal r) = r := by
  simp [← Ennreal.toReal, ← Ennreal.ofReal, ← Real.coe_to_nnreal _ h]

theorem to_real_of_real' {r : ℝ} : Ennreal.toReal (Ennreal.ofReal r) = max r 0 :=
  rfl

theorem coe_to_nnreal_le_self : ∀ {a : ℝ≥0∞}, ↑a.toNnreal ≤ a
  | some r => by
    rw [some_eq_coe, to_nnreal_coe] <;> exact le_rfl
  | none => le_top

theorem coe_nnreal_eq (r : ℝ≥0 ) : (r : ℝ≥0∞) = Ennreal.ofReal r := by
  rw [Ennreal.ofReal, Real.toNnreal]
  cases' r with r h
  congr
  dsimp'
  rw [max_eq_leftₓ h]

theorem of_real_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) : Ennreal.ofReal x = @coe ℝ≥0 ℝ≥0∞ _ (⟨x, h⟩ : ℝ≥0 ) := by
  rw [coe_nnreal_eq]
  rfl

@[simp]
theorem of_real_coe_nnreal : Ennreal.ofReal p = p :=
  (coe_nnreal_eq p).symm

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ≥0 ) = (0 : ℝ≥0∞) :=
  rfl

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ≥0 ) = (1 : ℝ≥0∞) :=
  rfl

@[simp]
theorem to_real_nonneg {a : ℝ≥0∞} : 0 ≤ a.toReal := by
  simp [← Ennreal.toReal]

@[simp]
theorem top_to_nnreal : ∞.toNnreal = 0 :=
  rfl

@[simp]
theorem top_to_real : ∞.toReal = 0 :=
  rfl

@[simp]
theorem one_to_real : (1 : ℝ≥0∞).toReal = 1 :=
  rfl

@[simp]
theorem one_to_nnreal : (1 : ℝ≥0∞).toNnreal = 1 :=
  rfl

@[simp]
theorem coe_to_real (r : ℝ≥0 ) : (r : ℝ≥0∞).toReal = r :=
  rfl

@[simp]
theorem zero_to_nnreal : (0 : ℝ≥0∞).toNnreal = 0 :=
  rfl

@[simp]
theorem zero_to_real : (0 : ℝ≥0∞).toReal = 0 :=
  rfl

@[simp]
theorem of_real_zero : Ennreal.ofReal (0 : ℝ) = 0 := by
  simp [← Ennreal.ofReal] <;> rfl

@[simp]
theorem of_real_one : Ennreal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by
  simp [← Ennreal.ofReal]

theorem of_real_to_real_le {a : ℝ≥0∞} : Ennreal.ofReal a.toReal ≤ a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eqₓ (of_real_to_real ha)

theorem forall_ennreal {p : ℝ≥0∞ → Prop} : (∀ a, p a) ↔ (∀ r : ℝ≥0 , p r) ∧ p ∞ :=
  ⟨fun h => ⟨fun r => h _, h _⟩, fun ⟨h₁, h₂⟩ a =>
    match a with
    | some r => h₁ _
    | none => h₂⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ≠ » «expr∞»())
theorem forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ (a) (_ : a ≠ ∞), p a) ↔ ∀ r : ℝ≥0 , p r :=
  Option.ball_ne_none

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ≠ » «expr∞»())
theorem exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ (a : _)(_ : a ≠ ∞), p a) ↔ ∃ r : ℝ≥0 , p r :=
  Option.bex_ne_none

theorem to_nnreal_eq_zero_iff (x : ℝ≥0∞) : x.toNnreal = 0 ↔ x = 0 ∨ x = ∞ :=
  ⟨by
    cases x
    · simp [← none_eq_top]
      
    · rintro (rfl : x = 0)
      exact Or.inl rfl
      ,
    by
    rintro (h | h) <;> simp [← h]⟩

theorem to_real_eq_zero_iff (x : ℝ≥0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [← Ennreal.toReal, ← to_nnreal_eq_zero_iff]

@[simp]
theorem coe_ne_top : (r : ℝ≥0∞) ≠ ∞ :=
  WithTop.coe_ne_top

@[simp]
theorem top_ne_coe : ∞ ≠ (r : ℝ≥0∞) :=
  WithTop.top_ne_coe

@[simp]
theorem of_real_ne_top {r : ℝ} : Ennreal.ofReal r ≠ ∞ := by
  simp [← Ennreal.ofReal]

@[simp]
theorem of_real_lt_top {r : ℝ} : Ennreal.ofReal r < ∞ :=
  lt_top_iff_ne_top.2 of_real_ne_top

@[simp]
theorem top_ne_of_real {r : ℝ} : ∞ ≠ Ennreal.ofReal r := by
  simp [← Ennreal.ofReal]

@[simp]
theorem zero_ne_top : 0 ≠ ∞ :=
  coe_ne_top

@[simp]
theorem top_ne_zero : ∞ ≠ 0 :=
  top_ne_coe

@[simp]
theorem one_ne_top : 1 ≠ ∞ :=
  coe_ne_top

@[simp]
theorem top_ne_one : ∞ ≠ 1 :=
  top_ne_coe

@[simp, norm_cast]
theorem coe_eq_coe : (↑r : ℝ≥0∞) = ↑q ↔ r = q :=
  WithTop.coe_eq_coe

@[simp, norm_cast]
theorem coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q :=
  WithTop.coe_le_coe

@[simp, norm_cast]
theorem coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q :=
  WithTop.coe_lt_coe

theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ≥0∞) := fun _ _ => coe_le_coe.2

@[simp, norm_cast]
theorem coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 :=
  coe_eq_coe

@[simp, norm_cast]
theorem one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_nonneg : 0 ≤ (↑r : ℝ≥0∞) ↔ 0 ≤ r :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_pos : 0 < (↑r : ℝ≥0∞) ↔ 0 < r :=
  coe_lt_coe

theorem coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 :=
  not_congr coe_eq_coe

@[simp, norm_cast]
theorem coe_add : ↑(r + p) = (r + p : ℝ≥0∞) :=
  WithTop.coe_add

@[simp, norm_cast]
theorem coe_mul : ↑(r * p) = (r * p : ℝ≥0∞) :=
  WithTop.coe_mul

@[simp, norm_cast]
theorem coe_bit0 : (↑(bit0 r) : ℝ≥0∞) = bit0 r :=
  coe_add

@[simp, norm_cast]
theorem coe_bit1 : (↑(bit1 r) : ℝ≥0∞) = bit1 r := by
  simp [← bit1]

theorem coe_two : ((2 : ℝ≥0 ) : ℝ≥0∞) = 2 := by
  norm_cast

protected theorem zero_lt_one : 0 < (1 : ℝ≥0∞) :=
  CanonicallyOrderedCommSemiring.zero_lt_one

@[simp]
theorem one_lt_two : (1 : ℝ≥0∞) < 2 :=
  coe_one ▸
    coe_two ▸ by
      exact_mod_cast @one_lt_two ℕ _ _

theorem one_le_two : (1 : ℝ≥0∞) ≤ 2 :=
  one_lt_two.le

@[simp]
theorem zero_lt_two : (0 : ℝ≥0∞) < 2 :=
  lt_transₓ Ennreal.zero_lt_one one_lt_two

theorem two_ne_zero : (2 : ℝ≥0∞) ≠ 0 :=
  (ne_of_ltₓ zero_lt_two).symm

theorem two_ne_top : (2 : ℝ≥0∞) ≠ ∞ :=
  coe_two ▸ coe_ne_top

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_one_ennreal : Fact ((1 : ℝ≥0∞) ≤ 1) :=
  ⟨le_rfl⟩

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_two_ennreal : Fact ((1 : ℝ≥0∞) ≤ 2) :=
  ⟨Ennreal.coe_le_coe.2
      (show (1 : ℝ≥0 ) ≤ 2 by
        norm_num)⟩

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞) :=
  ⟨le_top⟩

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def neTopEquivNnreal : { a | a ≠ ∞ } ≃ ℝ≥0 where
  toFun := fun x => Ennreal.toNnreal x
  invFun := fun x => ⟨x, coe_ne_top⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.eq <| coe_to_nnreal hx
  right_inv := fun x => to_nnreal_coe

theorem cinfi_ne_top [HasInfₓ α] (f : ℝ≥0∞ → α) : (⨅ x : { x // x ≠ ∞ }, f x) = ⨅ x : ℝ≥0 , f x :=
  Eq.symm <| (neTopEquivNnreal.symm.Surjective.infi_congr _) fun x => rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » «expr∞»())
theorem infi_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) : (⨅ (x) (_ : x ≠ ∞), f x) = ⨅ x : ℝ≥0 , f x := by
  rw [infi_subtype', cinfi_ne_top]

theorem csupr_ne_top [HasSupₓ α] (f : ℝ≥0∞ → α) : (⨆ x : { x // x ≠ ∞ }, f x) = ⨆ x : ℝ≥0 , f x :=
  @cinfi_ne_top αᵒᵈ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » «expr∞»())
theorem supr_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) : (⨆ (x) (_ : x ≠ ∞), f x) = ⨆ x : ℝ≥0 , f x :=
  @infi_ne_top αᵒᵈ _ _

theorem infi_ennreal {α : Type _} [CompleteLattice α] {f : ℝ≥0∞ → α} : (⨅ n, f n) = (⨅ n : ℝ≥0 , f n)⊓f ∞ :=
  le_antisymmₓ (le_inf (le_infi fun i => infi_le _ _) (infi_le _ _))
    (le_infi <| forall_ennreal.2 ⟨fun r => inf_le_of_left_le <| infi_le _ _, inf_le_right⟩)

theorem supr_ennreal {α : Type _} [CompleteLattice α] {f : ℝ≥0∞ → α} : (⨆ n, f n) = (⨆ n : ℝ≥0 , f n)⊔f ∞ :=
  @infi_ennreal αᵒᵈ _ _

@[simp]
theorem add_top : a + ∞ = ∞ :=
  add_top _

@[simp]
theorem top_add : ∞ + a = ∞ :=
  top_add _

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `ring_hom`. -/
def ofNnrealHom : ℝ≥0 →+* ℝ≥0∞ :=
  ⟨coe, coe_one, fun _ _ => coe_mul, coe_zero, fun _ _ => coe_add⟩

@[simp]
theorem coe_of_nnreal_hom : ⇑of_nnreal_hom = coe :=
  rfl

section Actions

/-- A `mul_action` over `ℝ≥0∞` restricts to a `mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [MulAction ℝ≥0∞ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M ofNnrealHom.toMonoidHom

theorem smul_def {M : Type _} [MulAction ℝ≥0∞ M] (c : ℝ≥0 ) (x : M) : c • x = (c : ℝ≥0∞) • x :=
  rfl

instance {M N : Type _} [MulAction ℝ≥0∞ M] [MulAction ℝ≥0∞ N] [HasSmul M N] [IsScalarTower ℝ≥0∞ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc := fun r => (smul_assoc (r : ℝ≥0∞) : _)

instance smul_comm_class_left {M N : Type _} [MulAction ℝ≥0∞ N] [HasSmul M N] [SmulCommClass ℝ≥0∞ M N] :
    SmulCommClass ℝ≥0 M N where smul_comm := fun r => (smul_comm (r : ℝ≥0∞) : _)

instance smul_comm_class_right {M N : Type _} [MulAction ℝ≥0∞ N] [HasSmul M N] [SmulCommClass M ℝ≥0∞ N] :
    SmulCommClass M ℝ≥0 N where smul_comm := fun m r => (smul_comm m (r : ℝ≥0∞) : _)

/-- A `distrib_mul_action` over `ℝ≥0∞` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [AddMonoidₓ M] [DistribMulAction ℝ≥0∞ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M ofNnrealHom.toMonoidHom

/-- A `module` over `ℝ≥0∞` restricts to a `module` over `ℝ≥0`. -/
noncomputable instance {M : Type _} [AddCommMonoidₓ M] [Module ℝ≥0∞ M] : Module ℝ≥0 M :=
  Module.compHom M ofNnrealHom

/-- An `algebra` over `ℝ≥0∞` restricts to an `algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type _} [Semiringₓ A] [Algebra ℝ≥0∞ A] : Algebra ℝ≥0 A where
  smul := (· • ·)
  commutes' := fun r x => by
    simp [← Algebra.commutes]
  smul_def' := fun r x => by
    simp [Algebra.smul_def (r : ℝ≥0∞) x, ← smul_def]
  toRingHom := (algebraMap ℝ≥0∞ A).comp (ofNnrealHom : ℝ≥0 →+* ℝ≥0∞)

-- verify that the above produces instances we might care about
noncomputable example : Algebra ℝ≥0 ℝ≥0∞ :=
  inferInstance

noncomputable example : DistribMulAction ℝ≥0 ˣ ℝ≥0∞ :=
  inferInstance

theorem coe_smul {R} (r : R) (s : ℝ≥0 ) [HasSmul R ℝ≥0 ] [HasSmul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0 ]
    [IsScalarTower R ℝ≥0 ℝ≥0∞] : (↑(r • s) : ℝ≥0∞) = r • ↑s := by
  rw [← smul_one_smul ℝ≥0 r (s : ℝ≥0∞), smul_def, smul_eq_mul, ← Ennreal.coe_mul, smul_mul_assoc, one_mulₓ]

end Actions

@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0 ) (a : α) :
    ((s.indicator f a : ℝ≥0 ) : ℝ≥0∞) = s.indicator (fun x => f x) a :=
  (ofNnrealHom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _

@[simp, norm_cast]
theorem coe_pow (n : ℕ) : (↑(r ^ n) : ℝ≥0∞) = r ^ n :=
  ofNnrealHom.map_pow r n

@[simp]
theorem add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ :=
  WithTop.add_eq_top

@[simp]
theorem add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ :=
  WithTop.add_lt_top

theorem to_nnreal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) : (r₁ + r₂).toNnreal = r₁.toNnreal + r₂.toNnreal := by
  lift r₁ to ℝ≥0 using h₁
  lift r₂ to ℝ≥0 using h₂
  rfl

theorem not_lt_top {x : ℝ≥0∞} : ¬x < ∞ ↔ x = ∞ := by
  rw [lt_top_iff_ne_top, not_not]

theorem add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ := by
  simpa only [← lt_top_iff_ne_top] using add_lt_top

theorem mul_top : a * ∞ = if a = 0 then 0 else ∞ := by
  split_ifs
  · simp [← h]
    
  · exact WithTop.mul_top h
    

theorem top_mul : ∞ * a = if a = 0 then 0 else ∞ := by
  split_ifs
  · simp [← h]
    
  · exact WithTop.top_mul h
    

@[simp]
theorem top_mul_top : ∞ * ∞ = ∞ :=
  WithTop.top_mul_top

theorem top_pow {n : ℕ} (h : 0 < n) : ∞ ^ n = ∞ :=
  Nat.le_induction (pow_oneₓ _)
    (fun m hm hm' => by
      rw [pow_succₓ, hm', top_mul_top])
    _ (Nat.succ_le_of_ltₓ h)

theorem mul_eq_top : a * b = ∞ ↔ a ≠ 0 ∧ b = ∞ ∨ a = ∞ ∧ b ≠ 0 :=
  WithTop.mul_eq_top_iff

theorem mul_lt_top : a ≠ ∞ → b ≠ ∞ → a * b < ∞ :=
  WithTop.mul_lt_top

theorem mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ := by
  simpa only [← lt_top_iff_ne_top] using mul_lt_top

theorem lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
  lt_top_iff_ne_top.2 fun ha => h <| mul_eq_top.2 (Or.inr ⟨ha, hb⟩)

theorem lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
  lt_top_of_mul_ne_top_left
    (by
      rwa [mul_comm])
    ha

theorem mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ a < ∞ ∧ b < ∞ ∨ a = 0 ∨ b = 0 := by
  constructor
  · intro h
    rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right]
    intro hb ha
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩
    
  · rintro (⟨ha, hb⟩ | rfl | rfl) <;> [exact mul_lt_top ha.ne hb.ne, simp , simp ]
    

theorem mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ := by
  rw [Ennreal.mul_lt_top_iff, and_selfₓ, or_selfₓ, or_iff_left_iff_imp]
  rintro rfl
  norm_num

theorem mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b :=
  CanonicallyOrderedCommSemiring.mul_pos

theorem mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
  mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

@[simp]
theorem pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 := by
  induction' n with n ihn
  · simp
    
  rw [pow_succₓ, mul_eq_top, ihn]
  fconstructor
  · rintro (⟨-, rfl, h0⟩ | ⟨rfl, h0⟩) <;> exact ⟨rfl, n.succ_ne_zero⟩
    
  · rintro ⟨rfl, -⟩
    exact Or.inr ⟨rfl, pow_ne_zero n top_ne_zero⟩
    

theorem pow_eq_top (n : ℕ) (h : a ^ n = ∞) : a = ∞ :=
  (pow_eq_top_iff.1 h).1

theorem pow_ne_top (h : a ≠ ∞) {n : ℕ} : a ^ n ≠ ∞ :=
  mt (pow_eq_top n) h

theorem pow_lt_top : a < ∞ → ∀ n : ℕ, a ^ n < ∞ := by
  simpa only [← lt_top_iff_ne_top] using pow_ne_top

@[simp, norm_cast]
theorem coe_finset_sum {s : Finset α} {f : α → ℝ≥0 } : ↑(∑ a in s, f a) = (∑ a in s, f a : ℝ≥0∞) :=
  ofNnrealHom.map_sum f s

@[simp, norm_cast]
theorem coe_finset_prod {s : Finset α} {f : α → ℝ≥0 } : ↑(∏ a in s, f a) = (∏ a in s, f a : ℝ≥0∞) :=
  ofNnrealHom.map_prod f s

section Order

@[simp]
theorem bot_eq_zero : (⊥ : ℝ≥0∞) = 0 :=
  rfl

@[simp]
theorem coe_lt_top : coe r < ∞ :=
  WithTop.coe_lt_top r

@[simp]
theorem not_top_le_coe : ¬∞ ≤ ↑r :=
  WithTop.not_top_le_coe r

@[simp, norm_cast]
theorem one_le_coe_iff : (1 : ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_le_one_iff : ↑r ≤ (1 : ℝ≥0∞) ↔ r ≤ 1 :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 :=
  coe_lt_coe

@[simp, norm_cast]
theorem one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p :=
  coe_lt_coe

@[simp, norm_cast]
theorem coe_nat (n : ℕ) : ((n : ℝ≥0 ) : ℝ≥0∞) = n :=
  WithTop.coe_nat n

@[simp]
theorem of_real_coe_nat (n : ℕ) : Ennreal.ofReal n = n := by
  simp [← Ennreal.ofReal]

@[simp]
theorem nat_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ :=
  WithTop.nat_ne_top n

@[simp]
theorem top_ne_nat (n : ℕ) : ∞ ≠ n :=
  WithTop.top_ne_nat n

@[simp]
theorem one_lt_top : 1 < ∞ :=
  coe_lt_top

@[simp, norm_cast]
theorem to_nnreal_nat (n : ℕ) : (n : ℝ≥0∞).toNnreal = n := by
  conv_lhs => rw [← Ennreal.coe_nat n, Ennreal.to_nnreal_coe]

@[simp, norm_cast]
theorem to_real_nat (n : ℕ) : (n : ℝ≥0∞).toReal = n := by
  conv_lhs => rw [← Ennreal.of_real_coe_nat n, Ennreal.to_real_of_real (Nat.cast_nonneg _)]

theorem le_coe_iff : a ≤ ↑r ↔ ∃ p : ℝ≥0 , a = p ∧ p ≤ r :=
  WithTop.le_coe_iff

theorem coe_le_iff : ↑r ≤ a ↔ ∀ p : ℝ≥0 , a = p → r ≤ p :=
  WithTop.coe_le_iff

theorem lt_iff_exists_coe : a < b ↔ ∃ p : ℝ≥0 , a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe

theorem to_real_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0 } (h : a ≤ b) : a.toReal ≤ b :=
  show ↑a.toNnreal ≤ ↑b by
    have : ↑a.to_nnreal = a := Ennreal.coe_to_nnreal (lt_of_le_of_ltₓ h coe_lt_top).Ne
    rw [← this] at h
    exact_mod_cast h

@[simp, norm_cast]
theorem coe_finset_sup {s : Finset α} {f : α → ℝ≥0 } : ↑(s.sup f) = s.sup fun x => (f x : ℝ≥0∞) :=
  Finset.comp_sup_eq_sup_comp_of_is_total _ coe_mono rfl

theorem pow_le_pow {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m := by
  cases a
  · cases m
    · rw [eq_bot_iff.mpr h]
      exact le_rfl
      
    · rw [none_eq_top, top_pow (Nat.succ_posₓ m)]
      exact le_top
      
    
  · rw [some_eq_coe, ← coe_pow, ← coe_pow, coe_le_coe]
    exact
      pow_le_pow
        (by
          simpa using ha)
        h
    

theorem one_le_pow_of_one_le (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n := by
  simpa using pow_le_pow ha (zero_le n)

@[simp]
theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [← nonpos_iff_eq_zero.symm, ← max_le_iff]

@[simp]
theorem max_zero_left : max 0 a = a :=
  max_eq_rightₓ (zero_le a)

@[simp]
theorem max_zero_right : max a 0 = a :=
  max_eq_leftₓ (zero_le a)

@[simp]
theorem sup_eq_max : a⊔b = max a b :=
  rfl

protected theorem pow_pos : 0 < a → ∀ n : ℕ, 0 < a ^ n :=
  CanonicallyOrderedCommSemiring.pow_pos

protected theorem pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a ^ n ≠ 0 := by
  simpa only [← pos_iff_ne_zero] using Ennreal.pow_pos

@[simp]
theorem not_lt_zero : ¬a < 0 := by
  simp

protected theorem le_of_add_le_add_left : a ≠ ∞ → a + b ≤ a + c → b ≤ c :=
  WithTop.le_of_add_le_add_left

protected theorem le_of_add_le_add_right : a ≠ ∞ → b + a ≤ c + a → b ≤ c :=
  WithTop.le_of_add_le_add_right

protected theorem add_lt_add_left : a ≠ ∞ → b < c → a + b < a + c :=
  WithTop.add_lt_add_left

protected theorem add_lt_add_right : a ≠ ∞ → b < c → b + a < c + a :=
  WithTop.add_lt_add_right

protected theorem add_le_add_iff_left : a ≠ ∞ → (a + b ≤ a + c ↔ b ≤ c) :=
  WithTop.add_le_add_iff_left

protected theorem add_le_add_iff_right : a ≠ ∞ → (b + a ≤ c + a ↔ b ≤ c) :=
  WithTop.add_le_add_iff_right

protected theorem add_lt_add_iff_left : a ≠ ∞ → (a + b < a + c ↔ b < c) :=
  WithTop.add_lt_add_iff_left

protected theorem add_lt_add_iff_right : a ≠ ∞ → (b + a < c + a ↔ b < c) :=
  WithTop.add_lt_add_iff_right

protected theorem add_lt_add_of_le_of_lt : a ≠ ∞ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

protected theorem add_lt_add_of_lt_of_le : c ≠ ∞ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

instance contravariant_class_add_lt : ContravariantClass ℝ≥0∞ ℝ≥0∞ (· + ·) (· < ·) :=
  WithTop.contravariant_class_add_lt

theorem lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b := by
  rwa [← pos_iff_ne_zero, ← Ennreal.add_lt_add_iff_left ha, add_zeroₓ] at hb

theorem le_of_forall_pos_le_add : ∀ {a b : ℝ≥0∞}, (∀ ε : ℝ≥0 , 0 < ε → b < ∞ → a ≤ b + ε) → a ≤ b
  | a, none, h => le_top
  | none, some a, h => by
    have : ∞ ≤ ↑a + ↑(1 : ℝ≥0 ) := h 1 zero_lt_one coe_lt_top
    rw [← coe_add] at this <;> exact (not_top_le_coe this).elim
  | some a, some b, h => by
    simp only [← none_eq_top, ← some_eq_coe, ← coe_add.symm, ← coe_le_coe, ← coe_lt_top, ← true_implies_iff] at * <;>
      exact Nnreal.le_of_forall_pos_le_add h

theorem lt_iff_exists_rat_btwn : a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNnreal q ∧ (Real.toNnreal q : ℝ≥0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases(Nnreal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_transₓ (coe_lt_coe.2 qr) cb⟩, fun ⟨q, q0, qa, qb⟩ => lt_transₓ qa qb⟩

theorem lt_iff_exists_real_btwn : a < b ↔ ∃ r : ℝ, 0 ≤ r ∧ a < Ennreal.ofReal r ∧ (Ennreal.ofReal r : ℝ≥0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := Ennreal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨q, q0, qa, qb⟩ => lt_transₓ qa qb⟩

theorem lt_iff_exists_nnreal_btwn : a < b ↔ ∃ r : ℝ≥0 , a < r ∧ (r : ℝ≥0∞) < b :=
  WithTop.lt_iff_exists_coe_btwn

theorem lt_iff_exists_add_pos_lt : a < b ↔ ∃ r : ℝ≥0 , 0 < r ∧ a + r < b := by
  refine' ⟨fun hab => _, fun ⟨r, rpos, hr⟩ => lt_of_le_of_ltₓ le_self_add hr⟩
  cases a
  · simpa using hab
    
  rcases lt_iff_exists_real_btwn.1 hab with ⟨c, c_nonneg, ac, cb⟩
  let d : ℝ≥0 := ⟨c, c_nonneg⟩
  have ad : a < d := by
    rw [of_real_eq_coe_nnreal c_nonneg] at ac
    exact coe_lt_coe.1 ac
  refine' ⟨d - a, tsub_pos_iff_lt.2 ad, _⟩
  rw [some_eq_coe, ← coe_add]
  convert cb
  have : Real.toNnreal c = d := by
    rw [← Nnreal.coe_eq, Real.coe_to_nnreal _ c_nonneg]
    rfl
  rw [add_commₓ, this]
  exact tsub_add_cancel_of_le ad.le

theorem coe_nat_lt_coe {n : ℕ} : (n : ℝ≥0∞) < r ↔ ↑n < r :=
  Ennreal.coe_nat n ▸ coe_lt_coe

theorem coe_lt_coe_nat {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n :=
  Ennreal.coe_nat n ▸ coe_lt_coe

@[simp, norm_cast]
theorem coe_nat_lt_coe_nat {m n : ℕ} : (m : ℝ≥0∞) < n ↔ m < n :=
  Ennreal.coe_nat n ▸ coe_nat_lt_coe.trans Nat.cast_lt

theorem coe_nat_ne_top {n : ℕ} : (n : ℝ≥0∞) ≠ ∞ :=
  Ennreal.coe_nat n ▸ coe_ne_top

theorem coe_nat_mono : StrictMono (coe : ℕ → ℝ≥0∞) := fun _ _ => coe_nat_lt_coe_nat.2

@[simp, norm_cast]
theorem coe_nat_le_coe_nat {m n : ℕ} : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
  coe_nat_mono.le_iff_le

instance : CharZero ℝ≥0∞ :=
  ⟨coe_nat_mono.Injective⟩

protected theorem exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
  lift r to ℝ≥0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_coe_nat.2 hn⟩

@[simp]
theorem Union_Iio_coe_nat : (⋃ n : ℕ, Iio (n : ℝ≥0∞)) = {∞}ᶜ := by
  ext x
  rw [mem_Union]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, Ennreal.exists_nat_gt⟩

@[simp]
theorem Union_Iic_coe_nat : (⋃ n : ℕ, Iic (n : ℝ≥0∞)) = {∞}ᶜ :=
  Subset.antisymm (Union_subset fun n x hx => ne_top_of_le_ne_top coe_nat_ne_top hx) <|
    Union_Iio_coe_nat ▸ Union_mono fun n => Iio_subset_Iic_self

@[simp]
theorem Union_Ioc_coe_nat : (⋃ n : ℕ, Ioc a n) = Ioi a \ {∞} := by
  simp only [Ioi_inter_Iic, inter_Union, ← Union_Iic_coe_nat, ← diff_eq]

@[simp]
theorem Union_Ioo_coe_nat : (⋃ n : ℕ, Ioo a n) = Ioi a \ {∞} := by
  simp only [Ioi_inter_Iio, inter_Union, ← Union_Iio_coe_nat, ← diff_eq]

@[simp]
theorem Union_Icc_coe_nat : (⋃ n : ℕ, Icc a n) = Ici a \ {∞} := by
  simp only [Ici_inter_Iic, inter_Union, ← Union_Iic_coe_nat, ← diff_eq]

@[simp]
theorem Union_Ico_coe_nat : (⋃ n : ℕ, Ico a n) = Ici a \ {∞} := by
  simp only [Ici_inter_Iio, inter_Union, ← Union_Iio_coe_nat, ← diff_eq]

@[simp]
theorem Inter_Ici_coe_nat : (⋂ n : ℕ, Ici (n : ℝ≥0∞)) = {∞} := by
  simp only [compl_Iio, compl_Union, ← Union_Iio_coe_nat, ← compl_compl]

@[simp]
theorem Inter_Ioi_coe_nat : (⋂ n : ℕ, Ioi (n : ℝ≥0∞)) = {∞} := by
  simp only [compl_Iic, compl_Union, ← Union_Iic_coe_nat, ← compl_compl]

theorem add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d := by
  lift a to ℝ≥0 using ne_top_of_lt ac
  lift b to ℝ≥0 using ne_top_of_lt bd
  cases c
  · simp
    
  cases d
  · simp
    
  simp only [coe_add, ← some_eq_coe, ← coe_lt_coe] at *
  exact add_lt_add ac bd

@[norm_cast]
theorem coe_min : ((min r p : ℝ≥0 ) : ℝ≥0∞) = min r p :=
  coe_mono.map_min

@[norm_cast]
theorem coe_max : ((max r p : ℝ≥0 ) : ℝ≥0∞) = max r p :=
  coe_mono.map_max

theorem le_of_top_imp_top_of_to_nnreal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
    (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.toNnreal ≤ b.toNnreal) : a ≤ b := by
  by_cases' ha : a = ⊤
  · rw [h ha]
    exact le_top
    
  by_cases' hb : b = ⊤
  · rw [hb]
    exact le_top
    
  rw [← coe_to_nnreal hb, ← coe_to_nnreal ha, coe_le_coe]
  exact h_nnreal ha hb

end Order

section CompleteLattice

theorem coe_Sup {s : Set ℝ≥0 } : BddAbove s → (↑(sup s) : ℝ≥0∞) = ⨆ a ∈ s, ↑a :=
  WithTop.coe_Sup

theorem coe_Inf {s : Set ℝ≥0 } : s.Nonempty → (↑(inf s) : ℝ≥0∞) = ⨅ a ∈ s, ↑a :=
  WithTop.coe_Inf

@[simp]
theorem top_mem_upper_bounds {s : Set ℝ≥0∞} : ∞ ∈ UpperBounds s := fun x hx => le_top

theorem coe_mem_upper_bounds {s : Set ℝ≥0 } : ↑r ∈ UpperBounds ((coe : ℝ≥0 → ℝ≥0∞) '' s) ↔ r ∈ UpperBounds s := by
  simp (config := { contextual := true })[← UpperBounds, ← ball_image_iff, -mem_image, *]

end CompleteLattice

section Mul

@[mono]
theorem mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d :=
  mul_le_mul'

@[mono]
theorem mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d := by
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩
  lift a to ℝ≥0 using ne_top_of_lt aa'
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩
  lift b to ℝ≥0 using ne_top_of_lt bb'
  norm_cast  at *
  calc ↑(a * b) < ↑(a' * b') :=
      coe_lt_coe.2 (mul_lt_mul' aa'.le bb' (zero_le _) ((zero_le a).trans_lt aa'))_ = ↑a' * ↑b' := coe_mul _ ≤ c * d :=
      mul_le_mul a'c.le b'd.le

theorem mul_left_mono : Monotone ((· * ·) a) := fun b c => mul_le_mul le_rfl

theorem mul_right_mono : Monotone fun x => x * a := fun b c h => mul_le_mul h le_rfl

theorem pow_strict_mono {n : ℕ} (hn : n ≠ 0) : StrictMono fun x : ℝ≥0∞ => x ^ n := by
  intro x y hxy
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  induction' n with n IH
  · simp only [← hxy, ← pow_oneₓ]
    
  · simp only [← pow_succₓ _ n.succ, ← mul_lt_mul hxy (IH (Nat.succ_posₓ _).ne')]
    

theorem max_mul : max a b * c = max (a * c) (b * c) :=
  mul_right_mono.map_max

theorem mul_max : a * max b c = max (a * b) (a * c) :=
  mul_left_mono.map_max

theorem mul_eq_mul_left : a ≠ 0 → a ≠ ∞ → (a * b = a * c ↔ b = c) := by
  cases a <;>
    cases b <;>
      cases c <;>
        simp (config := { contextual := true })[← none_eq_top, ← some_eq_coe, ← mul_top, ← top_mul, -coe_mul, ←
          coe_mul.symm, ← Nnreal.mul_eq_mul_left]

theorem mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left

theorem mul_le_mul_left : a ≠ 0 → a ≠ ∞ → (a * b ≤ a * c ↔ b ≤ c) := by
  cases a <;>
    cases b <;>
      cases c <;>
        simp (config := { contextual := true })[← none_eq_top, ← some_eq_coe, ← mul_top, ← top_mul, -coe_mul, ←
          coe_mul.symm]
  intro h
  exact mul_le_mul_left (pos_iff_ne_zero.2 h)

theorem mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

theorem mul_lt_mul_left : a ≠ 0 → a ≠ ∞ → (a * b < a * c ↔ b < c) := fun h0 ht => by
  simp only [← mul_le_mul_left h0 ht, ← lt_iff_le_not_leₓ]

theorem mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
  mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

end Mul

section Cancel

/-- An element `a` is `add_le_cancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
theorem add_le_cancellable_iff_ne {a : ℝ≥0∞} : AddLeCancellable a ↔ a ≠ ∞ := by
  constructor
  · rintro h rfl
    refine' ennreal.zero_lt_one.not_le (h _)
    simp
    
  · rintro h b c hbc
    apply Ennreal.le_of_add_le_add_left h hbc
    

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : AddLeCancellable a :=
  add_le_cancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : AddLeCancellable a :=
  cancel_of_ne h.Ne

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : AddLeCancellable a :=
  cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
theorem cancel_coe {a : ℝ≥0 } : AddLeCancellable (a : ℝ≥0∞) :=
  cancel_of_ne coe_ne_top

theorem add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
  (cancel_of_ne h).inj

theorem add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
  (cancel_of_ne h).inj_left

end Cancel

section Sub

theorem sub_eq_Inf {a b : ℝ≥0∞} : a - b = inf { d | a ≤ d + b } :=
  le_antisymmₓ (le_Inf fun c => tsub_le_iff_right.mpr) <| Inf_le le_tsub_add

/-- This is a special case of `with_top.coe_sub` in the `ennreal` namespace -/
theorem coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p :=
  WithTop.coe_sub

/-- This is a special case of `with_top.top_sub_coe` in the `ennreal` namespace -/
theorem top_sub_coe : ∞ - ↑r = ∞ :=
  WithTop.top_sub_coe

/-- This is a special case of `with_top.sub_top` in the `ennreal` namespace -/
theorem sub_top : a - ∞ = 0 :=
  WithTop.sub_top

theorem sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ := by
  cases a <;> cases b <;> simp [WithTop.coe_sub]

theorem sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ :=
  mt sub_eq_top_iff.mp <| mt And.left ha

protected theorem sub_eq_of_eq_add (hb : b ≠ ∞) : a = c + b → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add

protected theorem eq_sub_of_add_eq (hc : c ≠ ∞) : a + c = b → a = b - c :=
  (cancel_of_ne hc).eq_tsub_of_add_eq

protected theorem sub_eq_of_eq_add_rev (hb : b ≠ ∞) : a = b + c → a - b = c :=
  (cancel_of_ne hb).tsub_eq_of_eq_add_rev

theorem sub_eq_of_add_eq (hb : b ≠ ∞) (hc : a + b = c) : c - b = a :=
  Ennreal.sub_eq_of_eq_add hb hc.symm

@[simp]
protected theorem add_sub_cancel_left (ha : a ≠ ∞) : a + b - a = b :=
  (cancel_of_ne ha).add_tsub_cancel_left

@[simp]
protected theorem add_sub_cancel_right (hb : b ≠ ∞) : a + b - b = a :=
  (cancel_of_ne hb).add_tsub_cancel_right

protected theorem lt_add_of_sub_lt_left (h : a ≠ ∞ ∨ b ≠ ∞) : a - b < c → a < b + c := by
  obtain rfl | hb := eq_or_ne b ∞
  · rw [top_add, lt_top_iff_ne_top]
    exact fun _ => h.resolve_right (not_not.2 rfl)
    
  · exact (cancel_of_ne hb).lt_add_of_tsub_lt_left
    

protected theorem lt_add_of_sub_lt_right (h : a ≠ ∞ ∨ c ≠ ∞) : a - c < b → a < b + c :=
  add_commₓ c b ▸ Ennreal.lt_add_of_sub_lt_left h

theorem le_sub_of_add_le_left (ha : a ≠ ∞) : a + b ≤ c → b ≤ c - a :=
  (cancel_of_ne ha).le_tsub_of_add_le_left

theorem le_sub_of_add_le_right (hb : b ≠ ∞) : a + b ≤ c → a ≤ c - b :=
  (cancel_of_ne hb).le_tsub_of_add_le_right

protected theorem sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
  ((cancel_of_lt' <| hac.trans_lt h).tsub_lt_iff_right hac).mpr h

protected theorem sub_lt_iff_lt_right (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
  (cancel_of_ne hb).tsub_lt_iff_right hab

protected theorem sub_lt_self (ha : a ≠ ∞) (ha₀ : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
  (cancel_of_ne ha).tsub_lt_self (pos_iff_ne_zero.2 ha₀) (pos_iff_ne_zero.2 hb)

protected theorem sub_lt_self_iff (ha : a ≠ ∞) : a - b < a ↔ 0 < a ∧ 0 < b :=
  (cancel_of_ne ha).tsub_lt_self_iff

theorem sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
  Ennreal.sub_lt_of_lt_add h₂ (add_commₓ c b ▸ Ennreal.lt_add_of_sub_lt_right h₃ h₁)

theorem sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
  (cancel_of_ne <| sub_ne_top h).tsub_tsub_cancel_of_le h2

theorem sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) : a - b = a - c ↔ b = c :=
  (cancel_of_ne ha).tsub_right_inj (cancel_of_ne <| ne_top_of_le_ne_top ha hb)
    (cancel_of_ne <| ne_top_of_le_ne_top ha hc) hb hc

theorem sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c := by
  cases' le_or_ltₓ a b with hab hab
  · simp [← hab, ← mul_right_mono hab]
    
  rcases eq_or_lt_of_le (zero_le b) with (rfl | hb)
  · simp
    
  exact (cancel_of_ne <| mul_ne_top hab.ne_top (h hb hab)).tsub_mul

theorem mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c := by
  simp only [← mul_comm a]
  exact sub_mul h

end Sub

section Sum

open Finset

/-- A product of finite numbers is still finite -/
theorem prod_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀, ∀ a ∈ s, ∀, f a ≠ ∞) : (∏ a in s, f a) < ∞ :=
  WithTop.prod_lt_top h

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top {s : Finset α} {f : α → ℝ≥0∞} (h : ∀, ∀ a ∈ s, ∀, f a ≠ ∞) : (∑ a in s, f a) < ∞ :=
  WithTop.sum_lt_top h

/-- A sum of finite numbers is still finite -/
theorem sum_lt_top_iff {s : Finset α} {f : α → ℝ≥0∞} : (∑ a in s, f a) < ∞ ↔ ∀, ∀ a ∈ s, ∀, f a < ∞ :=
  WithTop.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
theorem sum_eq_top_iff {s : Finset α} {f : α → ℝ≥0∞} : (∑ x in s, f x) = ∞ ↔ ∃ a ∈ s, f a = ∞ :=
  WithTop.sum_eq_top_iff

theorem lt_top_of_sum_ne_top {s : Finset α} {f : α → ℝ≥0∞} (h : (∑ x in s, f x) ≠ ∞) {a : α} (ha : a ∈ s) : f a < ∞ :=
  sum_lt_top_iff.1 h.lt_top a ha

/-- seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
theorem to_nnreal_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀, ∀ a ∈ s, ∀, f a ≠ ∞) :
    Ennreal.toNnreal (∑ a in s, f a) = ∑ a in s, Ennreal.toNnreal (f a) := by
  rw [← coe_eq_coe, coe_to_nnreal, coe_finset_sum, sum_congr rfl]
  · intro x hx
    exact (coe_to_nnreal (hf x hx)).symm
    
  · exact (sum_lt_top hf).Ne
    

/-- seeing `ℝ≥0∞` as `real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
theorem to_real_sum {s : Finset α} {f : α → ℝ≥0∞} (hf : ∀, ∀ a ∈ s, ∀, f a ≠ ∞) :
    Ennreal.toReal (∑ a in s, f a) = ∑ a in s, Ennreal.toReal (f a) := by
  rw [Ennreal.toReal, to_nnreal_sum hf, Nnreal.coe_sum]
  rfl

theorem of_real_sum_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    Ennreal.ofReal (∑ i in s, f i) = ∑ i in s, Ennreal.ofReal (f i) := by
  simp_rw [Ennreal.ofReal, ← coe_finset_sum, coe_eq_coe]
  exact Real.to_nnreal_sum_of_nonneg hf

theorem sum_lt_sum_of_nonempty {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞} (Hlt : ∀, ∀ i ∈ s, ∀, f i < g i) :
    (∑ i in s, f i) < ∑ i in s, g i := by
  induction' hs using Finset.Nonempty.cons_induction with a a s as hs IH
  · simp [← Hlt _ (Finset.mem_singleton_self _)]
    
  · simp only [← as, ← Finset.sum_cons, ← not_false_iff]
    exact Ennreal.add_lt_add (Hlt _ (Finset.mem_cons_self _ _)) (IH fun i hi => Hlt _ (Finset.mem_cons.2 <| Or.inr hi))
    

theorem exists_le_of_sum_le {s : Finset α} (hs : s.Nonempty) {f g : α → ℝ≥0∞} (Hle : (∑ i in s, f i) ≤ ∑ i in s, g i) :
    ∃ i ∈ s, f i ≤ g i := by
  contrapose! Hle
  apply Ennreal.sum_lt_sum_of_nonempty hs Hle

end Sum

section Interval

variable {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : Set ℝ≥0∞}

protected theorem Ico_eq_Iio : Ico 0 y = Iio y :=
  Ico_bot

theorem mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) := fun xt ε0 => lt_add_right xt ε0

theorem mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) := fun xt x0 ε0 ε0' =>
  ⟨Ennreal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

end Interval

section Bit

@[mono]
theorem bit0_strict_mono : StrictMono (bit0 : ℝ≥0∞ → ℝ≥0∞) := fun a b h => add_lt_add h h

theorem bit0_injective : Function.Injective (bit0 : ℝ≥0∞ → ℝ≥0∞) :=
  bit0_strict_mono.Injective

@[simp]
theorem bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b :=
  bit0_strict_mono.lt_iff_lt

@[simp, mono]
theorem bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b :=
  bit0_strict_mono.le_iff_le

@[simp]
theorem bit0_inj : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff

@[simp]
theorem bit0_eq_zero_iff : bit0 a = 0 ↔ a = 0 :=
  bit0_injective.eq_iff' bit0_zero

@[simp]
theorem bit0_top : bit0 ∞ = ∞ :=
  add_top

@[simp]
theorem bit0_eq_top_iff : bit0 a = ∞ ↔ a = ∞ :=
  bit0_injective.eq_iff' bit0_top

@[mono]
theorem bit1_strict_mono : StrictMono (bit1 : ℝ≥0∞ → ℝ≥0∞) := fun a b h =>
  Ennreal.add_lt_add_right one_ne_top (bit0_strict_mono h)

theorem bit1_injective : Function.Injective (bit1 : ℝ≥0∞ → ℝ≥0∞) :=
  bit1_strict_mono.Injective

@[simp]
theorem bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
  bit1_strict_mono.lt_iff_lt

@[simp, mono]
theorem bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
  bit1_strict_mono.le_iff_le

@[simp]
theorem bit1_inj : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff

@[simp]
theorem bit1_ne_zero : bit1 a ≠ 0 := by
  simp [← bit1]

@[simp]
theorem bit1_top : bit1 ∞ = ∞ := by
  rw [bit1, bit0_top, top_add]

@[simp]
theorem bit1_eq_top_iff : bit1 a = ∞ ↔ a = ∞ :=
  bit1_injective.eq_iff' bit1_top

@[simp]
theorem bit1_eq_one_iff : bit1 a = 1 ↔ a = 0 :=
  bit1_injective.eq_iff' bit1_zero

end Bit

section Inv

noncomputable section

instance : Inv ℝ≥0∞ :=
  ⟨fun a => inf { b | 1 ≤ a * b }⟩

instance : DivInvMonoidₓ ℝ≥0∞ :=
  { (inferInstance : Monoidₓ ℝ≥0∞) with inv := Inv.inv }

theorem div_eq_inv_mul : a / b = b⁻¹ * a := by
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
  show inf { b : ℝ≥0∞ | 1 ≤ 0 * b } = ∞ by
    simp <;> rfl

@[simp]
theorem inv_top : ∞⁻¹ = 0 :=
  bot_unique <|
    le_of_forall_le_of_dense fun a (h : a > 0) =>
      Inf_le <| by
        simp [*, ← ne_of_gtₓ h, ← top_mul]

theorem coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
  le_Inf fun b (hb : 1 ≤ ↑r * b) =>
    coe_le_iff.2 <| by
      rintro b rfl
      apply Nnreal.inv_le_of_le_mul
      rwa [← coe_mul, ← coe_one, coe_le_coe] at hb

@[simp, norm_cast]
theorem coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
  coe_inv_le.antisymm <|
    Inf_le <|
      le_of_eqₓ <| by
        rw [← coe_mul, mul_inv_cancel hr, coe_one]

@[norm_cast]
theorem coe_inv_two : ((2⁻¹ : ℝ≥0 ) : ℝ≥0∞) = 2⁻¹ := by
  rw [coe_inv _root_.two_ne_zero, coe_two]

@[simp, norm_cast]
theorem coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r := by
  rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

theorem div_zero (h : a ≠ 0) : a / 0 = ∞ := by
  simp [← div_eq_mul_inv, ← h]

@[simp]
theorem inv_one : (1 : ℝ≥0∞)⁻¹ = 1 := by
  simpa only [← coe_inv one_ne_zero, ← coe_one] using coe_eq_coe.2 inv_one

@[simp]
theorem div_one {a : ℝ≥0∞} : a / 1 = a := by
  rw [div_eq_mul_inv, inv_one, mul_oneₓ]

protected theorem inv_pow {n : ℕ} : (a ^ n)⁻¹ = a⁻¹ ^ n := by
  cases n
  · simp only [← pow_zeroₓ, ← inv_one]
    
  induction a using WithTop.recTopCoe
  · simp [← top_pow n.succ_pos]
    
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp [← top_pow, ← zero_pow, ← n.succ_pos]
    
  rw [← coe_inv ha, ← coe_pow, ← coe_inv (pow_ne_zero _ ha), ← inv_pow, coe_pow]

theorem mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 := by
  lift a to ℝ≥0 using ht
  norm_cast  at *
  exact mul_inv_cancel h0

theorem inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
  mul_comm a a⁻¹ ▸ mul_inv_cancel h0 ht

theorem div_mul_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : b / a * a = b := by
  rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel h0 hI, mul_oneₓ]

theorem mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b := by
  rw [mul_comm, div_mul_cancel h0 hI]

instance : HasInvolutiveInv ℝ≥0∞ where
  inv := Inv.inv
  inv_inv := fun a => by
    by_cases' a = 0 <;> cases a <;> simp_all [← none_eq_top, ← some_eq_coe, -coe_inv, ← (coe_inv _).symm]

@[simp]
theorem inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
  inv_zero ▸ inv_inj

theorem inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by
  simp

@[simp]
theorem inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x := by
  simp only [← lt_top_iff_ne_top, ← inv_ne_top, ← pos_iff_ne_zero]

theorem div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
  mul_lt_top h1 (inv_ne_top.mpr h2)

@[simp]
theorem inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
  inv_top ▸ inv_inj

theorem inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by
  simp

theorem mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  induction b using WithTop.recTopCoe
  · replace ha : a ≠ 0 := ha.neg_resolve_right rfl
    simp [← ha]
    
  induction a using WithTop.recTopCoe
  · replace hb : b ≠ 0 := coe_ne_zero.1 (hb.neg_resolve_left rfl)
    simp [← hb]
    
  by_cases' h'a : a = 0
  · simp only [← h'a, ← WithTop.top_mul, ← Ennreal.inv_zero, ← Ennreal.coe_ne_top, ← zero_mul, ← Ne.def, ←
      not_false_iff, ← Ennreal.coe_zero, ← Ennreal.inv_eq_zero]
    
  by_cases' h'b : b = 0
  · simp only [← h'b, ← Ennreal.inv_zero, ← Ennreal.coe_ne_top, ← WithTop.mul_top, ← Ne.def, ← not_false_iff, ←
      mul_zero, ← Ennreal.coe_zero, ← Ennreal.inv_eq_zero]
    
  rw [← Ennreal.coe_mul, ← Ennreal.coe_inv, ← Ennreal.coe_inv h'a, ← Ennreal.coe_inv h'b, ← Ennreal.coe_mul,
    mul_inv_rev, mul_comm]
  simp [← h'a, ← h'b]

@[simp]
theorem inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
  pos_iff_ne_zero.trans inv_ne_zero

theorem inv_strict_anti : StrictAnti (Inv.inv : ℝ≥0∞ → ℝ≥0∞) := by
  intro a b h
  lift a to ℝ≥0 using h.ne_top
  induction b using WithTop.recTopCoe
  · simp
    
  rw [coe_lt_coe] at h
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp [← h]
    
  rw [← coe_inv h.ne_bot, ← coe_inv ha, coe_lt_coe]
  exact Nnreal.inv_lt_inv ha h

@[simp]
theorem inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
  inv_strict_anti.lt_iff_lt

theorem inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa only [← inv_invₓ] using @inv_lt_inv a b⁻¹

theorem lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa only [← inv_invₓ] using @inv_lt_inv a⁻¹ b

-- higher than le_inv_iff_mul_le
@[simp]
theorem inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  inv_strict_anti.le_iff_le

theorem inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  simpa only [← inv_invₓ] using @inv_le_inv a b⁻¹

theorem le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  simpa only [← inv_invₓ] using @inv_le_inv a⁻¹ b

@[simp]
theorem inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  inv_le_iff_inv_le.trans <| by
    rw [inv_one]

theorem one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  le_inv_iff_le_inv.trans <| by
    rw [inv_one]

@[simp]
theorem inv_lt_one : a⁻¹ < 1 ↔ 1 < a :=
  inv_lt_iff_inv_lt.trans <| by
    rw [inv_one]

/-- The inverse map `λ x, x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `order_dual` -/
@[simps apply]
def _root_.order_iso.inv_ennreal : ℝ≥0∞ ≃o ℝ≥0∞ᵒᵈ where
  map_rel_iff' := fun a b => Ennreal.inv_le_inv
  toEquiv := (Equivₓ.inv ℝ≥0∞).trans OrderDual.toDual

@[simp]
theorem _root_.order_iso.inv_ennreal_symm_apply : OrderIso.invEnnreal.symm a = (OrderDual.ofDual a)⁻¹ :=
  rfl

theorem pow_le_pow_of_le_one {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n := by
  rw [← inv_invₓ a, ← Ennreal.inv_pow, ← @Ennreal.inv_pow a⁻¹, inv_le_inv]
  exact pow_le_pow (one_le_inv.2 ha) h

@[simp]
theorem div_top : a / ∞ = 0 := by
  rw [div_eq_mul_inv, inv_top, mul_zero]

@[simp]
theorem top_div_coe : ∞ / p = ∞ := by
  simp [← div_eq_mul_inv, ← top_mul]

theorem top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ := by
  lift a to ℝ≥0 using h
  exact top_div_coe

theorem top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ :=
  top_div_of_ne_top h.Ne

theorem top_div : ∞ / a = if a = ∞ then 0 else ∞ := by
  by_cases' a = ∞ <;> simp [← top_div_of_ne_top, *]

@[simp]
theorem zero_div : 0 / a = 0 :=
  zero_mul a⁻¹

theorem div_eq_top : a / b = ∞ ↔ a ≠ 0 ∧ b = 0 ∨ a = ∞ ∧ b ≠ ∞ := by
  simp [← div_eq_mul_inv, ← Ennreal.mul_eq_top]

theorem le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : a ≤ c / b ↔ a * b ≤ c := by
  induction b using WithTop.recTopCoe
  · lift c to ℝ≥0 using ht.neg_resolve_left rfl
    rw [div_top, nonpos_iff_eq_zero, mul_top]
    rcases eq_or_ne a 0 with (rfl | ha) <;> simp [*]
    
  rcases eq_or_ne b 0 with (rfl | hb)
  · have hc : c ≠ 0 := h0.neg_resolve_left rfl
    simp [← div_zero hc]
    
  · rw [← coe_ne_zero] at hb
    rw [← Ennreal.mul_le_mul_right hb coe_ne_top, div_mul_cancel hb coe_ne_top]
    

theorem div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) : a / b ≤ c ↔ a ≤ c * b := by
  suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹ by
    simpa [← div_eq_mul_inv]
  refine' (le_div_iff_mul_le _ _).symm <;> simpa

theorem lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) : c < a / b ↔ c * b < a :=
  lt_iff_lt_of_le_iff_le (div_le_iff_le_mul hb0 hbt)

theorem div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b := by
  by_cases' h0 : c = 0
  · have : a = 0 := by
      simpa [← h0] using h
    simp [*]
    
  by_cases' hinf : c = ∞
  · simp [← hinf]
    
  exact (div_le_iff_le_mul (Or.inl h0) (Or.inl hinf)).2 h

theorem div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h

theorem mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b := by
  rw [← inv_invₓ c]
  exact div_le_of_le_mul h

theorem mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
  mul_comm a c ▸ mul_le_of_le_div h

protected theorem div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) : c / b < a ↔ c < a * b :=
  lt_iff_lt_of_le_iff_le <| le_div_iff_mul_le h0 ht

theorem mul_lt_of_lt_div (h : a < b / c) : a * c < b := by
  contrapose! h
  exact Ennreal.div_le_of_le_mul h

theorem mul_lt_of_lt_div' (h : a < b / c) : c * a < b :=
  mul_comm a c ▸ mul_lt_of_lt_div h

theorem inv_le_iff_le_mul (h₁ : b = ∞ → a ≠ 0) (h₂ : a = ∞ → b ≠ 0) : a⁻¹ ≤ b ↔ 1 ≤ a * b := by
  rw [← one_div, div_le_iff_le_mul, mul_comm]
  exacts[or_not_of_imp h₁, not_or_of_imp h₂]

@[simp]
theorem le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 := by
  rw [← one_div, le_div_iff_mul_le] <;>
    · right
      simp
      

theorem div_le_div {a b c d : ℝ≥0∞} (hab : a ≤ b) (hdc : d ≤ c) : a / c ≤ b / d :=
  div_eq_mul_inv b d ▸ div_eq_mul_inv a c ▸ Ennreal.mul_le_mul hab (Ennreal.inv_le_inv.mpr hdc)

theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ := by
  have hb : b ≠ ∞ := by
    rintro rfl
    simpa [← left_ne_zero_of_mul_eq_one h] using h
  rw [← mul_oneₓ a, ← mul_inv_cancel (right_ne_zero_of_mul_eq_one h) hb, ← mul_assoc, h, one_mulₓ]

theorem mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : r * a ≤ b ↔ a ≤ r⁻¹ * b := by
  rw [← @Ennreal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, mul_inv_cancel hr₀ hr₁, one_mulₓ]

theorem le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0 , ↑r < x → ↑r ≤ y) : x ≤ y := by
  refine' le_of_forall_ge_of_dense fun r hr => _
  lift r to ℝ≥0 using ne_top_of_lt hr
  exact h r hr

theorem le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0 , 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
  le_of_forall_nnreal_lt fun r hr => (zero_le r).eq_or_lt.elim (fun h => h ▸ zero_le _) fun h0 => h r h0 hr

theorem eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0 , ↑r ≤ x) : x = ∞ :=
  top_unique <| le_of_forall_nnreal_lt fun r hr => h r

theorem add_div : (a + b) / c = a / c + b / c :=
  right_distrib a b c⁻¹

theorem div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
  add_div.symm

theorem div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
  mul_inv_cancel h0 hI

theorem mul_div_le : a * (b / a) ≤ b :=
  mul_le_of_le_div' le_rfl

-- TODO: add this lemma for an `is_unit` in any `division_monoid`
theorem eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) : b = c / a ↔ a * b = c :=
  ⟨fun h => by
    rw [h, mul_div_cancel' ha ha'], fun h => by
    rw [← h, mul_div_assoc, mul_div_cancel' ha ha']⟩

theorem div_eq_div_iff (ha : a ≠ 0) (ha' : a ≠ ∞) (hb : b ≠ 0) (hb' : b ≠ ∞) : c / b = d / a ↔ a * c = b * d := by
  rw [eq_div_iff ha ha']
  conv_rhs => rw [eq_comm]
  rw [← eq_div_iff hb hb', mul_div_assoc, eq_comm]

theorem inv_two_add_inv_two : (2 : ℝ≥0∞)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, ← div_eq_mul_inv, div_self two_ne_zero two_ne_top]

theorem inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 1 := by
  rw
      [show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹ by
        ring,
      ← div_eq_mul_inv, Ennreal.div_self] <;>
    simp

@[simp]
theorem add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a := by
  rw [div_eq_mul_inv, ← mul_addₓ, inv_two_add_inv_two, mul_oneₓ]

@[simp]
theorem add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a := by
  rw [div_eq_mul_inv, ← mul_addₓ, ← mul_addₓ, inv_three_add_inv_three, mul_oneₓ]

@[simp]
theorem div_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ := by
  simp [← div_eq_mul_inv]

@[simp]
theorem div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ := by
  simp [← pos_iff_ne_zero, ← not_or_distrib]

theorem half_pos {a : ℝ≥0∞} (h : a ≠ 0) : 0 < a / 2 := by
  simp [← h]

theorem one_half_lt_one : (2⁻¹ : ℝ≥0∞) < 1 :=
  inv_lt_one.2 <| one_lt_two

theorem half_lt_self {a : ℝ≥0∞} (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a := by
  lift a to ℝ≥0 using ht
  rw [coe_ne_zero] at hz
  rw [← coe_two, ← coe_div, coe_lt_coe]
  exacts[Nnreal.half_lt_self hz, two_ne_zero']

theorem half_le_self : a / 2 ≤ a :=
  le_add_self.trans_eq (add_halves _)

theorem sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 := by
  lift a to ℝ≥0 using h
  exact
    sub_eq_of_add_eq
      (mul_ne_top coe_ne_top <| by
        simp )
      (add_halves a)

@[simp]
theorem one_sub_inv_two : (1 : ℝ≥0∞) - 2⁻¹ = 2⁻¹ := by
  simpa only [← div_eq_mul_inv, ← one_mulₓ] using sub_half one_ne_top

/-- The birational order isomorphism between `ℝ≥0∞` and the unit interval `set.Iic (1 : ℝ≥0∞)`. -/
@[simps apply_coe]
def orderIsoIicOneBirational : ℝ≥0∞ ≃o Iic (1 : ℝ≥0∞) := by
  refine'
    StrictMono.orderIsoOfRightInverse (fun x => ⟨(x⁻¹ + 1)⁻¹, inv_le_one.2 <| le_add_self⟩) (fun x y hxy => _)
      (fun x => (x⁻¹ - 1)⁻¹) fun x => Subtype.ext _
  · simpa only [← Subtype.mk_lt_mk, ← inv_lt_inv, ← Ennreal.add_lt_add_iff_right one_ne_top]
    
  · have : (1 : ℝ≥0∞) ≤ x⁻¹ := one_le_inv.2 x.2
    simp only [← inv_invₓ, ← Subtype.coe_mk, ← tsub_add_cancel_of_le this]
    

@[simp]
theorem order_iso_Iic_one_birational_symm_apply (x : Iic (1 : ℝ≥0∞)) : orderIsoIicOneBirational.symm x = (x⁻¹ - 1)⁻¹ :=
  rfl

/-- Order isomorphism between an initial interval in `ℝ≥0∞` and an initial interval in `ℝ≥0`. -/
@[simps apply_coe]
def orderIsoIicCoe (a : ℝ≥0 ) : Iic (a : ℝ≥0∞) ≃o Iic a :=
  OrderIso.symm
    { toFun := fun x => ⟨x, coe_le_coe.2 x.2⟩,
      invFun := fun x => ⟨Ennreal.toNnreal x, coe_le_coe.1 <| coe_to_nnreal_le_self.trans x.2⟩,
      left_inv := fun x => Subtype.ext <| to_nnreal_coe,
      right_inv := fun x => Subtype.ext <| coe_to_nnreal (ne_top_of_le_ne_top coe_ne_top x.2),
      map_rel_iff' := fun x y => by
        simp only [← Equivₓ.coe_fn_mk, ← Subtype.mk_le_mk, ← coe_coe, ← coe_le_coe, ← Subtype.coe_le_coe] }

@[simp]
theorem order_iso_Iic_coe_symm_apply_coe (a : ℝ≥0 ) (b : Iic a) : ((orderIsoIicCoe a).symm b : ℝ≥0∞) = b :=
  rfl

/-- An order isomorphism between the extended nonnegative real numbers and the unit interval. -/
def orderIsoUnitIntervalBirational : ℝ≥0∞ ≃o Icc (0 : ℝ) 1 :=
  orderIsoIicOneBirational.trans <| (orderIsoIicCoe 1).trans <| (Nnreal.orderIsoIccZeroCoe 1).symm

@[simp]
theorem order_iso_unit_interval_birational_apply_coe (x : ℝ≥0∞) :
    (orderIsoUnitIntervalBirational x : ℝ) = (x⁻¹ + 1)⁻¹.toReal :=
  rfl

theorem exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) : ∃ n : ℕ, (n : ℝ≥0∞)⁻¹ < a :=
  inv_invₓ a ▸ by
    simp only [← inv_lt_inv, ← Ennreal.exists_nat_gt (inv_ne_top.2 h)]

theorem exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n > 0, b < (n : ℕ) * a := by
  have : b / a ≠ ∞ := mul_ne_top hb (inv_ne_top.2 ha)
  refine' (Ennreal.exists_nat_gt this).imp fun n hn => _
  have : ↑0 < (n : ℝ≥0∞) :=
    lt_of_le_of_ltₓ
      (by
        simp )
      hn
  refine' ⟨coe_nat_lt_coe_nat.1 this, _⟩
  rwa [← Ennreal.div_lt_iff (Or.inl ha) (Or.inr hb)]

theorem exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) : ∃ n : ℕ, b < n * a :=
  (exists_nat_pos_mul_gt ha hb).imp fun n => Exists.snd

theorem exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b := by
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩
  have : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 npos.lt.ne'
  use n, npos
  rwa [← one_mulₓ b, ← inv_mul_cancel this coe_nat_ne_top, mul_assoc,
    mul_lt_mul_left (inv_ne_zero.2 coe_nat_ne_top) (inv_ne_top.2 this)]

theorem exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) : ∃ n > 0, ↑(n : ℝ≥0 ) * a < b := by
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩
  use (n : ℝ≥0 )⁻¹
  simp [*, ← npos.ne', ← zero_lt_one]

theorem exists_inv_two_pow_lt (ha : a ≠ 0) : ∃ n : ℕ, 2⁻¹ ^ n < a := by
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩
  refine' ⟨n, lt_transₓ _ hn⟩
  rw [← Ennreal.inv_pow, inv_lt_inv]
  norm_cast
  exact n.lt_two_pow

@[simp, norm_cast]
theorem coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r ^ n) : ℝ≥0∞) = r ^ n := by
  cases n
  · simp only [← Int.of_nat_eq_coe, ← coe_pow, ← zpow_coe_nat]
    
  · have : r ^ n.succ ≠ 0 := pow_ne_zero (n + 1) hr
    simp only [← zpow_neg_succ_of_nat, ← coe_inv this, ← coe_pow]
    

theorem zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n := by
  cases n
  · exact Ennreal.pow_pos ha.bot_lt n
    
  · simp only [← h'a, ← pow_eq_top_iff, ← zpow_neg_succ_of_nat, ← Ne.def, ← not_false_iff, ← inv_pos, ← false_andₓ]
    

theorem zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ := by
  cases n
  · exact Ennreal.pow_lt_top h'a.lt_top _
    
  · simp only [← Ennreal.pow_pos ha.bot_lt (n + 1), ← zpow_neg_succ_of_nat, ← inv_lt_top]
    

theorem exists_mem_Ico_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by
    simpa only [← Ne.def, ← coe_eq_zero] using (ennreal.zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1) := by
    refine' Nnreal.exists_mem_Ico_zpow _ (one_lt_coe_iff.1 hy)
    simpa only [← Ne.def, ← coe_eq_zero] using hx
  refine' ⟨n, _, _⟩
  · rwa [← Ennreal.coe_zpow A, Ennreal.coe_le_coe]
    
  · rwa [← Ennreal.coe_zpow A, Ennreal.coe_lt_coe]
    

theorem exists_mem_Ioc_zpow {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
    ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) := by
  lift x to ℝ≥0 using h'x
  lift y to ℝ≥0 using h'y
  have A : y ≠ 0 := by
    simpa only [← Ne.def, ← coe_eq_zero] using (ennreal.zero_lt_one.trans hy).ne'
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1) := by
    refine' Nnreal.exists_mem_Ioc_zpow _ (one_lt_coe_iff.1 hy)
    simpa only [← Ne.def, ← coe_eq_zero] using hx
  refine' ⟨n, _, _⟩
  · rwa [← Ennreal.coe_zpow A, Ennreal.coe_lt_coe]
    
  · rwa [← Ennreal.coe_zpow A, Ennreal.coe_le_coe]
    

theorem Ioo_zero_top_eq_Union_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
    Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ n : ℤ, Ico (y ^ n) (y ^ (n + 1)) := by
  ext x
  simp only [← mem_Union, ← mem_Ioo, ← mem_Ico]
  constructor
  · rintro ⟨hx, h'x⟩
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y
    
  · rintro ⟨n, hn, h'n⟩
    constructor
    · apply lt_of_lt_of_leₓ _ hn
      exact Ennreal.zpow_pos (ennreal.zero_lt_one.trans hy).ne' h'y _
      
    · apply lt_transₓ h'n _
      exact Ennreal.zpow_lt_top (ennreal.zero_lt_one.trans hy).ne' h'y _
      
    

theorem zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b := by
  induction' a with a a <;> induction' b with b b
  · simp only [← Int.of_nat_eq_coe, ← zpow_coe_nat]
    exact pow_le_pow hx (Int.le_of_coe_nat_le_coe_nat h)
    
  · apply absurd h (not_le_of_gtₓ _)
    exact lt_of_lt_of_leₓ (Int.neg_succ_lt_zeroₓ _) (Int.of_nat_nonneg _)
    
  · simp only [← zpow_neg_succ_of_nat, ← Int.of_nat_eq_coe, ← zpow_coe_nat]
    refine' le_transₓ (inv_le_one.2 _) _ <;> exact Ennreal.one_le_pow_of_one_le hx _
    
  · simp only [← zpow_neg_succ_of_nat, ← inv_le_inv]
    apply pow_le_pow hx
    simpa only [Int.coe_nat_le_coe_nat_iff, ← neg_le_neg_iff, ← Int.coe_nat_add, ← Int.coe_nat_one, ←
      Int.neg_succ_of_nat_eq] using h
    

theorem monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : Monotone ((· ^ ·) x : ℤ → ℝ≥0∞) := fun a b h => zpow_le_of_le hx h

theorem zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) : x ^ (m + n) = x ^ m * x ^ n := by
  lift x to ℝ≥0 using h'x
  replace hx : x ≠ 0
  · simpa only [← Ne.def, ← coe_eq_zero] using hx
    
  simp only [coe_zpow hx, ← zpow_add₀ hx, ← coe_mul]

end Inv

section Real

theorem to_real_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a + b).toReal = a.toReal + b.toReal := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  rfl

theorem to_real_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞) : (a - b).toReal = a.toReal - b.toReal := by
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h
  lift a to ℝ≥0 using ha
  simp only [Ennreal.coe_sub, ← Ennreal.coe_to_real, ← Nnreal.coe_sub (ennreal.coe_le_coe.mp h)]

theorem le_to_real_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.toReal - b.toReal ≤ (a - b).toReal := by
  lift b to ℝ≥0 using hb
  induction a using WithTop.recTopCoe
  · simp
    
  · simp only [coe_sub, ← Nnreal.sub_def, ← Real.coe_to_nnreal', ← coe_to_real]
    exact le_max_leftₓ _ _
    

theorem to_real_add_le : (a + b).toReal ≤ a.toReal + b.toReal :=
  if ha : a = ∞ then by
    simp only [← ha, ← top_add, ← top_to_real, ← zero_addₓ, ← to_real_nonneg]
  else
    if hb : b = ∞ then by
      simp only [← hb, ← add_top, ← top_to_real, ← add_zeroₓ, ← to_real_nonneg]
    else le_of_eqₓ (to_real_add ha hb)

theorem of_real_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    Ennreal.ofReal (p + q) = Ennreal.ofReal p + Ennreal.ofReal q := by
  rw [Ennreal.ofReal, Ennreal.ofReal, Ennreal.ofReal, ← coe_add, coe_eq_coe, Real.to_nnreal_add hp hq]

theorem of_real_add_le {p q : ℝ} : Ennreal.ofReal (p + q) ≤ Ennreal.ofReal p + Ennreal.ofReal q :=
  coe_le_coe.2 Real.to_nnreal_add_le

@[simp]
theorem to_real_le_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal ≤ b.toReal ↔ a ≤ b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

theorem to_real_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toReal ≤ b.toReal :=
  (to_real_le_to_real (h.trans_lt (lt_top_iff_ne_top.2 hb)).Ne hb).2 h

@[simp]
theorem to_real_lt_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toReal < b.toReal ↔ a < b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  norm_cast

theorem to_real_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toReal < b.toReal :=
  (to_real_lt_to_real (h.trans (lt_top_iff_ne_top.2 hb)).Ne hb).2 h

theorem to_nnreal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.toNnreal ≤ b.toNnreal := by
  simpa [Ennreal.coe_le_coe, ← hb, ← (h.trans_lt hb.lt_top).Ne]

@[simp]
theorem to_nnreal_le_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNnreal ≤ b.toNnreal ↔ a ≤ b :=
  ⟨fun h => by
    rwa [← coe_to_nnreal ha, ← coe_to_nnreal hb, coe_le_coe], to_nnreal_mono hb⟩

theorem to_nnreal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.toNnreal < b.toNnreal := by
  simpa [Ennreal.coe_lt_coe, ← hb, ← (h.trans hb.lt_top).Ne]

@[simp]
theorem to_nnreal_lt_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) : a.toNnreal < b.toNnreal ↔ a < b :=
  ⟨fun h => by
    rwa [← coe_to_nnreal ha, ← coe_to_nnreal hb, coe_lt_coe], to_nnreal_strict_mono hb⟩

theorem to_real_max (hr : a ≠ ∞) (hp : b ≠ ∞) : Ennreal.toReal (max a b) = max (Ennreal.toReal a) (Ennreal.toReal b) :=
  (le_totalₓ a b).elim
    (fun h => by
      simp only [← h, ← (Ennreal.to_real_le_to_real hr hp).2 h, ← max_eq_rightₓ])
    fun h => by
    simp only [← h, ← (Ennreal.to_real_le_to_real hp hr).2 h, ← max_eq_leftₓ]

theorem to_nnreal_pos_iff : 0 < a.toNnreal ↔ 0 < a ∧ a < ∞ := by
  induction a using WithTop.recTopCoe <;> simp

theorem to_nnreal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toNnreal :=
  to_nnreal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

theorem to_real_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞ :=
  Nnreal.coe_pos.trans to_nnreal_pos_iff

theorem to_real_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.toReal :=
  to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

theorem of_real_le_of_real {p q : ℝ} (h : p ≤ q) : Ennreal.ofReal p ≤ Ennreal.ofReal q := by
  simp [← Ennreal.ofReal, ← Real.to_nnreal_le_to_nnreal h]

theorem of_real_le_of_le_to_real {a : ℝ} {b : ℝ≥0∞} (h : a ≤ Ennreal.toReal b) : Ennreal.ofReal a ≤ b :=
  (of_real_le_of_real h).trans of_real_to_real_le

@[simp]
theorem of_real_le_of_real_iff {p q : ℝ} (h : 0 ≤ q) : Ennreal.ofReal p ≤ Ennreal.ofReal q ↔ p ≤ q := by
  rw [Ennreal.ofReal, Ennreal.ofReal, coe_le_coe, Real.to_nnreal_le_to_nnreal_iff h]

@[simp]
theorem of_real_lt_of_real_iff {p q : ℝ} (h : 0 < q) : Ennreal.ofReal p < Ennreal.ofReal q ↔ p < q := by
  rw [Ennreal.ofReal, Ennreal.ofReal, coe_lt_coe, Real.to_nnreal_lt_to_nnreal_iff h]

theorem of_real_lt_of_real_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) : Ennreal.ofReal p < Ennreal.ofReal q ↔ p < q := by
  rw [Ennreal.ofReal, Ennreal.ofReal, coe_lt_coe, Real.to_nnreal_lt_to_nnreal_iff_of_nonneg hp]

@[simp]
theorem of_real_pos {p : ℝ} : 0 < Ennreal.ofReal p ↔ 0 < p := by
  simp [← Ennreal.ofReal]

@[simp]
theorem of_real_eq_zero {p : ℝ} : Ennreal.ofReal p = 0 ↔ p ≤ 0 := by
  simp [← Ennreal.ofReal]

@[simp]
theorem zero_eq_of_real {p : ℝ} : 0 = Ennreal.ofReal p ↔ p ≤ 0 :=
  eq_comm.trans of_real_eq_zero

alias of_real_eq_zero ↔ _ of_real_of_nonpos

theorem of_real_sub (p : ℝ) (hq : 0 ≤ q) : Ennreal.ofReal (p - q) = Ennreal.ofReal p - Ennreal.ofReal q := by
  obtain h | h := le_totalₓ p q
  · rw [of_real_of_nonpos (sub_nonpos_of_le h), tsub_eq_zero_of_le (of_real_le_of_real h)]
    
  refine' Ennreal.eq_sub_of_add_eq of_real_ne_top _
  rw [← of_real_add (sub_nonneg_of_le h) hq, sub_add_cancel]

theorem of_real_le_iff_le_to_real {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) : Ennreal.ofReal a ≤ b ↔ a ≤ Ennreal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [← Ennreal.ofReal, ← Ennreal.toReal] using Real.to_nnreal_le_iff_le_coe

theorem of_real_lt_iff_lt_to_real {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
    Ennreal.ofReal a < b ↔ a < Ennreal.toReal b := by
  lift b to ℝ≥0 using hb
  simpa [← Ennreal.ofReal, ← Ennreal.toReal] using Real.to_nnreal_lt_iff_lt_coe ha

theorem le_of_real_iff_to_real_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
    a ≤ Ennreal.ofReal b ↔ Ennreal.toReal a ≤ b := by
  lift a to ℝ≥0 using ha
  simpa [← Ennreal.ofReal, ← Ennreal.toReal] using Real.le_to_nnreal_iff_coe_le hb

theorem to_real_le_of_le_of_real {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ Ennreal.ofReal b) : Ennreal.toReal a ≤ b :=
  have ha : a ≠ ∞ := ne_top_of_le_ne_top of_real_ne_top h
  (le_of_real_iff_to_real_le ha hb).1 h

theorem lt_of_real_iff_to_real_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) : a < Ennreal.ofReal b ↔ Ennreal.toReal a < b := by
  lift a to ℝ≥0 using ha
  simpa [← Ennreal.ofReal, ← Ennreal.toReal] using Real.lt_to_nnreal_iff_coe_lt

theorem of_real_mul {p q : ℝ} (hp : 0 ≤ p) : Ennreal.ofReal (p * q) = Ennreal.ofReal p * Ennreal.ofReal q := by
  simp only [← Ennreal.ofReal, coe_mul, ← Real.to_nnreal_mul hp]

theorem of_real_mul' {p q : ℝ} (hq : 0 ≤ q) : Ennreal.ofReal (p * q) = Ennreal.ofReal p * Ennreal.ofReal q := by
  rw [mul_comm, of_real_mul hq, mul_comm]

theorem of_real_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) : Ennreal.ofReal (p ^ n) = Ennreal.ofReal p ^ n := by
  rw [of_real_eq_coe_nnreal hp, ← coe_pow, ← of_real_coe_nnreal, Nnreal.coe_pow, Nnreal.coe_mk]

theorem of_real_inv_of_pos {x : ℝ} (hx : 0 < x) : (Ennreal.ofReal x)⁻¹ = Ennreal.ofReal x⁻¹ := by
  rw [Ennreal.ofReal, Ennreal.ofReal, ←
    @coe_inv (Real.toNnreal x)
      (by
        simp [← hx]),
    coe_eq_coe, real.to_nnreal_inv.symm]

theorem of_real_div_of_pos {x y : ℝ} (hy : 0 < y) : Ennreal.ofReal (x / y) = Ennreal.ofReal x / Ennreal.ofReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, of_real_mul' (inv_nonneg.2 hy.le), of_real_inv_of_pos hy]

theorem to_nnreal_mul_top (a : ℝ≥0∞) : Ennreal.toNnreal (a * ∞) = 0 := by
  by_cases' h : a = 0
  · rw [h, zero_mul, zero_to_nnreal]
    
  · rw [mul_top, if_neg h, top_to_nnreal]
    

theorem to_nnreal_top_mul (a : ℝ≥0∞) : Ennreal.toNnreal (∞ * a) = 0 := by
  rw [mul_comm, to_nnreal_mul_top]

@[simp]
theorem to_nnreal_mul {a b : ℝ≥0∞} : (a * b).toNnreal = a.toNnreal * b.toNnreal := by
  induction a using WithTop.recTopCoe
  · rw [to_nnreal_top_mul, top_to_nnreal, zero_mul]
    
  induction b using WithTop.recTopCoe
  · rw [to_nnreal_mul_top, top_to_nnreal, mul_zero]
    
  simp only [← to_nnreal_coe, coe_mul]

@[simp]
theorem smul_to_nnreal (a : ℝ≥0 ) (b : ℝ≥0∞) : (a • b).toNnreal = a * b.toNnreal := by
  change ((a : ℝ≥0∞) * b).toNnreal = a * b.to_nnreal
  simp only [← Ennreal.to_nnreal_mul, ← Ennreal.to_nnreal_coe]

/-- `ennreal.to_nnreal` as a `monoid_hom`. -/
def toNnrealHom : ℝ≥0∞ →* ℝ≥0 where
  toFun := Ennreal.toNnreal
  map_one' := to_nnreal_coe
  map_mul' := fun _ _ => to_nnreal_mul

@[simp]
theorem to_nnreal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toNnreal = a.toNnreal ^ n :=
  toNnrealHom.map_pow a n

@[simp]
theorem to_nnreal_prod {ι : Type _} {s : Finset ι} {f : ι → ℝ≥0∞} :
    (∏ i in s, f i).toNnreal = ∏ i in s, (f i).toNnreal :=
  toNnrealHom.map_prod _ _

/-- `ennreal.to_real` as a `monoid_hom`. -/
def toRealHom : ℝ≥0∞ →* ℝ :=
  (Nnreal.toRealHom : ℝ≥0 →* ℝ).comp toNnrealHom

@[simp]
theorem to_real_mul : (a * b).toReal = a.toReal * b.toReal :=
  toRealHom.map_mul a b

@[simp]
theorem to_real_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).toReal = a.toReal ^ n :=
  toRealHom.map_pow a n

@[simp]
theorem to_real_prod {ι : Type _} {s : Finset ι} {f : ι → ℝ≥0∞} : (∏ i in s, f i).toReal = ∏ i in s, (f i).toReal :=
  toRealHom.map_prod _ _

theorem to_real_of_real_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
    Ennreal.toReal (Ennreal.ofReal c * a) = c * Ennreal.toReal a := by
  rw [Ennreal.to_real_mul, Ennreal.to_real_of_real h]

theorem to_real_mul_top (a : ℝ≥0∞) : Ennreal.toReal (a * ∞) = 0 := by
  rw [to_real_mul, top_to_real, mul_zero]

theorem to_real_top_mul (a : ℝ≥0∞) : Ennreal.toReal (∞ * a) = 0 := by
  rw [mul_comm]
  exact to_real_mul_top _

theorem to_real_eq_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : Ennreal.toReal a = Ennreal.toReal b ↔ a = b := by
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  simp only [← coe_eq_coe, ← Nnreal.coe_eq, ← coe_to_real]

theorem to_real_smul (r : ℝ≥0 ) (s : ℝ≥0∞) : (r • s).toReal = r • s.toReal := by
  rw [Ennreal.smul_def, smul_eq_mul, to_real_mul, coe_to_real]
  rfl

protected theorem trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.toReal := by
  simpa only [← or_iff_not_imp_left] using to_real_pos

protected theorem trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
    p = 0 ∧ q = 0 ∨
      p = 0 ∧ q = ∞ ∨
        p = 0 ∧ 0 < q.toReal ∨
          p = ∞ ∧ q = ∞ ∨ 0 < p.toReal ∧ q = ∞ ∨ 0 < p.toReal ∧ 0 < q.toReal ∧ p.toReal ≤ q.toReal :=
  by
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with ((rfl : 0 = p) | (hp : 0 < p))
  · simpa using q.trichotomy
    
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with (rfl | hq)
  · simpa using p.trichotomy
    
  repeat'
    right
  have hq' : 0 < q := lt_of_lt_of_leₓ hp hpq
  have hp' : p < ∞ := lt_of_le_of_ltₓ hpq hq
  simp [← Ennreal.to_real_le_to_real hp'.ne hq.ne, ← Ennreal.to_real_pos_iff, ← hpq, ← hp, ← hp', ← hq', ← hq]

protected theorem dichotomy (p : ℝ≥0∞) [Fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.toReal := by
  have : p = ⊤ ∨ 0 < p.to_real ∧ 1 ≤ p.to_real := by
    simpa using Ennreal.trichotomy₂ (Fact.out _ : 1 ≤ p)
  exact this.imp_right fun h => h.2

theorem to_nnreal_inv (a : ℝ≥0∞) : a⁻¹.toNnreal = a.toNnreal⁻¹ := by
  induction a using WithTop.recTopCoe
  · simp
    
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
    
  rw [← coe_inv ha, to_nnreal_coe, to_nnreal_coe]

theorem to_nnreal_div (a b : ℝ≥0∞) : (a / b).toNnreal = a.toNnreal / b.toNnreal := by
  rw [div_eq_mul_inv, to_nnreal_mul, to_nnreal_inv, div_eq_mul_inv]

theorem to_real_inv (a : ℝ≥0∞) : a⁻¹.toReal = a.toReal⁻¹ := by
  simp_rw [Ennreal.toReal]
  norm_cast
  exact to_nnreal_inv a

theorem to_real_div (a b : ℝ≥0∞) : (a / b).toReal = a.toReal / b.toReal := by
  rw [div_eq_mul_inv, to_real_mul, to_real_inv, div_eq_mul_inv]

theorem of_real_prod_of_nonneg {s : Finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
    Ennreal.ofReal (∏ i in s, f i) = ∏ i in s, Ennreal.ofReal (f i) := by
  simp_rw [Ennreal.ofReal, ← coe_finset_prod, coe_eq_coe]
  exact Real.to_nnreal_prod_of_nonneg hf

@[simp]
theorem to_nnreal_bit0 {x : ℝ≥0∞} : (bit0 x).toNnreal = bit0 x.toNnreal := by
  induction x using WithTop.recTopCoe
  · simp
    
  · exact to_nnreal_add coe_ne_top coe_ne_top
    

@[simp]
theorem to_nnreal_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) : (bit1 x).toNnreal = bit1 x.toNnreal := by
  simp [← bit1, ← bit1, ←
    to_nnreal_add
      (by
        rwa [Ne.def, bit0_eq_top_iff])
      Ennreal.one_ne_top]

@[simp]
theorem to_real_bit0 {x : ℝ≥0∞} : (bit0 x).toReal = bit0 x.toReal := by
  simp [← Ennreal.toReal]

@[simp]
theorem to_real_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) : (bit1 x).toReal = bit1 x.toReal := by
  simp [← Ennreal.toReal, ← hx_top]

@[simp]
theorem of_real_bit0 (r : ℝ) : Ennreal.ofReal (bit0 r) = bit0 (Ennreal.ofReal r) := by
  simp [← Ennreal.ofReal]

@[simp]
theorem of_real_bit1 {r : ℝ} (hr : 0 ≤ r) : Ennreal.ofReal (bit1 r) = bit1 (Ennreal.ofReal r) :=
  (of_real_add
        (by
          simp [← hr])
        zero_le_one).trans
    (by
      simp [← Real.to_nnreal_one, ← bit1])

end Real

section infi

variable {ι : Sort _} {f g : ι → ℝ≥0∞}

theorem infi_add : infi f + a = ⨅ i, f i + a :=
  le_antisymmₓ (le_infi fun i => add_le_add (infi_le _ _) <| le_rfl)
    (tsub_le_iff_right.1 <| le_infi fun i => tsub_le_iff_right.2 <| infi_le _ _)

theorem supr_sub : (⨆ i, f i) - a = ⨆ i, f i - a :=
  le_antisymmₓ (tsub_le_iff_right.2 <| supr_le fun i => tsub_le_iff_right.1 <| le_supr _ i)
    (supr_le fun i => tsub_le_tsub (le_supr _ _) (le_reflₓ a))

theorem sub_infi : (a - ⨅ i, f i) = ⨆ i, a - f i := by
  refine' eq_of_forall_ge_iff fun c => _
  rw [tsub_le_iff_right, add_commₓ, infi_add]
  simp [← tsub_le_iff_right, ← sub_eq_add_neg, ← add_commₓ]

theorem Inf_add {s : Set ℝ≥0∞} : inf s + a = ⨅ b ∈ s, b + a := by
  simp [← Inf_eq_infi, ← infi_add]

theorem add_infi {a : ℝ≥0∞} : a + infi f = ⨅ b, a + f b := by
  rw [add_commₓ, infi_add] <;> simp [← add_commₓ]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a a')
theorem infi_add_infi (h : ∀ i j, ∃ k, f k + g k ≤ f i + g j) : infi f + infi g = ⨅ a, f a + g a :=
  suffices (⨅ a, f a + g a) ≤ infi f + infi g from
    le_antisymmₓ (le_infi fun a => add_le_add (infi_le _ _) (infi_le _ _)) this
  calc
    (⨅ a, f a + g a) ≤ ⨅ (a) (a'), f a + g a' :=
      le_infi fun a =>
        le_infi fun a' =>
          let ⟨k, h⟩ := h a a'
          infi_le_of_le k h
    _ = infi f + infi g := by
      simp [← add_infi, ← infi_add]
    

theorem infi_sum {f : ι → α → ℝ≥0∞} {s : Finset α} [Nonempty ι]
    (h : ∀ (t : Finset α) (i j : ι), ∃ k, ∀, ∀ a ∈ t, ∀, f k a ≤ f i a ∧ f k a ≤ f j a) :
    (⨅ i, ∑ a in s, f i a) = ∑ a in s, ⨅ i, f i a := by
  induction' s using Finset.induction_on with a s ha ih
  · simp
    
  have : ∀ i j : ι, ∃ k : ι, (f k a + ∑ b in s, f k b) ≤ f i a + ∑ b in s, f j b := by
    intro i j
    obtain ⟨k, hk⟩ := h (insert a s) i j
    exact
      ⟨k,
        add_le_add (hk a (Finset.mem_insert_self _ _)).left <|
          Finset.sum_le_sum fun a ha => (hk _ <| Finset.mem_insert_of_mem ha).right⟩
  simp [← ha, ← ih.symm, ← infi_add_infi this]

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ennreal.infi_mul` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
theorem infi_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) : infi f * x = ⨅ i, f i * x :=
  le_antisymmₓ mul_right_mono.map_infi_le
    ((div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mp <|
      le_infi fun i => (div_le_iff_le_mul (Or.inl h0) <| Or.inl h).mpr <| infi_le _ _)

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.infi_mul_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
theorem infi_mul {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) : infi f * x = ⨅ i, f i * x := by
  by_cases' h0 : x = 0
  · simp only [← h0, ← mul_zero, ← infi_const]
    
  · exact infi_mul_of_ne h0 h
    

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.mul_infi_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
theorem mul_infi {ι} [Nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) : x * infi f = ⨅ i, x * f i := by
  simpa only [← mul_comm] using infi_mul h

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ennreal.mul_infi` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
theorem mul_infi_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) : x * infi f = ⨅ i, x * f i := by
  simpa only [← mul_comm] using infi_mul_of_ne h0 h

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/


end infi

section supr

@[simp]
theorem supr_eq_zero {ι : Sort _} {f : ι → ℝ≥0∞} : (⨆ i, f i) = 0 ↔ ∀ i, f i = 0 :=
  supr_eq_bot

@[simp]
theorem supr_zero_eq_zero {ι : Sort _} : (⨆ i : ι, (0 : ℝ≥0∞)) = 0 := by
  simp

theorem sup_eq_zero {a b : ℝ≥0∞} : a⊔b = 0 ↔ a = 0 ∧ b = 0 :=
  sup_eq_bot_iff

theorem supr_coe_nat : (⨆ n : ℕ, (n : ℝ≥0∞)) = ∞ :=
  (supr_eq_top _).2 fun b hb => Ennreal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

end supr

end Ennreal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0 } {u : Set ℝ≥0∞}

theorem preimage_coe_nnreal_ennreal (h : u.OrdConnected) : (coe ⁻¹' u : Set ℝ≥0 ).OrdConnected :=
  h.preimage_mono Ennreal.coe_mono

theorem image_coe_nnreal_ennreal (h : t.OrdConnected) : (coe '' t : Set ℝ≥0∞).OrdConnected := by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  rcases Ennreal.le_coe_iff.1 hz.2 with ⟨z, rfl, hzy⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨Ennreal.coe_le_coe.1 hz.1, Ennreal.coe_le_coe.1 hz.2⟩)

theorem preimage_ennreal_of_real (h : u.OrdConnected) : (Ennreal.ofReal ⁻¹' u).OrdConnected :=
  h.preimage_coe_nnreal_ennreal.preimage_real_to_nnreal

theorem image_ennreal_of_real (h : s.OrdConnected) : (Ennreal.ofReal '' s).OrdConnected := by
  simpa only [← image_image] using h.image_real_to_nnreal.image_coe_nnreal_ennreal

end OrdConnected

end Set

