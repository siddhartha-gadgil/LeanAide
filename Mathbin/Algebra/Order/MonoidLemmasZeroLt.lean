/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Algebra.GroupWithZero.Defs

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

*  the notation `α>0` to stands for `{x : α // 0 < x}`.

If the type `α` also has a multiplication, then we combine this with (`contravariant_`)
`covariant_class`es to assume that multiplication by positive elements is (strictly) monotone on a
`mul_zero_class`, `monoid_with_zero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `covariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono α`,
    expressing that multiplication by positive elements on the left is monotone;
* * `covariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_strict_mono α`,
    expressing that multiplication by positive elements on the left is strictly monotone;
* monotone right
* * `covariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono α`,
    expressing that multiplication by positive elements on the right is monotone;
* * `covariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_strict_mono α`,
    expressing that multiplication by positive elements on the right is strictly monotone.
* reverse monotone left
* * `contravariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono_rev α`,
    expressing that multiplication by positive elements on the left is reverse monotone;
* * `contravariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_reflect_lt α`,
    expressing that multiplication by positive elements on the left is strictly reverse monotone;
* reverse reverse monotone right
* * `contravariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono_rev α`,
    expressing that multiplication by positive elements on the right is reverse monotone;
* * `contravariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_reflect_lt α`,
    expressing that multiplication by positive elements on the right is strictly reverse monotone.

##  Formalization comments

We use `α>0 = {x : α // 0 < x}` with a strict inequality since in most cases what happens with `0`
is clear.  This creates a few bumps in the first couple of proofs, where we have to split cases on
whether an element is `0` or not, but goes smoothly after that.  A further advantage is that we
only introduce notation for the positive elements and we do not need also the non-negative ones.

Some lemmas for `partial_order` also have a variant for `preorder`, where the `preorder` version has
stronger hypotheses.  In this case we put the `preorder` lemma in the `preorder` namespace.
-/


/- I am changing the file `algebra/order/monoid_lemmas` incrementally, with the idea of
reproducing almost all of the proofs in `algebra/order/ring` with weaker assumptions. -/
universe u

variable {α : Type u}

-- mathport name: «exprα>0»
/-  Notation for positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation "α>0" => { x : α // 0 < x }

namespace ZeroLt

section AbbreviationsStrictMono

variable (X : Type u) [Mul X] [Zero X] [LT X]

/-- `zero_lt.pos_mul_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => x * y) (· < ·)

/-- `zero_lt.mul_pos_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => y * x) (· < ·)

/-- `zero_lt.pos_mul_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly reverse monotone. -/
abbrev PosMulReflectLt : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => x * y) (· < ·)

/-- `zero_lt.mul_pos_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly reverse monotone. -/
abbrev MulPosReflectLt : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => y * x) (· < ·)

end AbbreviationsStrictMono

section AbbreviationsMono

variable (X : Type _) [Mul X] [Zero X] [LT X] [LE X]

/-- `zero_lt.pos_mul_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is monotone. -/
abbrev PosMulMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => x * y) (· ≤ ·)

/-- `zero_lt.mul_pos_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is monotone. -/
abbrev MulPosMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => y * x) (· ≤ ·)

/-- `zero_lt.pos_mul_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbrev PosMulMonoRev : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => x * y) (· ≤ ·)

/-- `zero_lt.mul_pos_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbrev MulPosMonoRev : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => y * x) (· ≤ ·)

end AbbreviationsMono

variable {a b c d : α}

section HasMulZero

variable [Mul α] [Zero α]

section LT

variable [LT α]

theorem mul_lt_mul_left' [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

theorem mul_lt_mul_right' [MulPosStrictMono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left`
theorem lt_of_mul_lt_mul_left' [PosMulReflectLt α] (bc : a * b < a * c) (a0 : 0 < a) : b < c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right`
theorem lt_of_mul_lt_mul_right' [MulPosReflectLt α] (bc : b * a < c * a) (a0 : 0 < a) : b < c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

@[simp]
theorem mul_lt_mul_iff_left [PosMulStrictMono α] [PosMulReflectLt α] (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_lt_mul_iff_right [MulPosStrictMono α] [MulPosReflectLt α] (a0 : 0 < a) : b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _

end LT

section HasLtLe

variable [LT α] [LE α]

-- proven with `a0 : 0 ≤ a` as `mul_le_mul_left`
theorem mul_le_mul_left' [PosMulMono α] (bc : b ≤ c) (a0 : 0 < a) : a * b ≤ a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `mul_le_mul_right`
theorem mul_le_mul_right' [MulPosMono α] (bc : b ≤ c) (a0 : 0 < a) : b * a ≤ c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

theorem le_of_mul_le_mul_left' [PosMulMonoRev α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

theorem le_of_mul_le_mul_right' [MulPosMonoRev α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc

@[simp]
theorem mul_le_mul_iff_left [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_le_mul_iff_right [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _

end HasLtLe

section Preorderₓ

variable [Preorderₓ α]

-- proven with `a0 : 0 ≤ a` `d0 : 0 ≤ d` as `mul_le_mul_of_le_of_le`
theorem Preorder.mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 < a)
    (d0 : 0 < d) : a * c ≤ b * d :=
  (mul_le_mul_left' h₂ a0).trans (mul_le_mul_right' h₁ d0)

-- proven with `b0 : 0 ≤ b` `c0 : 0 ≤ c` as `mul_le_mul_of_le_of_le'`
theorem Preorder.mul_le_mul_of_le_of_le' [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (b0 : 0 < b)
    (c0 : 0 < c) : a * c ≤ b * d :=
  (mul_le_mul_right' h₁ c0).trans (mul_le_mul_left' h₂ b0)

theorem mul_lt_mul_of_le_of_lt [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c < b * d :=
  (mul_lt_mul_left' h₂ a0).trans_le (mul_le_mul_right' h₁ d0)

theorem mul_lt_mul_of_le_of_lt' [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d) (b0 : 0 < b)
    (c0 : 0 < c) : a * c < b * d :=
  (mul_le_mul_right' h₁ c0).trans_lt (mul_lt_mul_left' h₂ b0)

theorem mul_lt_mul_of_lt_of_le [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c < b * d :=
  (mul_le_mul_left' h₂ a0).trans_lt (mul_lt_mul_right' h₁ d0)

theorem mul_lt_mul_of_lt_of_le' [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d) (b0 : 0 < b)
    (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_right' h₁ c0).trans_le (mul_le_mul_left' h₂ b0)

theorem mul_lt_mul_of_lt_of_lt [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d) (a0 : 0 < a)
    (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_left' h₂ a0).trans (mul_lt_mul_right' h₁ d0)

theorem mul_lt_mul_of_lt_of_lt' [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d) (b0 : 0 < b)
    (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_right' h₁ c0).trans (mul_lt_mul_left' h₂ b0)

-- proven with `a0 : 0 ≤ a` as `mul_le_of_mul_le_left`
theorem Preorder.mul_le_of_mul_le_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 < a) : a * d ≤ c :=
  (mul_le_mul_left' hle a0).trans h

theorem mul_lt_of_mul_lt_left [PosMulMono α] (h : a * b < c) (hle : d ≤ b) (a0 : 0 < a) : a * d < c :=
  (mul_le_mul_left' hle a0).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_mul_of_le_mul_left`
theorem Preorder.le_mul_of_le_mul_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 < b) : a ≤ b * d :=
  h.trans (mul_le_mul_left' hle b0)

theorem lt_mul_of_lt_mul_left [PosMulMono α] (h : a < b * c) (hle : c ≤ d) (b0 : 0 < b) : a < b * d :=
  h.trans_le (mul_le_mul_left' hle b0)

-- proven with `b0 : 0 ≤ b` as `mul_le_of_mul_le_right`
theorem Preorder.mul_le_of_mul_le_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 < b) : d * b ≤ c :=
  (mul_le_mul_right' hle b0).trans h

theorem mul_lt_of_mul_lt_right [MulPosMono α] (h : a * b < c) (hle : d ≤ a) (b0 : 0 < b) : d * b < c :=
  (mul_le_mul_right' hle b0).trans_lt h

-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_mul_right`
theorem Preorder.le_mul_of_le_mul_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 < c) : a ≤ d * c :=
  h.trans (mul_le_mul_right' hle c0)

theorem lt_mul_of_lt_mul_right [MulPosMono α] (h : a < b * c) (hle : b ≤ d) (c0 : 0 < c) : a < d * c :=
  h.trans_le (mul_le_mul_right' hle c0)

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.to_pos_mul_mono [PosMulStrictMono α] : PosMulMono α :=
  ⟨fun x a b h => h.eq_or_lt.elim (fun h' => h' ▸ le_rfl) fun h' => (mul_lt_mul_left' h' x.Prop).le⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.to_mul_pos_mono [MulPosStrictMono α] : MulPosMono α :=
  ⟨fun x a b h => h.eq_or_lt.elim (fun h' => h' ▸ le_rfl) fun h' => (mul_lt_mul_right' h' x.Prop).le⟩

-- see Note [lower instance priority]
instance (priority := 100) PosMulMonoRev.to_pos_mul_reflect_lt [PosMulMonoRev α] : PosMulReflectLt α :=
  ⟨fun x a b h =>
    lt_of_le_of_neₓ (le_of_mul_le_mul_left' h.le x.Prop) fun h' => by
      simpa [← h'] using h⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosMonoRev.to_mul_pos_reflect_lt [MulPosMonoRev α] : MulPosReflectLt α :=
  ⟨fun x a b h =>
    lt_of_le_of_neₓ (le_of_mul_le_mul_right' h.le x.Prop) fun h' => by
      simpa [← h'] using h⟩

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.to_pos_mul_mono_rev [PosMulStrictMono α] : PosMulMonoRev α :=
  ⟨fun x a b h => le_of_not_ltₓ fun h' => h.not_lt (mul_lt_mul_left' h' x.Prop)⟩

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.to_mul_pos_mono_rev [MulPosStrictMono α] : MulPosMonoRev α :=
  ⟨fun x a b h => le_of_not_ltₓ fun h' => h.not_lt (mul_lt_mul_right' h' x.Prop)⟩

theorem PosMulMonoRev.to_pos_mul_strict_mono [PosMulMonoRev α] : PosMulStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le (le_of_mul_le_mul_left' h' x.Prop)⟩

theorem MulPosMonoRev.to_mul_pos_strict_mono [MulPosMonoRev α] : MulPosStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le (le_of_mul_le_mul_right' h' x.Prop)⟩

theorem pos_mul_strict_mono_iff_pos_mul_mono_rev : PosMulStrictMono α ↔ PosMulMonoRev α :=
  ⟨@ZeroLt.PosMulStrictMono.to_pos_mul_mono_rev _ _ _ _, @PosMulMonoRev.to_pos_mul_strict_mono _ _ _ _⟩

theorem mul_pos_strict_mono_iff_mul_pos_mono_rev : MulPosStrictMono α ↔ MulPosMonoRev α :=
  ⟨@ZeroLt.MulPosStrictMono.to_mul_pos_mono_rev _ _ _ _, @MulPosMonoRev.to_mul_pos_strict_mono _ _ _ _⟩

theorem PosMulReflectLt.to_pos_mul_mono [PosMulReflectLt α] : PosMulMono α :=
  ⟨fun x a b h => le_of_not_ltₓ fun h' => h.not_lt (lt_of_mul_lt_mul_left' h' x.Prop)⟩

theorem MulPosReflectLt.to_mul_pos_mono [MulPosReflectLt α] : MulPosMono α :=
  ⟨fun x a b h => le_of_not_ltₓ fun h' => h.not_lt (lt_of_mul_lt_mul_right' h' x.Prop)⟩

theorem PosMulMono.to_pos_mul_reflect_lt [PosMulMono α] : PosMulReflectLt α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le (mul_le_mul_left' h' x.Prop)⟩

theorem MulPosMono.to_mul_pos_reflect_lt [MulPosMono α] : MulPosReflectLt α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le (mul_le_mul_right' h' x.Prop)⟩

theorem pos_mul_mono_iff_pos_mul_reflect_lt : PosMulMono α ↔ PosMulReflectLt α :=
  ⟨@PosMulMono.to_pos_mul_reflect_lt _ _ _ _, @PosMulReflectLt.to_pos_mul_mono _ _ _ _⟩

theorem mul_pos_mono_iff_mul_pos_reflect_lt : MulPosMono α ↔ MulPosReflectLt α :=
  ⟨@MulPosMono.to_mul_pos_reflect_lt _ _ _ _, @MulPosReflectLt.to_mul_pos_mono _ _ _ _⟩

end LinearOrderₓ

end HasMulZero

section MulZeroClassₓ

variable [MulZeroClassₓ α]

section Preorderₓ

variable [Preorderₓ α]

/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h : a * 0 < a * b := mul_lt_mul_left' hb ha
  rwa [mul_zero] at h

theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  have h : a * b < a * 0 := mul_lt_mul_left' hb ha
  rwa [mul_zero] at h

/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  have h : 0 * b < a * b := mul_lt_mul_right' ha hb
  rwa [zero_mul] at h

theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have h : a * b < 0 * b := mul_lt_mul_right' ha hb
  rwa [zero_mul] at h

end Preorderₓ

section PartialOrderₓ

variable [PartialOrderₓ α]

theorem mul_le_mul_left [PosMulMono α] (bc : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  a0.lt_or_eq.elim (mul_le_mul_left' bc) fun h => by
    simp only [h, ← zero_mul]

theorem mul_le_mul_right [MulPosMono α] (bc : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  a0.lt_or_eq.elim (mul_le_mul_right' bc) fun h => by
    simp only [h, ← mul_zero]

/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h : a * 0 ≤ a * b := mul_le_mul_left hb ha
  rwa [mul_zero] at h

theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  have h : a * b ≤ a * 0 := mul_le_mul_left hb ha
  rwa [mul_zero] at h

/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  have h : 0 * b ≤ a * b := mul_le_mul_right ha hb
  rwa [zero_mul] at h

theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  have h : a * b ≤ 0 * b := mul_le_mul_right ha hb
  rwa [zero_mul] at h

theorem lt_of_mul_lt_mul_left [PosMulReflectLt α] (bc : a * b < a * c) (a0 : 0 ≤ a) : b < c := by
  by_cases' a₀ : a = 0
  · exact
      (lt_irreflₓ (0 : α)
          (by
            simpa only [← a₀, ← zero_mul] using bc)).elim
    
  · exact lt_of_mul_lt_mul_left' bc ((Ne.symm a₀).le_iff_lt.mp a0)
    

theorem pos_of_mul_pos_right [PosMulReflectLt α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha

theorem lt_of_mul_lt_mul_right [MulPosReflectLt α] (bc : b * a < c * a) (a0 : 0 ≤ a) : b < c := by
  by_cases' a₀ : a = 0
  · exact
      (lt_irreflₓ (0 : α)
          (by
            simpa only [← a₀, ← mul_zero] using bc)).elim
    
  · exact lt_of_mul_lt_mul_right' bc ((Ne.symm a₀).le_iff_lt.mp a0)
    

theorem pos_of_mul_pos_left [MulPosReflectLt α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb

theorem pos_iff_pos_of_mul_pos [PosMulReflectLt α] [MulPosReflectLt α] (hab : 0 < a * b) : 0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_ltₓ, pos_of_mul_pos_left hab ∘ le_of_ltₓ⟩

theorem mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a) (d0 : 0 ≤ d) :
    a * c ≤ b * d :=
  (mul_le_mul_left h₂ a0).trans <| mul_le_mul_right h₁ d0

theorem mul_le_mul_of_le_of_le' [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (b0 : 0 ≤ b) (c0 : 0 ≤ c) :
    a * c ≤ b * d :=
  (mul_le_mul_right h₁ c0).trans <| mul_le_mul_left h₂ b0

theorem mul_le_of_mul_le_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) : a * d ≤ c :=
  (mul_le_mul_left hle a0).trans h

theorem le_mul_of_le_mul_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) : a ≤ b * d :=
  h.trans (mul_le_mul_left hle b0)

theorem mul_le_of_mul_le_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) : d * b ≤ c :=
  (mul_le_mul_right hle b0).trans h

theorem le_mul_of_le_mul_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) : a ≤ d * c :=
  h.trans (mul_le_mul_right hle c0)

theorem mul_left_cancel_iff [PosMulMonoRev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_left' h.le a0).antisymm (le_of_mul_le_mul_left' h.Ge a0), congr_arg _⟩

theorem mul_right_cancel_iff [MulPosMonoRev α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h => (le_of_mul_le_mul_right' h.le b0).antisymm (le_of_mul_le_mul_right' h.Ge b0), congr_arg _⟩

theorem mul_eq_mul_iff_eq_and_eq [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α] [MulPosMonoRev α]
    (hac : a ≤ b) (hbd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) : a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg2ₓ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iffₓ a0).mp h⟩
    
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iffₓ d0).mp h, rfl⟩
    
  exact ((mul_lt_mul_of_lt_of_lt hac hbd a0 d0).Ne h).elim

theorem mul_eq_mul_iff_eq_and_eq' [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α] [MulPosMonoRev α]
    (hac : a ≤ b) (hbd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) : a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg2ₓ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iffₓ b0).mp h⟩
    
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iffₓ c0).mp h, rfl⟩
    
  exact ((mul_lt_mul_of_lt_of_lt' hac hbd b0 c0).Ne h).elim

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomyₓ 0 a with (ha | rfl | ha)
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
    
  · rw [zero_mul] at hab
    exact hab.false.elim
    
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
    

theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2

theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1

theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_ltₓ, neg_of_mul_pos_left hab ∘ le_of_ltₓ⟩

theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_geₓ fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h

theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_geₓ fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h

theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_geₓ fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h

theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_geₓ fun h2 : a ≥ 0 => (Right.mul_nonneg h2 h1).not_lt h

end LinearOrderₓ

end MulZeroClassₓ

section MulOneClassₓ

variable [MulOneClassₓ α] [Zero α]

section Preorderₓ

variable [Preorderₓ α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/


@[simp]
theorem le_mul_iff_one_le_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_le_mul_iff_left a0)

@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLt α] (a0 : 0 < a) : a < a * b ↔ 1 < b :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_lt_mul_iff_left a0)

@[simp]
theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_le_mul_iff_left a0)

@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLt α] (a0 : 0 < a) : a * b < a ↔ b < 1 :=
  Iff.trans
    (by
      rw [mul_oneₓ])
    (mul_lt_mul_iff_left a0)

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


@[simp]
theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_le_mul_iff_right a0)

@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLt α] (a0 : 0 < a) : a < b * a ↔ 1 < b :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_lt_mul_iff_right a0)

@[simp]
theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosMonoRev α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_le_mul_iff_right b0)

@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLt α] (b0 : 0 < b) : a * b < b ↔ a < 1 :=
  Iff.trans
    (by
      rw [one_mulₓ])
    (mul_lt_mul_iff_right b0)

/-! Lemmas of the form `b ≤ c → a ≤ 1 → 0 < b → b * a ≤ c`,
which assume left covariance. -/


-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_of_le_one`
theorem Preorder.mul_le_of_le_of_le_one [PosMulMono α] (bc : b ≤ c) (ha : a ≤ 1) (b0 : 0 < b) : b * a ≤ c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b0
    _ = b := mul_oneₓ b
    _ ≤ c := bc
    

theorem mul_lt_of_le_of_lt_one [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b0
    _ = b := mul_oneₓ b
    _ ≤ c := bc
    

theorem mul_lt_of_lt_of_le_one [PosMulMono α] (bc : b < c) (ha : a ≤ 1) (b0 : 0 < b) : b * a < c :=
  calc
    b * a ≤ b * 1 := mul_le_mul_left' ha b0
    _ = b := mul_oneₓ b
    _ < c := bc
    

theorem mul_lt_of_lt_of_lt_one [PosMulStrictMono α] (bc : b < c) (ha : a < 1) (b0 : 0 < b) : b * a < c :=
  calc
    b * a < b * 1 := mul_lt_mul_left' ha b0
    _ = b := mul_oneₓ b
    _ < c := bc
    

/-- Assumes left covariance. -/
-- proven with `a0 : 0 ≤ a` as `left.mul_le_one_of_le_of_le`
theorem Preorder.Left.mul_le_one_of_le_of_le' [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 < a) : a * b ≤ 1 :=
  Preorder.mul_le_of_le_of_le_one ha hb a0

/-- Assumes left covariance. -/
theorem Left.mul_lt_one_of_le_of_lt [PosMulStrictMono α] (ha : a ≤ 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
  mul_lt_of_le_of_lt_one ha hb a0

/-- Assumes left covariance. -/
theorem Left.mul_lt_one_of_lt_of_le [PosMulMono α] (ha : a < 1) (hb : b ≤ 1) (a0 : 0 < a) : a * b < 1 :=
  mul_lt_of_lt_of_le_one ha hb a0

/-- Assumes left covariance. -/
theorem Left.mul_lt_one_of_lt_of_lt [PosMulStrictMono α] (ha : a < 1) (hb : b < 1) (a0 : 0 < a) : a * b < 1 :=
  mul_lt_of_lt_of_lt_one ha hb a0

/-! Lemmas of the form `b ≤ c → 1 ≤ a → 0 < c → b ≤ c * a`,
which assume left covariance. -/


-- proven with `c0 : 0 ≤ c` as `le_mul_of_le_of_one_le`
theorem Preorder.le_mul_of_le_of_one_le [PosMulMono α] (bc : b ≤ c) (ha : 1 ≤ a) (c0 : 0 < c) : b ≤ c * a :=
  calc
    b ≤ c := bc
    _ = c * 1 := (mul_oneₓ c).symm
    _ ≤ c * a := mul_le_mul_left' ha c0
    

theorem lt_mul_of_le_of_one_lt [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) : b < c * a :=
  calc
    b ≤ c := bc
    _ = c * 1 := (mul_oneₓ c).symm
    _ < c * a := mul_lt_mul_left' ha c0
    

theorem lt_mul_of_lt_of_one_le [PosMulMono α] (bc : b < c) (ha : 1 ≤ a) (c0 : 0 < c) : b < c * a :=
  calc
    b < c := bc
    _ = c * 1 := (mul_oneₓ c).symm
    _ ≤ c * a := mul_le_mul_left' ha c0
    

theorem lt_mul_of_lt_of_one_lt [PosMulStrictMono α] (bc : b < c) (ha : 1 < a) (c0 : 0 < c) : b < c * a :=
  calc
    b < c := bc
    _ = c * 1 := (mul_oneₓ _).symm
    _ < c * a := mul_lt_mul_left' ha c0
    

/-- Assumes left covariance. -/
-- proven with `a0 : 0 ≤ a` as `left.one_le_mul_of_le_of_le`
theorem Preorder.Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 < a) : 1 ≤ a * b :=
  Preorder.le_mul_of_le_of_one_le ha hb a0

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_le_of_lt [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b) (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_le_of_one_lt ha hb a0

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_lt_of_le [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b) (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_lt_of_one_le ha hb a0

/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_lt_of_lt [PosMulStrictMono α] (ha : 1 < a) (hb : 1 < b) (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_lt_of_one_lt ha hb a0

/-! Lemmas of the form `a ≤ 1 → b ≤ c → 0 < b → a * b ≤ c`,
which assume right covariance. -/


-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_of_le`
theorem Preorder.mul_le_of_le_one_of_le [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (b0 : 0 < b) : a * b ≤ c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b0
    _ = b := one_mulₓ b
    _ ≤ c := bc
    

theorem mul_lt_of_lt_one_of_le [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c) (b0 : 0 < b) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b0
    _ = b := one_mulₓ b
    _ ≤ c := bc
    

theorem mul_lt_of_le_one_of_lt [MulPosMono α] (ha : a ≤ 1) (hb : b < c) (b0 : 0 < b) : a * b < c :=
  calc
    a * b ≤ 1 * b := mul_le_mul_right' ha b0
    _ = b := one_mulₓ b
    _ < c := hb
    

theorem mul_lt_of_lt_one_of_lt [MulPosStrictMono α] (ha : a < 1) (bc : b < c) (b0 : 0 < b) : a * b < c :=
  calc
    a * b < 1 * b := mul_lt_mul_right' ha b0
    _ = b := one_mulₓ b
    _ < c := bc
    

/-- Assumes right covariance. -/
-- proven with `b0 : 0 ≤ b` as `right.mul_le_one_of_le_of_le`
theorem Preorder.Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b ≤ 1 :=
  Preorder.mul_le_of_le_one_of_le ha hb b0

/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_lt_of_le [MulPosStrictMono α] (ha : a < 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_le ha hb b0

/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_le_of_lt [MulPosMono α] (ha : a ≤ 1) (hb : b < 1) (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_le_one_of_lt ha hb b0

/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_lt_of_lt [MulPosStrictMono α] (ha : a < 1) (hb : b < 1) (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_lt ha hb b0

/-! Lemmas of the form `1 ≤ a → b ≤ c → 0 < c → b ≤ a * c`,
which assume right covariance. -/


-- proven with `c0 : 0 ≤ c` as `le_mul_of_one_le_of_le`
theorem Preorder.le_mul_of_one_le_of_le [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 < c) : b ≤ a * c :=
  calc
    b ≤ c := bc
    _ = 1 * c := (one_mulₓ c).symm
    _ ≤ a * c := mul_le_mul_right' ha c0
    

theorem lt_mul_of_one_lt_of_le [MulPosStrictMono α] (ha : 1 < a) (bc : b ≤ c) (c0 : 0 < c) : b < a * c :=
  calc
    b ≤ c := bc
    _ = 1 * c := (one_mulₓ c).symm
    _ < a * c := mul_lt_mul_right' ha c0
    

theorem lt_mul_of_one_le_of_lt [MulPosMono α] (ha : 1 ≤ a) (bc : b < c) (c0 : 0 < c) : b < a * c :=
  calc
    b < c := bc
    _ = 1 * c := (one_mulₓ c).symm
    _ ≤ a * c := mul_le_mul_right' ha c0
    

theorem lt_mul_of_one_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (bc : b < c) (c0 : 0 < c) : b < a * c :=
  calc
    b < c := bc
    _ = 1 * c := (one_mulₓ c).symm
    _ < a * c := mul_lt_mul_right' ha c0
    

/-- Assumes right covariance. -/
-- proven with `b0 : 0 ≤ b` as `right.one_le_mul_of_le_of_le`
theorem Preorder.Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 < b) : 1 ≤ a * b :=
  Preorder.le_mul_of_one_le_of_le ha hb b0

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_le [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b) (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le ha hb b0

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_le_of_lt [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b) (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt ha hb b0

/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_lt ha hb b0

-- proven with `a0 : 0 ≤ a` as `mul_le_of_le_one_right`
theorem Preorder.mul_le_of_le_one_right [PosMulMono α] (h : b ≤ 1) (a0 : 0 < a) : a * b ≤ a :=
  Preorder.mul_le_of_le_of_le_one le_rfl h a0

-- proven with `a0 : 0 ≤ a` as `le_mul_of_one_le_right`
theorem Preorder.le_mul_of_one_le_right [PosMulMono α] (h : 1 ≤ b) (a0 : 0 < a) : a ≤ a * b :=
  Preorder.le_mul_of_le_of_one_le le_rfl h a0

-- proven with `b0 : 0 ≤ b` as `mul_le_of_le_one_left`
theorem Preorder.mul_le_of_le_one_left [MulPosMono α] (h : a ≤ 1) (b0 : 0 < b) : a * b ≤ b :=
  Preorder.mul_le_of_le_one_of_le h le_rfl b0

-- proven with `b0 : 0 ≤ b` as `le_mul_of_one_le_left`
theorem Preorder.le_mul_of_one_le_left [MulPosMono α] (h : 1 ≤ a) (b0 : 0 < b) : b ≤ a * b :=
  Preorder.le_mul_of_one_le_of_le h le_rfl b0

theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (h : b < 1) (a0 : 0 < a) : a * b < a :=
  mul_lt_of_le_of_lt_one le_rfl h a0

theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (h : 1 < b) (a0 : 0 < a) : a < a * b :=
  lt_mul_of_le_of_one_lt le_rfl h a0

theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (h : a < 1) (b0 : 0 < b) : a * b < b :=
  mul_lt_of_lt_one_of_le h le_rfl b0

theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (h : 1 < a) (b0 : 0 < b) : b < a * b :=
  lt_mul_of_one_lt_of_le h le_rfl b0

-- proven with `a0 : 0 ≤ a` as `le_of_mul_le_of_one_le_left`
theorem Preorder.le_of_mul_le_of_one_le_left [PosMulMono α] (h : a * b ≤ c) (hle : 1 ≤ b) (a0 : 0 < a) : a ≤ c :=
  (Preorder.le_mul_of_one_le_right hle a0).trans h

theorem lt_of_mul_lt_of_one_le_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b) (a0 : 0 < a) : a < c :=
  (Preorder.le_mul_of_one_le_right hle a0).trans_lt h

-- proven with `b0 : 0 ≤ b` as `le_of_le_mul_of_le_one_left`
theorem Preorder.le_of_le_mul_of_le_one_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ 1) (b0 : 0 < b) : a ≤ b :=
  h.trans (Preorder.mul_le_of_le_one_right hle b0)

theorem lt_of_lt_mul_of_le_one_left [PosMulMono α] (h : a < b * c) (hle : c ≤ 1) (b0 : 0 < b) : a < b :=
  h.trans_le (Preorder.mul_le_of_le_one_right hle b0)

-- proven with `b0 : 0 ≤ b` as `le_of_mul_le_of_one_le_right`
theorem Preorder.le_of_mul_le_of_one_le_right [MulPosMono α] (h : a * b ≤ c) (hle : 1 ≤ a) (b0 : 0 < b) : b ≤ c :=
  (Preorder.le_mul_of_one_le_left hle b0).trans h

theorem lt_of_mul_lt_of_one_le_right [MulPosMono α] (h : a * b < c) (hle : 1 ≤ a) (b0 : 0 < b) : b < c :=
  (Preorder.le_mul_of_one_le_left hle b0).trans_lt h

-- proven with `c0 : 0 ≤ b` as `le_of_le_mul_of_le_one_right`
theorem Preorder.le_of_le_mul_of_le_one_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ 1) (c0 : 0 < c) : a ≤ c :=
  h.trans (Preorder.mul_le_of_le_one_left hle c0)

theorem lt_of_lt_mul_of_le_one_right [MulPosMono α] (h : a < b * c) (hle : b ≤ 1) (c0 : 0 < c) : a < c :=
  h.trans_le (Preorder.mul_le_of_le_one_left hle c0)

end Preorderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

-- proven with `a0 : 0 ≤ a` as `exists_square_le`
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a := by
  by_cases' h : a < 1
  · use a
    have : a * a < a * 1 := mul_lt_mul_left' h a0
    rw [mul_oneₓ] at this
    exact le_of_ltₓ this
    
  · use 1
    push_neg  at h
    rwa [mul_oneₓ]
    

end LinearOrderₓ

end MulOneClassₓ

section MulZeroOneClassₓ

variable [MulZeroOneClassₓ α]

section PartialOrderₓ

variable [PartialOrderₓ α]

theorem mul_le_of_le_of_le_one [PosMulMono α] (bc : b ≤ c) (ha : a ≤ 1) (b0 : 0 ≤ b) : b * a ≤ c :=
  b0.lt_or_eq.elim (Preorder.mul_le_of_le_of_le_one bc ha) fun h => by
    rw [← h, zero_mul] <;> exact b0.trans bc

/-- Assumes left covariance. -/
theorem Left.mul_le_one_of_le_of_le [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) : a * b ≤ 1 :=
  mul_le_of_le_of_le_one ha hb a0

theorem le_mul_of_le_of_one_le [PosMulMono α] (bc : b ≤ c) (ha : 1 ≤ a) (c0 : 0 ≤ c) : b ≤ c * a :=
  c0.lt_or_eq.elim (Preorder.le_mul_of_le_of_one_le bc ha) fun h => by
    rw [← h, zero_mul] at * <;> exact bc

/-- Assumes left covariance. -/
theorem Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) : 1 ≤ a * b :=
  le_mul_of_le_of_one_le ha hb a0

theorem mul_le_of_le_one_of_le [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (b0 : 0 ≤ b) : a * b ≤ c :=
  b0.lt_or_eq.elim (Preorder.mul_le_of_le_one_of_le ha bc) fun h => by
    rw [← h, mul_zero] at * <;> exact bc

/-- Assumes right covariance. -/
theorem Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 < b) : a * b ≤ 1 :=
  Preorder.mul_le_of_le_one_of_le ha hb b0

theorem le_mul_of_one_le_of_le [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) : b ≤ a * c :=
  c0.lt_or_eq.elim (Preorder.le_mul_of_one_le_of_le ha bc) fun h => by
    rw [← h, mul_zero] at * <;> exact bc

/-- Assumes right covariance. -/
theorem Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) : 1 ≤ a * b :=
  le_mul_of_one_le_of_le ha hb b0

theorem mul_le_of_le_one_right [PosMulMono α] (h : b ≤ 1) (a0 : 0 ≤ a) : a * b ≤ a :=
  mul_le_of_le_of_le_one le_rfl h a0

theorem le_mul_of_one_le_right [PosMulMono α] (h : 1 ≤ b) (a0 : 0 ≤ a) : a ≤ a * b :=
  le_mul_of_le_of_one_le le_rfl h a0

theorem mul_le_of_le_one_left [MulPosMono α] (h : a ≤ 1) (b0 : 0 ≤ b) : a * b ≤ b :=
  mul_le_of_le_one_of_le h le_rfl b0

theorem le_mul_of_one_le_left [MulPosMono α] (h : 1 ≤ a) (b0 : 0 ≤ b) : b ≤ a * b :=
  le_mul_of_one_le_of_le h le_rfl b0

theorem le_of_mul_le_of_one_le_left [PosMulMono α] (h : a * b ≤ c) (hle : 1 ≤ b) (a0 : 0 ≤ a) : a ≤ c :=
  a0.lt_or_eq.elim (Preorder.le_of_mul_le_of_one_le_left h hle) fun ha => by
    simpa only [ha, ← zero_mul] using h

theorem le_of_le_mul_of_le_one_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ 1) (b0 : 0 ≤ b) : a ≤ b :=
  b0.lt_or_eq.elim (Preorder.le_of_le_mul_of_le_one_left h hle) fun hb => by
    simpa only [hb, ← zero_mul] using h

theorem le_of_mul_le_of_one_le_right [MulPosMono α] (h : a * b ≤ c) (hle : 1 ≤ a) (b0 : 0 ≤ b) : b ≤ c :=
  b0.lt_or_eq.elim (Preorder.le_of_mul_le_of_one_le_right h hle) fun ha => by
    simpa only [ha, ← mul_zero] using h

theorem le_of_le_mul_of_le_one_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ 1) (c0 : 0 ≤ c) : a ≤ c :=
  c0.lt_or_eq.elim (Preorder.le_of_le_mul_of_le_one_right h hle) fun ha => by
    simpa only [ha, ← mul_zero] using h

end PartialOrderₓ

section LinearOrderₓ

variable [LinearOrderₓ α]

theorem exists_square_le [PosMulStrictMono α] (a0 : 0 ≤ a) : ∃ b : α, b * b ≤ a :=
  a0.lt_or_eq.elim exists_square_le' fun h => by
    rw [← h] <;>
      exact
        ⟨0, by
          simp ⟩

end LinearOrderₓ

end MulZeroOneClassₓ

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrderₓ

variable [PartialOrderₓ α]

theorem PosMulMono.to_pos_mul_strict_mono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x a b h => lt_of_le_of_neₓ (mul_le_mul_left' h.le x.2) (h.Ne ∘ mul_left_cancel₀ x.2.Ne.symm)⟩

theorem pos_mul_mono_iff_pos_mul_strict_mono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.to_pos_mul_strict_mono α _ _, @ZeroLt.PosMulStrictMono.to_pos_mul_mono α _ _ _⟩

theorem MulPosMono.to_mul_pos_strict_mono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x a b h => lt_of_le_of_neₓ (mul_le_mul_right' h.le x.2) (h.Ne ∘ mul_right_cancel₀ x.2.Ne.symm)⟩

theorem mul_pos_mono_iff_mul_pos_strict_mono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.to_mul_pos_strict_mono α _ _, @ZeroLt.MulPosStrictMono.to_mul_pos_mono α _ _ _⟩

theorem PosMulReflectLt.to_pos_mul_mono_rev [PosMulReflectLt α] : PosMulMonoRev α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eqₓ ∘ mul_left_cancel₀ x.2.Ne.symm) fun h' => (lt_of_mul_lt_mul_left' h' x.2).le⟩

theorem pos_mul_mono_rev_iff_pos_mul_reflect_lt : PosMulMonoRev α ↔ PosMulReflectLt α :=
  ⟨@ZeroLt.PosMulMonoRev.to_pos_mul_reflect_lt α _ _ _, @PosMulReflectLt.to_pos_mul_mono_rev α _ _⟩

theorem MulPosReflectLt.to_mul_pos_mono_rev [MulPosReflectLt α] : MulPosMonoRev α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eqₓ ∘ mul_right_cancel₀ x.2.Ne.symm) fun h' => (lt_of_mul_lt_mul_right' h' x.2).le⟩

theorem mul_pos_mono_rev_iff_mul_pos_reflect_lt : MulPosMonoRev α ↔ MulPosReflectLt α :=
  ⟨@ZeroLt.MulPosMonoRev.to_mul_pos_reflect_lt α _ _ _, @MulPosReflectLt.to_mul_pos_mono_rev α _ _⟩

end PartialOrderₓ

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [CommSemigroupₓ α] [Zero α]

variable [LT α]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem pos_mul_strict_mono_iff_mul_pos_strict_mono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp only [← mul_comm]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem pos_mul_reflect_lt_iff_mul_pos_reflect_lt : PosMulReflectLt α ↔ MulPosReflectLt α := by
  simp only [← mul_comm]

variable [LE α]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem pos_mul_mono_iff_mul_pos_mono : PosMulMono α ↔ MulPosMono α := by
  simp only [← mul_comm]

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:353:22: warning: unsupported simp config option: iota_eqn
theorem pos_mul_mono_rev_iff_mul_pos_mono_rev : PosMulMonoRev α ↔ MulPosMonoRev α := by
  simp only [← mul_comm]

end CommSemigroupHasZero

end ZeroLt

