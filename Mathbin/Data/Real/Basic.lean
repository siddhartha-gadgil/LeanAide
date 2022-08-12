/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Algebra.Bounds
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Real.CauSeqCompletion
import Mathbin.Order.ConditionallyCompleteLattice

/-!
# Real numbers from Cauchy sequences

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/


open Pointwise

/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where of_cauchy ::
  cauchy : @CauSeq.Completion.Cauchy ℚ _ _ _ abs _

-- mathport name: «exprℝ»
notation "ℝ" => Real

attribute [pp_using_anonymous_constructor] Real

namespace Real

open CauSeq CauSeq.Completion

variable {x y : ℝ}

theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    constructor <;> cc

theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2

/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy :=
  ⟨Real.cauchy, Real.of_cauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : ℝ :=
  ⟨0⟩

private irreducible_def one : ℝ :=
  ⟨1⟩

private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩

private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩

private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩

instance : Zero ℝ :=
  ⟨zero⟩

instance : One ℝ :=
  ⟨one⟩

instance : Add ℝ :=
  ⟨add⟩

instance : Neg ℝ :=
  ⟨neg⟩

instance : Mul ℝ :=
  ⟨mul⟩

theorem of_cauchy_zero : (⟨0⟩ : ℝ) = 0 :=
  show _ = zero by
    rw [zero]

theorem of_cauchy_one : (⟨1⟩ : ℝ) = 1 :=
  show _ = one by
    rw [one]

theorem of_cauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by
    rw [add]

theorem of_cauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  show _ = neg _ by
    rw [neg]

theorem of_cauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by
    rw [mul]

theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by
    rw [zero]

theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by
    rw [one]

theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ =>
    show (add _ _).cauchy = _ by
      rw [add]

theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ =>
    show (neg _).cauchy = _ by
      rw [neg]

theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ =>
    show (mul _ _).cauchy = _ by
      rw [mul]

instance : CommRingₓ ℝ := by
  refine_struct
      { zero := (0 : ℝ), one := (1 : ℝ), mul := (· * ·), add := (· + ·), neg := @Neg.neg ℝ _, sub := fun a b => a + -b,
        natCast := fun n => ⟨n⟩, intCast := fun n => ⟨n⟩, npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩,
        nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩, zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ } <;>
    repeat'
        rintro ⟨_⟩ <;>
      try
          rfl <;>
        simp [of_cauchy_zero, of_cauchy_one, of_cauchy_add, of_cauchy_neg, of_cauchy_mul, ← fun n =>
            show @coe ℕ ℝ ⟨_⟩ n = ⟨n⟩ from rfl] <;>
          first |
            apply add_assocₓ|
            apply add_commₓ|
            apply mul_assoc|
            apply mul_comm|
            apply left_distrib|
            apply right_distrib|
            apply sub_eq_add_neg|
            skip

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/


instance : Ringₓ ℝ := by
  infer_instance

instance : CommSemiringₓ ℝ := by
  infer_instance

instance : Semiringₓ ℝ := by
  infer_instance

instance : CommMonoidWithZero ℝ := by
  infer_instance

instance : MonoidWithZeroₓ ℝ := by
  infer_instance

instance : AddCommGroupₓ ℝ := by
  infer_instance

instance : AddGroupₓ ℝ := by
  infer_instance

instance : AddCommMonoidₓ ℝ := by
  infer_instance

instance : AddMonoidₓ ℝ := by
  infer_instance

instance : AddLeftCancelSemigroup ℝ := by
  infer_instance

instance : AddRightCancelSemigroup ℝ := by
  infer_instance

instance : AddCommSemigroupₓ ℝ := by
  infer_instance

instance : AddSemigroupₓ ℝ := by
  infer_instance

instance : CommMonoidₓ ℝ := by
  infer_instance

instance : Monoidₓ ℝ := by
  infer_instance

instance : CommSemigroupₓ ℝ := by
  infer_instance

instance : Semigroupₓ ℝ := by
  infer_instance

instance : Sub ℝ := by
  infer_instance

instance : Module ℝ ℝ := by
  infer_instance

instance : Inhabited ℝ :=
  ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : StarRing ℝ :=
  starRingOfComm

instance : HasTrivialStar ℝ :=
  ⟨fun _ => rfl⟩

/-- Coercion `ℚ` → `ℝ` as a `ring_hom`. Note that this
is `cau_seq.completion.of_rat`, not `rat.cast`. -/
def ofRat : ℚ →+* ℝ := by
  refine_struct { toFun := of_cauchy ∘ of_rat } <;>
    simp [← of_rat_one, ← of_rat_zero, ← of_rat_mul, ← of_rat_add, ← of_cauchy_one, ← of_cauchy_zero, of_cauchy_mul,
      of_cauchy_add]

theorem of_rat_apply (x : ℚ) : ofRat x = of_cauchy (CauSeq.Completion.ofRat x) :=
  rfl

/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩

theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans mk_eq

private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    (Quotientₓ.liftOn₂ x y (· < ·)) fun f₁ g₁ f₂ g₂ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoidₓ.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoidₓ.symm hg))⟩

instance : LT ℝ :=
  ⟨Lt⟩

theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show Lt _ _ ↔ _ by
    rw [lt] <;> rfl

@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy

theorem mk_zero : mk 0 = 0 := by
  rw [← of_cauchy_zero] <;> rfl

theorem mk_one : mk 1 = 1 := by
  rw [← of_cauchy_one] <;> rfl

theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by
  simp [← mk, of_cauchy_add]

theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by
  simp [← mk, of_cauchy_mul]

theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by
  simp [← mk, of_cauchy_neg]

@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt] <;> exact iff_of_eq (congr_arg Pos (sub_zero f))

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y

instance : LE ℝ :=
  ⟨Le⟩

private theorem le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show Le _ _ ↔ _ by
    rw [le]

@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by
  simp [← le_def, ← mk_eq] <;> rfl

@[elab_as_eliminator]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x := by
  cases' x with x
  induction' x using Quot.induction_on with x
  exact h x

theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b := by
  induction a using Real.ind_mk
  induction b using Real.ind_mk
  induction c using Real.ind_mk
  simp only [← mk_lt, mk_add]
  show Pos _ ↔ Pos _
  rw [add_sub_add_left_eq_sub]

instance : PartialOrderₓ ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le := fun a b =>
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b => by
        simpa using lt_iff_le_not_leₓ
  le_refl := fun a =>
    a.ind_mk
      (by
        intro a <;> rw [mk_le])
  le_trans := fun a b c =>
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b =>
        (Real.ind_mk c) fun c => by
          simpa using le_transₓ
  lt_iff_le_not_le := fun a b =>
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b => by
        simpa using lt_iff_le_not_leₓ
  le_antisymm := fun a b =>
    (Real.ind_mk a) fun a =>
      (Real.ind_mk b) fun b => by
        simpa [← mk_eq] using @CauSeq.le_antisymm _ _ a b

instance : Preorderₓ ℝ := by
  infer_instance

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible }
theorem of_rat_lt {x y : ℚ} : ofRat x < ofRat y ↔ x < y := by
  rw [mk_lt]
  exact const_lt

protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert of_rat_lt.2 zero_lt_one <;> simp

protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b := by
  induction' a using Real.ind_mk with a
  induction' b using Real.ind_mk with b
  simpa only [← mk_lt, ← mk_pos, mk_mul] using CauSeq.mul_pos

instance : OrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder, Real.semiring with
    add_le_add_left := by
      simp only [← le_iff_eq_or_lt]
      rintro a b ⟨rfl, h⟩
      · simp
        
      · exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›)
        ,
    zero_le_one := le_of_ltₓ Real.zero_lt_one, mul_pos := @Real.mul_pos }

instance : OrderedRing ℝ := by
  infer_instance

instance : OrderedSemiring ℝ := by
  infer_instance

instance : OrderedAddCommGroup ℝ := by
  infer_instance

instance : OrderedCancelAddCommMonoid ℝ := by
  infer_instance

instance : OrderedAddCommMonoid ℝ := by
  infer_instance

instance : Nontrivial ℝ :=
  ⟨⟨0, 1, ne_of_ltₓ Real.zero_lt_one⟩⟩

open Classical

noncomputable instance : LinearOrderₓ ℝ :=
  { Real.partialOrder with
    le_total := by
      intro a b
      induction' a using Real.ind_mk with a
      induction' b using Real.ind_mk with b
      simpa using le_totalₓ a b,
    decidableLe := by
      infer_instance }

noncomputable instance : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.orderedRing, Real.commRing, Real.linearOrder with }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedRing ℝ := by
  infer_instance

noncomputable instance : LinearOrderedSemiring ℝ := by
  infer_instance

instance : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.is_domain with }

private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩

noncomputable instance : Inv ℝ :=
  ⟨inv'⟩

theorem of_cauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by
    rw [inv']

theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ =>
    show (inv' _).cauchy = _ by
      rw [inv']

noncomputable instance : LinearOrderedField ℝ :=
  { Real.linearOrderedCommRing with inv := Inv.inv,
    mul_inv_cancel := by
      rintro ⟨a⟩ h
      rw [mul_comm]
      simp only [of_cauchy_inv, of_cauchy_mul, of_cauchy_one, of_cauchy_zero, ← Ne.def] at *
      exact CauSeq.Completion.inv_mul_cancel h,
    inv_zero := by
      simp [of_cauchy_zero, of_cauchy_inv] }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedAddCommGroup ℝ := by
  infer_instance

noncomputable instance field : Field ℝ := by
  infer_instance

noncomputable instance : DivisionRing ℝ := by
  infer_instance

noncomputable instance : DistribLattice ℝ := by
  infer_instance

noncomputable instance : Lattice ℝ := by
  infer_instance

noncomputable instance : SemilatticeInf ℝ := by
  infer_instance

noncomputable instance : SemilatticeSup ℝ := by
  infer_instance

noncomputable instance : HasInf ℝ := by
  infer_instance

noncomputable instance : HasSup ℝ := by
  infer_instance

noncomputable instance decidableLt (a b : ℝ) : Decidable (a < b) := by
  infer_instance

noncomputable instance decidableLe (a b : ℝ) : Decidable (a ≤ b) := by
  infer_instance

noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by
  infer_instance

open Rat

@[simp]
theorem of_rat_eq_cast : ∀ x : ℚ, ofRat x = x :=
  ofRat.eq_rat_cast

-- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:92:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible }
theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀, ∀ j ≥ i, ∀, x ≤ f j) → x ≤ mk f := by
  intro h
  induction' x using Real.ind_mk with x
  apply le_of_not_ltₓ
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_le (H _ le_rfl).1
  rw [← of_rat_eq_cast]
  rw [mk_lt]
  refine' ⟨_, half_pos K0, i, fun j ij => _⟩
  have := add_le_add (H _ ij).2.1 (le_of_ltₓ (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this

theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀, ∀ j ≥ i, ∀, (f j : ℝ) ≤ x) : mk f ≤ x := by
  cases' h with i H
  rw [← neg_le_neg_iff, ← mk_neg]
  exact
    le_mk_of_forall_le
      ⟨i, fun j ij => by
        simp [← H _ ij]⟩

theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ} (H : ∃ i, ∀, ∀ j ≥ i, ∀, abs ((f j : ℝ) - x) ≤ ε) :
    abs (mk f - x) ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2 <|
        mk_le_of_forall_le <| H.imp fun i h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le.1 <| le_mk_of_forall_le <| H.imp fun i h j ij => sub_le.1 (abs_sub_le_iff.1 <| h j ij).2⟩

instance : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    (Real.ind_mk x) fun f =>
      let ⟨M, M0, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_ltₓ (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

theorem is_cau_seq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij =>
      lt_transₓ
        (by
          simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij))
        δε,
    fun H ε ε0 =>
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij =>
      (@Rat.cast_lt ℝ _ _ _).1 <| by
        simpa using hi _ ij⟩

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀, ∀ ε > 0, ∀, ∃ i, ∀, ∀ j ≥ i, ∀, abs ((f j : ℝ) - x) < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨is_cau_seq_iff_lift.2 (of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_le_of_dense (abs_nonneg _)) fun ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun i h j ij => le_of_ltₓ (h j ij)⟩

theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun z h' => Int.cast_le.1 <| le_transₓ h' <| le_of_ltₓ hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_ltₓ hn⟩)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (j k «expr ≥ » «expr⌈ ⌉₊»(«expr ⁻¹»(ε)))
theorem exists_is_lub (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLub S x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d } := by
    cases' exists_int_gt U with k hk
    refine' fun d => ⟨k * d, fun z h => _⟩
    rcases h with ⟨y, yS, hy⟩
    refine' Int.cast_le.1 (hy.trans _)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  choose f hf using fun d : ℕ => Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀, ∀ n > 0, ∀, ∃ y ∈ S, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by
      simpa using (div_le_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀, ∀ n > 0, ∀, ∀ y ∈ S, ∀, (y - (n : ℕ)⁻¹ : ℝ) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp [-sub_eq_add_neg]
    rwa [lt_div_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, _root_.inv_mul_cancel]
    exact ne_of_gtₓ (Nat.cast_pos.2 n0)
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ (j k) (_ : j ≥ ⌈ε⁻¹⌉₊) (_ : k ≥ ⌈ε⁻¹⌉₊), (f j / j - f k / k : ℚ) < ε by
      refine' ⟨_, fun j ij => abs_lt.2 ⟨_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_transₓ (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_transₓ (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine' lt_of_lt_of_leₓ ((@Rat.cast_lt ℝ _ _ _).1 _) ((inv_le ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_ltₓ hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine' ⟨mk g, ⟨fun x xS => _, fun y h => _⟩⟩
  · refine' le_of_forall_ge_of_dense fun z xz => _
    cases' exists_nat_gt (x - z)⁻¹ with K hK
    refine' le_mk_of_forall_le ⟨K, fun n nK => _⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine' le_transₓ _ (hf₂ _ n0 _ xS).le
    rwa [le_sub, inv_le (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
    
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_transₓ hx (h xS)⟩
    

noncomputable instance : HasSupₓ ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.some (exists_is_lub S h.1 h.2) else 0⟩

theorem Sup_def (S : Set ℝ) :
    sup S = if h : S.Nonempty ∧ BddAbove S then Classical.some (exists_is_lub S h.1 h.2) else 0 :=
  rfl

protected theorem is_lub_Sup (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) : IsLub S (sup S) := by
  simp only [← Sup_def, ← dif_pos (And.intro h₁ h₂)]
  apply Classical.some_spec

noncomputable instance : HasInfₓ ℝ :=
  ⟨fun S => -sup (-S)⟩

theorem Inf_def (S : Set ℝ) : inf S = -sup (-S) :=
  rfl

protected theorem is_glb_Inf (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddBelow S) : IsGlb S (inf S) := by
  rw [Inf_def, ← is_lub_neg', neg_negₓ]
  exact Real.is_lub_Sup _ h₁.neg h₂.neg

noncomputable instance : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with sup := HasSupₓ.sup, inf := HasInfₓ.inf,
    le_cSup := fun s a hs ha => (Real.is_lub_Sup s ⟨a, ha⟩ hs).1 ha,
    cSup_le := fun s a hs ha => (Real.is_lub_Sup s hs ⟨a, ha⟩).2 ha,
    cInf_le := fun s a hs ha => (Real.is_glb_Inf s ⟨a, ha⟩ hs).1 ha,
    le_cInf := fun s a hs ha => (Real.is_glb_Inf s hs ⟨a, ha⟩).2 ha }

theorem lt_Inf_add_pos {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) : ∃ a ∈ s, a < inf s + ε :=
  exists_lt_of_cInf_lt h <| lt_add_of_pos_right _ hε

theorem add_neg_lt_Sup {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) : ∃ a ∈ s, sup s + ε < a :=
  exists_lt_of_lt_cSup h <| add_lt_iff_neg_left.2 hε

theorem Inf_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.Nonempty) {a : ℝ} :
    inf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_cInf_lt h' (H ε ε_pos)
    
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact cInf_lt_of_lt h x_in hx
    

theorem le_Sup_iff {s : Set ℝ} (h : BddAbove s) (h' : s.Nonempty) {a : ℝ} :
    a ≤ sup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine' ⟨fun H ε ε_neg => _, fun H ε ε_pos => _⟩
  · exact exists_lt_of_lt_cSup h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
    
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_cSup_of_lt h x_in hx)
    

@[simp]
theorem Sup_empty : sup (∅ : Set ℝ) = 0 :=
  dif_neg <| by
    simp

theorem csupr_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨆ i, f i) = 0 := by
  dsimp' [← supr]
  convert Real.Sup_empty
  rw [Set.range_eq_empty_iff]
  infer_instance

@[simp]
theorem csupr_const_zero {α : Sort _} : (⨆ i : α, (0 : ℝ)) = 0 := by
  cases is_empty_or_nonempty α
  · exact Real.csupr_empty _
    
  · exact csupr_const
    

theorem Sup_of_not_bdd_above {s : Set ℝ} (hs : ¬BddAbove s) : sup s = 0 :=
  dif_neg fun h => hs h.2

theorem supr_of_not_bdd_above {α : Sort _} {f : α → ℝ} (hf : ¬BddAbove (Set.Range f)) : (⨆ i, f i) = 0 :=
  Sup_of_not_bdd_above hf

theorem Sup_univ : sup (@Set.Univ ℝ) = 0 :=
  Real.Sup_of_not_bdd_above fun ⟨x, h⟩ => not_le_of_lt (lt_add_one _) <| h (Set.mem_univ _)

@[simp]
theorem Inf_empty : inf (∅ : Set ℝ) = 0 := by
  simp [← Inf_def, ← Sup_empty]

theorem cinfi_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨅ i, f i) = 0 := by
  rw [infi_of_empty', Inf_empty]

@[simp]
theorem cinfi_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ)) = 0 := by
  cases is_empty_or_nonempty α
  · exact Real.cinfi_empty _
    
  · exact cinfi_const
    

theorem Inf_of_not_bdd_below {s : Set ℝ} (hs : ¬BddBelow s) : inf s = 0 :=
  neg_eq_zero.2 <| Sup_of_not_bdd_above <| mt bdd_above_neg.1 hs

theorem infi_of_not_bdd_below {α : Sort _} {f : α → ℝ} (hf : ¬BddBelow (Set.Range f)) : (⨅ i, f i) = 0 :=
  Inf_of_not_bdd_below hf

/-- As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Sup_nonneg (S : Set ℝ) (hS : ∀, ∀ x ∈ S, ∀, (0 : ℝ) ≤ x) : 0 ≤ sup S := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Sup_empty.ge
    
  · apply dite _ (fun h => le_cSup_of_le h hy <| hS y hy) fun h => (Sup_of_not_bdd_above h).Ge
    

/-- As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
theorem Sup_nonpos (S : Set ℝ) (hS : ∀, ∀ x ∈ S, ∀, x ≤ (0 : ℝ)) : sup S ≤ 0 := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Sup_empty.le, cSup_le hS₂ hS]

/-- As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem Inf_nonneg (S : Set ℝ) (hS : ∀, ∀ x ∈ S, ∀, (0 : ℝ) ≤ x) : 0 ≤ inf S := by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Inf_empty.ge, le_cInf hS₂ hS]

/-- As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
theorem Inf_nonpos (S : Set ℝ) (hS : ∀, ∀ x ∈ S, ∀, x ≤ (0 : ℝ)) : inf S ≤ 0 := by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Inf_empty.le
    
  · apply dite _ (fun h => cInf_le_of_le h hy <| hS y hy) fun h => (Inf_of_not_bdd_below h).le
    

theorem Inf_le_Sup (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : inf s ≤ sup s := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [Inf_empty, Sup_empty]
    
  · exact cInf_le_cSup h₁ h₂ hne
    

theorem cau_seq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let S := { x : ℝ | const abs x < f }
  have lb : ∃ x, x ∈ S := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀, ∀ y ∈ S, ∀, y ≤ x := fun x h y yS =>
    le_of_ltₓ <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀, ∀ y ∈ S, ∀, y ≤ x := (exists_gt f).imp ub'
  refine' ⟨Sup S, ((lt_total _ _).resolve_left fun h => _).resolve_right fun h => _⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (cSup_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
    
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (le_cSup ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, add_commₓ, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij
    

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cau_seq_converges⟩

end Real

