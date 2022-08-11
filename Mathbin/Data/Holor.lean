/-
Copyright (c) 2018 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Mathbin.Algebra.Module.Pi
import Mathbin.Algebra.BigOperators.Basic

/-!
# Basic properties of holors

Holors are indexed collections of tensor coefficients. Confusingly,
they are often called tensors in physics and in the neural network
community.

A holor is simply a multidimensional array of values. The size of a
holor is specified by a `list ℕ`, whose length is called the dimension
of the holor.

The tensor product of `x₁ : holor α ds₁` and `x₂ : holor α ds₂` is the
holor given by `(x₁ ⊗ x₂) (i₁ ++ i₂) = x₁ i₁ * x₂ i₂`. A holor is "of
rank at most 1" if it is a tensor product of one-dimensional holors.
The CP rank of a holor `x` is the smallest N such that `x` is the sum
of N holors of rank at most 1.

Based on the tensor library found in <https://www.isa-afp.org/entries/Deep_Learning.html>

## References

* <https://en.wikipedia.org/wiki/Tensor_rank_decomposition>
-/


universe u

open List

open BigOperators

/-- `holor_index ds` is the type of valid index tuples used to identify an entry of a holor
of dimensions `ds`. -/
def HolorIndex (ds : List ℕ) : Type :=
  { is : List ℕ // Forall₂ (· < ·) is ds }

namespace HolorIndex

variable {ds₁ ds₂ ds₃ : List ℕ}

def take : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₁
  | ds, is => ⟨List.takeₓ (length ds) is.1, forall₂_take_append is.1 ds ds₂ is.2⟩

def drop : ∀ {ds₁ : List ℕ}, HolorIndex (ds₁ ++ ds₂) → HolorIndex ds₂
  | ds, is => ⟨List.dropₓ (length ds) is.1, forall₂_drop_append is.1 ds ds₂ is.2⟩

theorem cast_type (is : List ℕ) (eq : ds₁ = ds₂) (h : Forall₂ (· < ·) is ds₁) :
    (cast (congr_arg HolorIndex Eq) ⟨is, h⟩).val = is := by
  subst Eq <;> rfl

def assocRight : HolorIndex (ds₁ ++ ds₂ ++ ds₃) → HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃))

def assocLeft : HolorIndex (ds₁ ++ (ds₂ ++ ds₃)) → HolorIndex (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg HolorIndex (append_assoc ds₁ ds₂ ds₃).symm)

theorem take_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.take = t.take.take
  | ⟨is, h⟩ =>
    Subtype.eq <| by
      simp [← assoc_right, ← take, ← cast_type, ← List.take_take, ← Nat.le_add_rightₓ, ← min_eq_leftₓ]

theorem drop_take : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.take = t.take.drop
  | ⟨is, h⟩ =>
    Subtype.eq
      (by
        simp [← assoc_right, ← take, ← drop, ← cast_type, ← List.drop_take])

theorem drop_drop : ∀ t : HolorIndex (ds₁ ++ ds₂ ++ ds₃), t.assocRight.drop.drop = t.drop
  | ⟨is, h⟩ =>
    Subtype.eq
      (by
        simp [← add_commₓ, ← assoc_right, ← drop, ← cast_type, ← List.drop_drop])

end HolorIndex

/-- Holor (indexed collections of tensor coefficients) -/
def Holor (α : Type u) (ds : List ℕ) :=
  HolorIndex ds → α

namespace Holor

variable {α : Type} {d : ℕ} {ds : List ℕ} {ds₁ : List ℕ} {ds₂ : List ℕ} {ds₃ : List ℕ}

instance [Inhabited α] : Inhabited (Holor α ds) :=
  ⟨fun t => default⟩

instance [Zero α] : Zero (Holor α ds) :=
  ⟨fun t => 0⟩

instance [Add α] : Add (Holor α ds) :=
  ⟨fun x y t => x t + y t⟩

instance [Neg α] : Neg (Holor α ds) :=
  ⟨fun a t => -a t⟩

instance [AddSemigroupₓ α] : AddSemigroupₓ (Holor α ds) := by
  refine_struct { add := (· + ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance [AddCommSemigroupₓ α] : AddCommSemigroupₓ (Holor α ds) := by
  refine_struct { add := (· + ·).. } <;>
    run_tac
      tactic.pi_instance_derive_field

instance [AddMonoidₓ α] : AddMonoidₓ (Holor α ds) := by
  refine_struct { zero := (0 : Holor α ds), add := (· + ·), nsmul := fun n x i => n • x i } <;>
    run_tac
      tactic.pi_instance_derive_field

instance [AddCommMonoidₓ α] : AddCommMonoidₓ (Holor α ds) := by
  refine_struct { zero := (0 : Holor α ds), add := (· + ·), nsmul := AddMonoidₓ.nsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

instance [AddGroupₓ α] : AddGroupₓ (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds), add := (· + ·), nsmul := AddMonoidₓ.nsmul, zsmul := fun n x i => n • x i } <;>
    run_tac
      tactic.pi_instance_derive_field

instance [AddCommGroupₓ α] : AddCommGroupₓ (Holor α ds) := by
  refine_struct
      { zero := (0 : Holor α ds), add := (· + ·), nsmul := AddMonoidₓ.nsmul, zsmul := SubNegMonoidₓ.zsmul } <;>
    run_tac
      tactic.pi_instance_derive_field

-- scalar product
instance [Mul α] : HasSmul α (Holor α ds) :=
  ⟨fun a x => fun t => a * x t⟩

instance [Semiringₓ α] : Module α (Holor α ds) :=
  Pi.module _ _ _

/-- The tensor product of two holors. -/
def mul [s : Mul α] (x : Holor α ds₁) (y : Holor α ds₂) : Holor α (ds₁ ++ ds₂) := fun t => x t.take * y t.drop

-- mathport name: «expr ⊗ »
local infixl:70 " ⊗ " => mul

theorem cast_type (eq : ds₁ = ds₂) (a : Holor α ds₁) :
    cast (congr_arg (Holor α) Eq) a = fun t => a (cast (congr_arg HolorIndex Eq.symm) t) := by
  subst Eq <;> rfl

def assocRight : Holor α (ds₁ ++ ds₂ ++ ds₃) → Holor α (ds₁ ++ (ds₂ ++ ds₃)) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃))

def assocLeft : Holor α (ds₁ ++ (ds₂ ++ ds₃)) → Holor α (ds₁ ++ ds₂ ++ ds₃) :=
  cast (congr_arg (Holor α) (append_assoc ds₁ ds₂ ds₃).symm)

theorem mul_assoc0 [Semigroupₓ α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    x ⊗ y ⊗ z = (x ⊗ (y ⊗ z)).assocLeft :=
  funext fun t : HolorIndex (ds₁ ++ ds₂ ++ ds₃) => by
    rw [assoc_left]
    unfold mul
    rw [mul_assoc]
    rw [← HolorIndex.take_take, ← HolorIndex.drop_take, ← HolorIndex.drop_drop]
    rw [cast_type]
    rfl
    rw [append_assoc]

theorem mul_assoc [Semigroupₓ α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₃) :
    HEq (mul (mul x y) z) (mul x (mul y z)) := by
  simp [← cast_heq, ← mul_assoc0, ← assoc_left]

theorem mul_left_distrib [Distribₓ α] (x : Holor α ds₁) (y : Holor α ds₂) (z : Holor α ds₂) :
    x ⊗ (y + z) = x ⊗ y + x ⊗ z :=
  funext fun t => left_distrib (x (HolorIndex.take t)) (y (HolorIndex.drop t)) (z (HolorIndex.drop t))

theorem mul_right_distrib [Distribₓ α] (x : Holor α ds₁) (y : Holor α ds₁) (z : Holor α ds₂) :
    (x + y) ⊗ z = x ⊗ z + y ⊗ z :=
  funext fun t => add_mulₓ (x (HolorIndex.take t)) (y (HolorIndex.take t)) (z (HolorIndex.drop t))

@[simp]
theorem zero_mul {α : Type} [Ringₓ α] (x : Holor α ds₂) : (0 : Holor α ds₁) ⊗ x = 0 :=
  funext fun t => zero_mul (x (HolorIndex.drop t))

@[simp]
theorem mul_zero {α : Type} [Ringₓ α] (x : Holor α ds₁) : x ⊗ (0 : Holor α ds₂) = 0 :=
  funext fun t => mul_zero (x (HolorIndex.take t))

theorem mul_scalar_mul [Monoidₓ α] (x : Holor α []) (y : Holor α ds) : x ⊗ y = x ⟨[], Forall₂.nil⟩ • y := by
  simp [← mul, ← HasSmul.smul, ← HolorIndex.take, ← HolorIndex.drop]

/-- A slice is a subholor consisting of all entries with initial index i. -/
-- holor slices
def slice (x : Holor α (d :: ds)) (i : ℕ) (h : i < d) : Holor α ds := fun is : HolorIndex ds =>
  x ⟨i :: is.1, Forall₂.cons h is.2⟩

/-- The 1-dimensional "unit" holor with 1 in the `j`th position. -/
def unitVec [Monoidₓ α] [AddMonoidₓ α] (d : ℕ) (j : ℕ) : Holor α [d] := fun ti => if ti.1 = [j] then 1 else 0

theorem holor_index_cons_decomp (p : HolorIndex (d :: ds) → Prop) :
    ∀ t : HolorIndex (d :: ds),
      (∀ i is,
          ∀ h : t.1 = i :: is,
            p
              ⟨i :: is, by
                rw [← h]
                exact t.2⟩) →
        p t
  | ⟨[], hforall₂⟩, hp => absurd (forall₂_nil_left_iff.1 hforall₂) (cons_ne_nil d ds)
  | ⟨i :: is, hforall₂⟩, hp => hp i is rfl

/-- Two holors are equal if all their slices are equal. -/
theorem slice_eq (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) (h : slice x = slice y) : x = y :=
  funext fun t : HolorIndex (d :: ds) =>
    (holor_index_cons_decomp (fun t => x t = y t) t) fun i is hiis =>
      have hiisdds : Forall₂ (· < ·) (i :: is) (d :: ds) := by
        rw [← hiis]
        exact t.2
      have hid : i < d := (forall₂_cons.1 hiisdds).1
      have hisds : Forall₂ (· < ·) is ds := (forall₂_cons.1 hiisdds).2
      calc
        x ⟨i :: is, _⟩ = slice x i hid ⟨is, hisds⟩ := congr_arg (fun t => x t) (Subtype.eq rfl)
        _ = slice y i hid ⟨is, hisds⟩ := by
          rw [h]
        _ = y ⟨i :: is, _⟩ := congr_arg (fun t => y t) (Subtype.eq rfl)
        

theorem slice_unit_vec_mul [Ringₓ α] {i : ℕ} {j : ℕ} (hid : i < d) (x : Holor α ds) :
    slice (unitVec d j ⊗ x) i hid = if i = j then x else 0 :=
  funext fun t : HolorIndex ds =>
    if h : i = j then by
      simp [← slice, ← mul, ← HolorIndex.take, ← unit_vec, ← HolorIndex.drop, ← h]
    else by
      simp [← slice, ← mul, ← HolorIndex.take, ← unit_vec, ← HolorIndex.drop, ← h] <;> rfl

theorem slice_add [Add α] (i : ℕ) (hid : i < d) (x : Holor α (d :: ds)) (y : Holor α (d :: ds)) :
    slice x i hid + slice y i hid = slice (x + y) i hid :=
  funext fun t => by
    simp [← slice, ← (· + ·)]

theorem slice_zero [Zero α] (i : ℕ) (hid : i < d) : slice (0 : Holor α (d :: ds)) i hid = 0 :=
  rfl

theorem slice_sum [AddCommMonoidₓ α] {β : Type} (i : ℕ) (hid : i < d) (s : Finset β) (f : β → Holor α (d :: ds)) :
    (∑ x in s, slice (f x) i hid) = slice (∑ x in s, f x) i hid := by
  let this := Classical.decEq β
  refine' Finset.induction_on s _ _
  · simp [← slice_zero]
    
  · intro _ _ h_not_in ih
    rw [Finset.sum_insert h_not_in, ih, slice_add, Finset.sum_insert h_not_in]
    

/-- The original holor can be recovered from its slices by multiplying with unit vectors and
summing up. -/
@[simp]
theorem sum_unit_vec_mul_slice [Ringₓ α] (x : Holor α (d :: ds)) :
    (∑ i in (Finset.range d).attach, unitVec d i ⊗ slice x i (Nat.succ_le_of_ltₓ (Finset.mem_range.1 i.Prop))) = x := by
  apply slice_eq _ _ _
  ext i hid
  rw [← slice_sum]
  simp only [← slice_unit_vec_mul hid]
  rw [Finset.sum_eq_single (Subtype.mk i <| Finset.mem_range.2 hid)]
  · simp
    
  · intro (b : { x // x ∈ Finset.range d })(hb : b ∈ (Finset.range d).attach)(hbi : b ≠ ⟨i, _⟩)
    have hbi' : i ≠ b := by
      simpa only [← Ne.def, ← Subtype.ext_iff, ← Subtype.coe_mk] using hbi.symm
    simp [← hbi']
    
  · intro (hid' : Subtype.mk i _ ∉ Finset.attach (Finset.range d))
    exfalso
    exact absurd (Finset.mem_attach _ _) hid'
    

/-- `cprank_max1 x` means `x` has CP rank at most 1, that is,
  it is the tensor product of 1-dimensional holors. -/
-- CP rank
inductive CprankMax1 [Mul α] : ∀ {ds}, Holor α ds → Prop
  | nil (x : Holor α []) : cprank_max1 x
  | cons {d} {ds} (x : Holor α [d]) (y : Holor α ds) : cprank_max1 y → cprank_max1 (x ⊗ y)

/-- `cprank_max N x` means `x` has CP rank at most `N`, that is,
  it can be written as the sum of N holors of rank at most 1. -/
inductive CprankMax [Mul α] [AddMonoidₓ α] : ℕ → ∀ {ds}, Holor α ds → Prop
  | zero {ds} : cprank_max 0 (0 : Holor α ds)
  | succ (n) {ds} (x : Holor α ds) (y : Holor α ds) : CprankMax1 x → cprank_max n y → cprank_max (n + 1) (x + y)

theorem cprank_max_nil [Monoidₓ α] [AddMonoidₓ α] (x : Holor α nil) : CprankMax 1 x := by
  have h := CprankMax.succ 0 x 0 (CprankMax1.nil x) CprankMax.zero
  rwa [add_zeroₓ x, zero_addₓ] at h

theorem cprank_max_1 [Monoidₓ α] [AddMonoidₓ α] {x : Holor α ds} (h : CprankMax1 x) : CprankMax 1 x := by
  have h' := CprankMax.succ 0 x 0 h CprankMax.zero
  rwa [zero_addₓ, add_zeroₓ] at h'

theorem cprank_max_add [Monoidₓ α] [AddMonoidₓ α] :
    ∀ {m : ℕ} {n : ℕ} {x : Holor α ds} {y : Holor α ds}, CprankMax m x → CprankMax n y → CprankMax (m + n) (x + y)
  | 0, n, x, y, cprank_max.zero, hy => by
    simp [← hy]
  | m + 1, n, _, y, cprank_max.succ k x₁ x₂ hx₁ hx₂, hy => by
    simp only [← add_commₓ, ← add_assocₓ]
    apply cprank_max.succ
    · assumption
      
    · exact cprank_max_add hx₂ hy
      

theorem cprank_max_mul [Ringₓ α] : ∀ (n : ℕ) (x : Holor α [d]) (y : Holor α ds), CprankMax n y → CprankMax n (x ⊗ y)
  | 0, x, _, cprank_max.zero => by
    simp [← mul_zero x, ← cprank_max.zero]
  | n + 1, x, _, cprank_max.succ k y₁ y₂ hy₁ hy₂ => by
    rw [mul_left_distrib]
    rw [Nat.add_comm]
    apply cprank_max_add
    · exact cprank_max_1 (cprank_max1.cons _ _ hy₁)
      
    · exact cprank_max_mul k x y₂ hy₂
      

theorem cprank_max_sum [Ringₓ α] {β} {n : ℕ} (s : Finset β) (f : β → Holor α ds) :
    (∀, ∀ x ∈ s, ∀, CprankMax n (f x)) → CprankMax (s.card * n) (∑ x in s, f x) := by
  let this := Classical.decEq β <;>
    exact
      Finset.induction_on s
        (by
          simp [← cprank_max.zero])
        (by
          intro x s(h_x_notin_s : x ∉ s)ih h_cprank
          simp only [← Finset.sum_insert h_x_notin_s, ← Finset.card_insert_of_not_mem h_x_notin_s]
          rw [Nat.right_distrib]
          simp only [← Nat.one_mul, ← Nat.add_comm]
          have ih' : cprank_max (Finset.card s * n) (∑ x in s, f x) := by
            apply ih
            intro (x : β)(h_x_in_s : x ∈ s)
            simp only [← h_cprank, ← Finset.mem_insert_of_mem, ← h_x_in_s]
          exact cprank_max_add (h_cprank x (Finset.mem_insert_self x s)) ih')

theorem cprank_max_upper_bound [Ringₓ α] : ∀ {ds}, ∀ x : Holor α ds, CprankMax ds.Prod x
  | [], x => cprank_max_nil x
  | d :: ds, x => by
    have h_summands :
      ∀ i : { x // x ∈ Finset.range d }, CprankMax ds.Prod (unitVec d i.1 ⊗ slice x i.1 (mem_range.1 i.2)) := fun i =>
      cprank_max_mul _ _ _ (cprank_max_upper_bound (slice x i.1 (mem_range.1 i.2)))
    have h_dds_prod : (List.cons d ds).Prod = Finset.card (Finset.range d) * Prod ds := by
      simp [← Finset.card_range]
    have :
      CprankMax (Finset.card (Finset.attach (Finset.range d)) * Prod ds)
        (∑ i in Finset.attach (Finset.range d), unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) :=
      cprank_max_sum (Finset.range d).attach _ fun i _ => h_summands i
    have h_cprank_max_sum :
      CprankMax (Finset.card (Finset.range d) * Prod ds)
        (∑ i in Finset.attach (Finset.range d), unitVec d i.val ⊗ slice x i.val (mem_range.1 i.2)) :=
      by
      rwa [Finset.card_attach] at this
    rw [← sum_unit_vec_mul_slice x]
    rw [h_dds_prod]
    exact h_cprank_max_sum

/-- The CP rank of a holor `x`: the smallest N such that
  `x` can be written as the sum of N holors of rank at most 1. -/
noncomputable def cprank [Ringₓ α] (x : Holor α ds) : Nat :=
  @Nat.findₓ (fun n => CprankMax n x) (Classical.decPred _) ⟨ds.Prod, cprank_max_upper_bound x⟩

theorem cprank_upper_bound [Ringₓ α] : ∀ {ds}, ∀ x : Holor α ds, cprank x ≤ ds.Prod := fun ds (x : Holor α ds) => by
  let this := Classical.decPred fun n : ℕ => cprank_max n x <;>
    exact
      Nat.find_min'ₓ ⟨ds.prod, show (fun n => cprank_max n x) ds.prod from cprank_max_upper_bound x⟩
        (cprank_max_upper_bound x)

end Holor

