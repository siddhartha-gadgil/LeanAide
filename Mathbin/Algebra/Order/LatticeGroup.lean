/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.Order.Group
import Mathbin.Tactic.NthRewrite.Default

/-!
# Lattice ordered groups

Lattice ordered groups were introduced by [Birkhoff][birkhoff1942].
They form the algebraic underpinnings of vector lattices, Banach lattices, AL-space, AM-space etc.

This file develops the basic theory, concentrating on the commutative case.

## Main statements

- `pos_div_neg`: Every element `a` of a lattice ordered commutative group has a decomposition
  `a⁺-a⁻` into the difference of the positive and negative component.
- `pos_inf_neg_eq_one`: The positive and negative components are coprime.
- `abs_triangle`: The absolute value operation satisfies the triangle inequality.

It is shown that the inf and sup operations are related to the absolute value operation by a
number of equations and inequalities.

## Notations

- `a⁺ = a ⊔ 0`: The *positive component* of an element `a` of a lattice ordered commutative group
- `a⁻ = (-a) ⊔ 0`: The *negative component* of an element `a` of a lattice ordered commutative group
- `|a| = a⊔(-a)`: The *absolute value* of an element `a` of a lattice ordered commutative group

## Implementation notes

A lattice ordered commutative group is a type `α` satisfying:

* `[lattice α]`
* `[comm_group α]`
* `[covariant_class α α (*) (≤)]`

The remainder of the file establishes basic properties of lattice ordered commutative groups. A
number of these results also hold in the non-commutative case ([Birkhoff][birkhoff1942],
[Fuchs][fuchs1963]) but we have not developed that here, since we are primarily interested in vector
lattices.

## References

* [Birkhoff, Lattice-ordered Groups][birkhoff1942]
* [Bourbaki, Algebra II][bourbaki1981]
* [Fuchs, Partially Ordered Algebraic Systems][fuchs1963]
* [Zaanen, Lectures on "Riesz Spaces"][zaanen1966]
* [Banasiak, Banach Lattices in Applications][banasiak]

## Tags

lattice, ordered, group
-/


-- Needed for squares
-- Needed for squares
universe u

-- A linearly ordered additive commutative group is a lattice ordered commutative group
-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LinearOrderedCommGroup.to_covariant_class (α : Type u) [LinearOrderedCommGroup α] :
    CovariantClass α α (· * ·) (· ≤ ·) where elim := fun a b c bc => LinearOrderedCommGroup.mul_le_mul_left _ _ bc a

variable {α : Type u} [Lattice α] [CommGroupₓ α]

-- Special case of Bourbaki A.VI.9 (1)
-- c + (a ⊔ b) = (c + a) ⊔ (c + b)
@[to_additive]
theorem mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a⊔b) = c * a⊔c * b := by
  refine'
    le_antisymmₓ _
      (by
        simp )
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_selfₓ, one_mulₓ]
  exact
    sup_le
      (by
        simp )
      (by
        simp )

@[to_additive]
theorem mul_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a⊓b) = c * a⊓c * b := by
  refine'
    le_antisymmₓ
      (by
        simp )
      _
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_selfₓ, one_mulₓ]
  exact
    le_inf
      (by
        simp )
      (by
        simp )

-- Special case of Bourbaki A.VI.9 (2)
-- -(a ⊔ b)=(-a) ⊓ (-b)
@[to_additive]
theorem inv_sup_eq_inv_inf_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊔b)⁻¹ = a⁻¹⊓b⁻¹ := by
  apply le_antisymmₓ
  · refine' le_inf _ _
    · rw [inv_le_inv_iff]
      exact le_sup_left
      
    · rw [inv_le_inv_iff]
      exact le_sup_right
      
    
  · rw [← inv_le_inv_iff, inv_invₓ]
    refine' sup_le _ _
    · rw [← inv_le_inv_iff]
      simp
      
    · rw [← inv_le_inv_iff]
      simp
      
    

-- -(a ⊓ b) = -a ⊔ -b
@[to_additive]
theorem inv_inf_eq_sup_inv [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊓b)⁻¹ = a⁻¹⊔b⁻¹ := by
  rw [← inv_invₓ (a⁻¹⊔b⁻¹), inv_sup_eq_inv_inf_inv a⁻¹ b⁻¹, inv_invₓ, inv_invₓ]

-- Bourbaki A.VI.10 Prop 7
-- a ⊓ b + (a ⊔ b) = a + b
@[to_additive]
theorem inf_mul_sup [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊓b) * (a⊔b) = a * b :=
  calc
    (a⊓b) * (a⊔b) = (a⊓b) * (a * b * (b⁻¹⊔a⁻¹)) := by
      rw [mul_sup b⁻¹ a⁻¹ (a * b)]
      simp
    _ = (a⊓b) * (a * b * (a⊓b)⁻¹) := by
      rw [inv_inf_eq_sup_inv, sup_comm]
    _ = a * b := by
      rw [mul_comm, inv_mul_cancel_right]
    

namespace LatticeOrderedCommGroup

/-- Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `a ⊔ 1` is said to be the *positive component* of `a`, denoted `a⁺`.
-/
-- see Note [lower instance priority]
@[to_additive
      "\nLet `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\nthe element `a ⊔ 0` is said to be the *positive component* of `a`, denoted `a⁺`.\n"]
instance (priority := 100) hasOneLatticeHasPosPart : HasPosPart α :=
  ⟨fun a => a⊔1⟩

@[to_additive pos_part_def]
theorem m_pos_part_def (a : α) : a⁺ = a⊔1 :=
  rfl

/-- Let `α` be a lattice ordered commutative group with identity `1`. For an element `a` of type `α`,
the element `(-a) ⊔ 1` is said to be the *negative component* of `a`, denoted `a⁻`.
-/
-- see Note [lower instance priority]
@[to_additive
      "\nLet `α` be a lattice ordered commutative group with identity `0`. For an element `a` of type `α`,\nthe element `(-a) ⊔ 0` is said to be the *negative component* of `a`, denoted `a⁻`.\n"]
instance (priority := 100) hasOneLatticeHasNegPart : HasNegPart α :=
  ⟨fun a => a⁻¹⊔1⟩

@[to_additive neg_part_def]
theorem m_neg_part_def (a : α) : a⁻ = a⁻¹⊔1 :=
  rfl

@[simp, to_additive]
theorem pos_one : (1 : α)⁺ = 1 :=
  sup_idem

@[simp, to_additive]
theorem neg_one : (1 : α)⁻ = 1 := by
  rw [m_neg_part_def, inv_one, sup_idem]

-- a⁻ = -(a ⊓ 0)
@[to_additive]
theorem neg_eq_inv_inf_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁻ = (a⊓1)⁻¹ := by
  rw [m_neg_part_def, ← inv_inj, inv_sup_eq_inv_inf_inv, inv_invₓ, inv_invₓ, inv_one]

@[to_additive le_abs]
theorem le_mabs (a : α) : a ≤ abs a :=
  le_sup_left

-- -a ≤ |a|
@[to_additive]
theorem inv_le_abs (a : α) : a⁻¹ ≤ abs a :=
  le_sup_right

-- 0 ≤ a⁺
@[to_additive pos_nonneg]
theorem one_le_pos (a : α) : 1 ≤ a⁺ :=
  le_sup_right

-- 0 ≤ a⁻
@[to_additive neg_nonneg]
theorem one_le_neg (a : α) : 1 ≤ a⁻ :=
  le_sup_right

-- pos_nonpos_iff
@[to_additive]
theorem pos_le_one_iff {a : α} : a⁺ ≤ 1 ↔ a ≤ 1 := by
  rw [m_pos_part_def, sup_le_iff]
  simp

-- neg_nonpos_iff
@[to_additive]
theorem neg_le_one_iff {a : α} : a⁻ ≤ 1 ↔ a⁻¹ ≤ 1 := by
  rw [m_neg_part_def, sup_le_iff]
  simp

@[to_additive]
theorem pos_eq_one_iff {a : α} : a⁺ = 1 ↔ a ≤ 1 := by
  rw [le_antisymm_iffₓ]
  simp only [← one_le_pos, ← and_trueₓ]
  exact pos_le_one_iff

@[to_additive]
theorem neg_eq_one_iff' {a : α} : a⁻ = 1 ↔ a⁻¹ ≤ 1 := by
  rw [le_antisymm_iffₓ]
  simp only [← one_le_neg, ← and_trueₓ]
  rw [neg_le_one_iff]

@[to_additive]
theorem neg_eq_one_iff [CovariantClass α α Mul.mul LE.le] {a : α} : a⁻ = 1 ↔ 1 ≤ a := by
  rw [le_antisymm_iffₓ]
  simp only [← one_le_neg, ← and_trueₓ]
  rw [neg_le_one_iff, inv_le_one']

@[to_additive le_pos]
theorem m_le_pos (a : α) : a ≤ a⁺ :=
  le_sup_left

-- -a ≤ a⁻
@[to_additive]
theorem inv_le_neg (a : α) : a⁻¹ ≤ a⁻ :=
  le_sup_left

-- Bourbaki A.VI.12
--  a⁻ = (-a)⁺
@[to_additive]
theorem neg_eq_pos_inv (a : α) : a⁻ = a⁻¹⁺ :=
  rfl

-- a⁺ = (-a)⁻
@[to_additive]
theorem pos_eq_neg_inv (a : α) : a⁺ = a⁻¹⁻ := by
  simp [← neg_eq_pos_inv]

-- We use this in Bourbaki A.VI.12  Prop 9 a)
-- c + (a ⊓ b) = (c + a) ⊓ (c + b)
@[to_additive]
theorem mul_inf_eq_mul_inf_mul [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : c * (a⊓b) = c * a⊓c * b := by
  refine'
    le_antisymmₓ
      (by
        simp )
      _
  rw [← mul_le_mul_iff_left c⁻¹, ← mul_assoc, inv_mul_selfₓ, one_mulₓ, le_inf_iff]
  simp

-- Bourbaki A.VI.12  Prop 9 a)
-- a = a⁺ - a⁻
@[simp, to_additive]
theorem pos_div_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺ / a⁻ = a := by
  symm
  rw [div_eq_mul_inv]
  apply eq_mul_inv_of_mul_eq
  rw [m_neg_part_def, mul_sup, mul_oneₓ, mul_right_invₓ, sup_comm, m_pos_part_def]

-- Bourbaki A.VI.12  Prop 9 a)
-- a⁺ ⊓ a⁻ = 0 (`a⁺` and `a⁻` are co-prime, and, since they are positive, disjoint)
@[to_additive]
theorem pos_inf_neg_eq_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : a⁺⊓a⁻ = 1 := by
  rw [← mul_right_injₓ (a⁻)⁻¹, mul_inf_eq_mul_inf_mul, mul_oneₓ, mul_left_invₓ, mul_comm, ← div_eq_mul_inv, pos_div_neg,
    neg_eq_inv_inf_one, inv_invₓ]

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊔b = b + (a - b)⁺
@[to_additive]
theorem sup_eq_mul_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a⊔b = b * (a / b)⁺ :=
  calc
    a⊔b = b * (a / b)⊔b * 1 := by
      rw [mul_oneₓ b, div_eq_mul_inv, mul_comm a, mul_inv_cancel_left]
    _ = b * (a / b⊔1) := by
      rw [← mul_sup (a / b) 1 b]
    

-- Bourbaki A.VI.12 (with a and b swapped)
-- a⊓b = a - (a - b)⁺
@[to_additive]
theorem inf_eq_div_pos_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a⊓b = a / (a / b)⁺ :=
  calc
    a⊓b = a * 1⊓a * (b / a) := by
      rw [mul_oneₓ a, div_eq_mul_inv, mul_comm b, mul_inv_cancel_left]
    _ = a * (1⊓b / a) := by
      rw [← mul_inf_eq_mul_inf_mul 1 (b / a) a]
    _ = a * (b / a⊓1) := by
      rw [inf_comm]
    _ = a * ((a / b)⁻¹⊓1) := by
      rw [div_eq_mul_inv]
      nth_rw 0[← inv_invₓ b]
      rw [← mul_inv, mul_comm b⁻¹, ← div_eq_mul_inv]
    _ = a * ((a / b)⁻¹⊓1⁻¹) := by
      rw [inv_one]
    _ = a / (a / b⊔1) := by
      rw [← inv_sup_eq_inv_inf_inv, ← div_eq_mul_inv]
    

-- Bourbaki A.VI.12 Prop 9 c)
@[to_additive le_iff_pos_le_neg_ge]
theorem m_le_iff_pos_le_neg_ge [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : a ≤ b ↔ a⁺ ≤ b⁺ ∧ b⁻ ≤ a⁻ := by
  constructor <;> intro h
  · constructor
    · exact sup_le (h.trans (m_le_pos b)) (one_le_pos b)
      
    · rw [← inv_le_inv_iff] at h
      exact sup_le (h.trans (inv_le_neg a)) (one_le_neg a)
      
    
  · rw [← pos_div_neg a, ← pos_div_neg b]
    exact div_le_div'' h.1 h.2
    

@[to_additive neg_abs]
theorem m_neg_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : abs a⁻ = 1 := by
  refine' le_antisymmₓ _ _
  · rw [← pos_inf_neg_eq_one a]
    apply le_inf
    · rw [pos_eq_neg_inv]
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_abs a)).right
      
    · exact And.right (Iff.elim_left (m_le_iff_pos_le_neg_ge _ _) (le_mabs a))
      
    
  · exact one_le_neg _
    

@[to_additive pos_abs]
theorem m_pos_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : abs a⁺ = abs a := by
  nth_rw 1[← pos_div_neg (abs a)]
  rw [div_eq_mul_inv]
  symm
  rw [mul_right_eq_self, inv_eq_one]
  exact m_neg_abs a

@[to_additive abs_nonneg]
theorem one_le_abs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : 1 ≤ abs a := by
  rw [← m_pos_abs]
  exact one_le_pos _

-- The proof from Bourbaki A.VI.12 Prop 9 d)
-- |a| = a⁺ - a⁻
@[to_additive]
theorem pos_mul_neg [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : abs a = a⁺ * a⁻ := by
  refine' le_antisymmₓ _ _
  · refine' sup_le _ _
    · nth_rw 0[← mul_oneₓ a]
      exact mul_le_mul' (m_le_pos a) (one_le_neg a)
      
    · nth_rw 0[← one_mulₓ a⁻¹]
      exact mul_le_mul' (one_le_pos a) (inv_le_neg a)
      
    
  · rw [← inf_mul_sup, pos_inf_neg_eq_one, one_mulₓ, ← m_pos_abs a]
    apply sup_le
    · exact ((m_le_iff_pos_le_neg_ge _ _).mp (le_mabs a)).left
      
    · rw [neg_eq_pos_inv]
      exact ((m_le_iff_pos_le_neg_ge _ _).mp (inv_le_abs a)).left
      
    

-- a ⊔ b - (a ⊓ b) = |b - a|
@[to_additive]
theorem sup_div_inf_eq_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊔b) / (a⊓b) = abs (b / a) := by
  rw [sup_eq_mul_pos_div, inf_comm, inf_eq_div_pos_div, div_eq_mul_inv]
  nth_rw 1[div_eq_mul_inv]
  rw [mul_inv_rev, inv_invₓ, mul_comm, ← mul_assoc, inv_mul_cancel_right, pos_eq_neg_inv (a / b)]
  nth_rw 1[div_eq_mul_inv]
  rw [mul_inv_rev, ← div_eq_mul_inv, inv_invₓ, ← pos_mul_neg]

-- 2•(a ⊔ b) = a + b + |b - a|
@[to_additive two_sup_eq_add_add_abs_sub]
theorem sup_sq_eq_mul_mul_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊔b) ^ 2 = a * b * abs (b / a) := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, ← mul_assoc, mul_comm, mul_assoc, ← pow_two,
    inv_mul_cancel_leftₓ]

-- 2•(a ⊓ b) = a + b - |b - a|
@[to_additive two_inf_eq_add_sub_abs_sub]
theorem inf_sq_eq_mul_div_abs_div [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : (a⊓b) ^ 2 = a * b / abs (b / a) := by
  rw [← inf_mul_sup a b, ← sup_div_inf_eq_abs_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_invₓ, mul_assoc,
    mul_inv_cancel_comm_assoc, ← pow_two]

/-- Every lattice ordered commutative group is a distributive lattice
-/
@[to_additive "Every lattice ordered commutative additive group is a distributive lattice"]
def latticeOrderedCommGroupToDistribLattice (α : Type u) [s : Lattice α] [CommGroupₓ α]
    [CovariantClass α α (· * ·) (· ≤ ·)] : DistribLattice α :=
  { s with
    le_sup_inf := by
      intros
      rw [← mul_le_mul_iff_left (x⊓(y⊓z)), inf_mul_sup x (y⊓z), ← inv_mul_le_iff_le_mul, le_inf_iff]
      constructor
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x y]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_left
          
        · apply inf_le_left
          
        
      · rw [inv_mul_le_iff_le_mul, ← inf_mul_sup x z]
        apply mul_le_mul'
        · apply inf_le_inf_left
          apply inf_le_right
          
        · apply inf_le_right
          
         }

-- See, e.g. Zaanen, Lectures on Riesz Spaces
-- 3rd lecture
-- |a ⊔ c - (b ⊔ c)| + |a ⊓ c-b ⊓ c| = |a - b|
@[to_additive]
theorem abs_div_sup_mul_abs_div_inf [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    abs ((a⊔c) / (b⊔c)) * abs ((a⊓c) / (b⊓c)) = abs (a / b) := by
  let this : DistribLattice α := lattice_ordered_comm_group_to_distrib_lattice α
  calc abs ((a⊔c) / (b⊔c)) * abs ((a⊓c) / (b⊓c)) = (b⊔c⊔(a⊔c)) / ((b⊔c)⊓(a⊔c)) * abs ((a⊓c) / (b⊓c)) := by
      rw [sup_div_inf_eq_abs_div]_ = (b⊔c⊔(a⊔c)) / ((b⊔c)⊓(a⊔c)) * ((b⊓c⊔a⊓c) / (b⊓c⊓(a⊓c))) := by
      rw [sup_div_inf_eq_abs_div (b⊓c) (a⊓c)]_ = (b⊔a⊔c) / (b⊓a⊔c) * (((b⊔a)⊓c) / (b⊓a⊓c)) := by
      rw [← sup_inf_right, ← inf_sup_right, sup_assoc]
      nth_rw 1[sup_comm]
      rw [sup_right_idem, sup_assoc, inf_assoc]
      nth_rw 3[inf_comm]
      rw [inf_right_idem, inf_assoc]_ = (b⊔a⊔c) * ((b⊔a)⊓c) / ((b⊓a⊔c) * (b⊓a⊓c)) := by
      rw [div_mul_div_comm]_ = (b⊔a) * c / ((b⊓a) * c) := by
      rw [mul_comm, inf_mul_sup, mul_comm (b⊓a⊔c), inf_mul_sup]_ = (b⊔a) / (b⊓a) := by
      rw [div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_inv_cancel_left, ← div_eq_mul_inv]_ = abs (a / b) := by
      rw [sup_div_inf_eq_abs_div]

/-- If `a` is positive, then it is equal to its positive component `a⁺`. -/
-- pos_of_nonneg
@[to_additive "If `a` is positive, then it is equal to its positive component `a⁺`."]
theorem pos_of_one_le (a : α) (h : 1 ≤ a) : a⁺ = a := by
  rw [m_pos_part_def]
  exact sup_of_le_left h

-- 0 ≤ a implies a⁺ = a
-- pos_of_nonpos
@[to_additive]
theorem pos_of_le_one (a : α) (h : a ≤ 1) : a⁺ = 1 :=
  pos_eq_one_iff.mpr h

@[to_additive neg_of_inv_nonneg]
theorem neg_of_one_le_inv (a : α) (h : 1 ≤ a⁻¹) : a⁻ = a⁻¹ := by
  rw [neg_eq_pos_inv]
  exact pos_of_one_le _ h

-- neg_of_neg_nonpos
@[to_additive]
theorem neg_of_inv_le_one (a : α) (h : a⁻¹ ≤ 1) : a⁻ = 1 :=
  neg_eq_one_iff'.mpr h

-- neg_of_nonpos
@[to_additive]
theorem neg_of_le_one [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : a ≤ 1) : a⁻ = a⁻¹ := by
  refine' neg_of_one_le_inv _ _
  rw [one_le_inv']
  exact h

-- neg_of_nonneg'
@[to_additive]
theorem neg_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : a⁻ = 1 :=
  neg_eq_one_iff.mpr h

-- 0 ≤ a implies |a| = a
@[to_additive abs_of_nonneg]
theorem mabs_of_one_le [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) (h : 1 ≤ a) : abs a = a := by
  unfold HasAbs.abs
  rw [sup_eq_mul_pos_div, div_eq_mul_inv, inv_invₓ, ← pow_two, inv_mul_eq_iff_eq_mul, ← pow_two, pos_of_one_le]
  rw [pow_two]
  apply one_le_mul h h

/-- The unary operation of taking the absolute value is idempotent. -/
@[simp, to_additive abs_abs "The unary operation of taking the absolute value is idempotent."]
theorem mabs_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a : α) : abs (abs a) = abs a :=
  mabs_of_one_le _ (one_le_abs _)

@[to_additive abs_sup_sub_sup_le_abs]
theorem mabs_sup_div_sup_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : abs ((a⊔c) / (b⊔c)) ≤ abs (a / b) :=
  by
  apply le_of_mul_le_of_one_le_left
  · rw [abs_div_sup_mul_abs_div_inf]
    
  · exact one_le_abs _
    

@[to_additive abs_inf_sub_inf_le_abs]
theorem mabs_inf_div_inf_le_mabs [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) : abs ((a⊓c) / (b⊓c)) ≤ abs (a / b) :=
  by
  apply le_of_mul_le_of_one_le_right
  · rw [abs_div_sup_mul_abs_div_inf]
    
  · exact one_le_abs _
    

-- Commutative case, Zaanen, 3rd lecture
-- For the non-commutative case, see Birkhoff Theorem 19 (27)
-- |(a ⊔ c) - (b ⊔ c)| ⊔ |(a ⊓ c) - (b ⊓ c)| ≤ |a - b|
@[to_additive Birkhoff_inequalities]
theorem m_Birkhoff_inequalities [CovariantClass α α (· * ·) (· ≤ ·)] (a b c : α) :
    abs ((a⊔c) / (b⊔c))⊔abs ((a⊓c) / (b⊓c)) ≤ abs (a / b) :=
  sup_le (mabs_sup_div_sup_le_mabs a b c) (mabs_inf_div_inf_le_mabs a b c)

/-- The absolute value satisfies the triangle inequality.
-/
-- Banasiak Proposition 2.12, Zaanen 2nd lecture
@[to_additive abs_add_le]
theorem mabs_mul_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : abs (a * b) ≤ abs a * abs b := by
  apply sup_le
  · exact mul_le_mul' (le_mabs a) (le_mabs b)
    
  · rw [mul_inv]
    exact mul_le_mul' (inv_le_abs _) (inv_le_abs _)
    

-- |a - b| = |b - a|
@[to_additive]
theorem abs_inv_comm (a b : α) : abs (a / b) = abs (b / a) := by
  unfold HasAbs.abs
  rw [inv_div a b, ← inv_invₓ (a / b), inv_div, sup_comm]

-- | |a| - |b| | ≤ |a - b|
@[to_additive]
theorem abs_abs_div_abs_le [CovariantClass α α (· * ·) (· ≤ ·)] (a b : α) : abs (abs a / abs b) ≤ abs (a / b) := by
  unfold HasAbs.abs
  rw [sup_le_iff]
  constructor
  · apply div_le_iff_le_mul.2
    convert mabs_mul_le (a / b) b
    · rw [div_mul_cancel']
      
    · rw [div_mul_cancel']
      
    · exact covariant_swap_mul_le_of_covariant_mul_le α
      
    
  · rw [div_eq_mul_inv, mul_inv_rev, inv_invₓ, mul_inv_le_iff_le_mul, ← abs_eq_sup_inv (a / b), abs_inv_comm]
    convert mabs_mul_le (b / a) a
    · rw [div_mul_cancel']
      
    · rw [div_mul_cancel']
      
    

end LatticeOrderedCommGroup

