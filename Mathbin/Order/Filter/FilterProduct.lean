/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
import Mathbin.Order.Filter.Ultrafilter
import Mathbin.Order.Filter.Germ

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `order.filter.germ`.

## Tags

ultrafilter, ultraproduct
-/


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

open Classical

namespace Filter

-- mathport name: «expr∀* , »
local notation3"∀* "(...)", "r:(scoped p => Filter.Eventually p φ) => r

namespace Germ

open Ultrafilter

-- mathport name: «exprβ*»
local notation "β*" => Germ (φ : Filter α) β

/-- If `φ` is an ultrafilter then the ultraproduct is a division ring. -/
instance [DivisionRing β] : DivisionRing β* :=
  { Germ.ring, Germ.divInvMonoid, Germ.nontrivial with
    mul_inv_cancel := fun f =>
      (induction_on f) fun f hf =>
        coe_eq.2 <|
          (φ.em fun y => f y = 0).elim (fun H => (hf <| coe_eq.2 H).elim) fun H => H.mono fun x => mul_inv_cancel,
    inv_zero :=
      coe_eq.2 <| by
        simp only [← (· ∘ ·), ← inv_zero] }

/-- If `φ` is an ultrafilter then the ultraproduct is a field. -/
instance [Field β] : Field β* :=
  { Germ.commRing, Germ.divisionRing with }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance [LinearOrderₓ β] : LinearOrderₓ β* :=
  { Germ.partialOrder with
    le_total := fun f g =>
      (induction_on₂ f g) fun f g => eventually_or.1 <| eventually_of_forall fun x => le_totalₓ _ _,
    decidableLe := by
      infer_instance }

@[simp, norm_cast]
theorem const_div [DivisionRing β] (x y : β) : (↑(x / y) : β*) = ↑x / ↑y :=
  rfl

theorem coe_lt [Preorderₓ β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [← lt_iff_le_not_leₓ, ← eventually_and, ← coe_le, ← eventually_not, ← eventually_le]

theorem coe_pos [Preorderₓ β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt

theorem const_lt [Preorderₓ β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans lift_rel_const_iff

theorem lt_def [Preorderₓ β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

/-- If `φ` is an ultrafilter then the ultraproduct is an ordered ring. -/
instance [OrderedRing β] : OrderedRing β* :=
  { Germ.ring, Germ.orderedAddCommGroup, Germ.nontrivial with zero_le_one := const_le zero_le_one,
    mul_pos := fun x y =>
      (induction_on₂ x y) fun f g hf hg => coe_pos.2 <| (coe_pos.1 hg).mp <| (coe_pos.1 hf).mono fun x => mul_pos }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered ring. -/
noncomputable instance [LinearOrderedRing β] : LinearOrderedRing β* :=
  { Germ.orderedRing, Germ.linearOrder, Germ.nontrivial with }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered field. -/
noncomputable instance [LinearOrderedField β] : LinearOrderedField β* :=
  { Germ.linearOrderedRing, Germ.field with }

/-- If `φ` is an ultrafilter then the ultraproduct is a linear ordered commutative ring. -/
noncomputable instance [LinearOrderedCommRing β] : LinearOrderedCommRing β* :=
  { Germ.linearOrderedRing, Germ.commMonoid with }

/-- If `φ` is an ultrafilter then the ultraproduct is a decidable linear ordered commutative
group. -/
noncomputable instance [LinearOrderedAddCommGroup β] : LinearOrderedAddCommGroup β* :=
  { Germ.orderedAddCommGroup, Germ.linearOrder with }

theorem max_def [LinearOrderₓ β] (x y : β*) : max x y = map₂ max x y :=
  (induction_on₂ x y) fun a b => by
    cases le_totalₓ (a : β*) b
    · rw [max_eq_rightₓ h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_rightₓ hi).symm
      
    · rw [max_eq_leftₓ h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_leftₓ hi).symm
      

theorem min_def [K : LinearOrderₓ β] (x y : β*) : min x y = map₂ min x y :=
  (induction_on₂ x y) fun a b => by
    cases le_totalₓ (a : β*) b
    · rw [min_eq_leftₓ h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_leftₓ hi).symm
      
    · rw [min_eq_rightₓ h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_rightₓ hi).symm
      

theorem abs_def [LinearOrderedAddCommGroup β] (x : β*) : abs x = map abs x :=
  (induction_on x) fun a => rfl

@[simp]
theorem const_max [LinearOrderₓ β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]

@[simp]
theorem const_min [LinearOrderₓ β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]

@[simp]
theorem const_abs [LinearOrderedAddCommGroup β] (x : β) : (↑(abs x) : β*) = abs ↑x := by
  rw [abs_def, map_const]

theorem linearOrder.to_lattice_eq_filter_germ_lattice [LinearOrderₓ β] :
    @LinearOrderₓ.toLattice (Filter.Germ (↑φ) β) Filter.Germ.linearOrder = Filter.Germ.lattice :=
  Lattice.ext fun x y => Iff.rfl

end Germ

end Filter

