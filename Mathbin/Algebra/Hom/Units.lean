/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Mathbin.Algebra.Hom.Group

/-!
# Monoid homomorphisms and units

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `units` that depend on `monoid_hom`.

## Main declarations

* `units.map`: Turn an homomorphism from `α` to `β` monoids into an homomorphism from `αˣ` to `βˣ`.
* `monoid_hom.to_hom_units`: Turn an homomorphism from a group `α` to `β` into an homomorphism from
  `α` to `βˣ`.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `group` lemmas.
-/


open Function

universe u v w

namespace Units

variable {α : Type _} {M : Type u} {N : Type v} {P : Type w} [Monoidₓ M] [Monoidₓ N] [Monoidₓ P]

/-- The group homomorphism on units induced by a `monoid_hom`. -/
@[to_additive "The `add_group` homomorphism on `add_unit`s induced by an `add_monoid_hom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u =>
      ⟨f u.val, f u.inv, by
        rw [← f.map_mul, u.val_inv, f.map_one], by
        rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_mul x y)

@[simp, to_additive]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x :=
  rfl

@[simp, to_additive]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ :=
  rfl

@[simp, to_additive]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) :=
  rfl

variable (M)

@[simp, to_additive]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by
  ext <;> rfl

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `add_units M → M` as an add_monoid homomorphism."]
def coeHom : Mˣ →* M :=
  ⟨coe, coe_one, coe_mul⟩

variable {M}

@[simp, to_additive]
theorem coe_hom_apply (x : Mˣ) : coeHom M x = ↑x :=
  rfl

@[simp, norm_cast, to_additive]
theorem coe_pow (u : Mˣ) (n : ℕ) : ((u ^ n : Mˣ) : M) = u ^ n :=
  (Units.coeHom M).map_pow u n

section DivisionMonoid

variable [DivisionMonoid α]

@[simp, norm_cast, to_additive]
theorem coe_inv : ∀ u : αˣ, ↑u⁻¹ = (u⁻¹ : α) :=
  (Units.coeHom α).map_inv

@[simp, norm_cast, to_additive]
theorem coe_zpow : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = u ^ n :=
  (Units.coeHom α).map_zpow

theorem _root_.divp_eq_div (a : α) (u : αˣ) : a /ₚ u = a / u := by
  rw [div_eq_mul_inv, divp, u.coe_inv]

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
      "If a map `g : M → add_units N` agrees with a homomorphism `f : M →+ N`, then this map\nis an add_monoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ where
  toFun := g
  map_one' := Units.ext <| (h 1).symm ▸ f.map_one
  map_mul' := fun x y =>
    Units.ext <| by
      simp only [← h, ← coe_mul, ← f.map_mul]

@[simp, to_additive]
theorem coe_lift_right {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) : (liftRight f g h x : N) = f x :=
  h x

@[simp, to_additive]
theorem mul_lift_right_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) : f x * ↑(liftRight f g h x)⁻¹ = 1 :=
  by
  rw [Units.mul_inv_eq_iff_eq_mul, one_mulₓ, coe_lift_right]

@[simp, to_additive]
theorem lift_right_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) : ↑(liftRight f g h x)⁻¹ * f x = 1 :=
  by
  rw [Units.inv_mul_eq_iff_eq_mul, mul_oneₓ, coe_lift_right]

end Units

namespace MonoidHom

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
      "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,\nthen its image lies in the `add_units` of `M`,\nand `f.to_hom_units` is the corresponding homomorphism from `G` to `add_units M`."]
def toHomUnits {G M : Type _} [Groupₓ G] [Monoidₓ M] (f : G →* M) : G →* Mˣ where
  toFun := fun g =>
    ⟨f g, f g⁻¹, by
      rw [← f.map_mul, mul_inv_selfₓ, f.map_one], by
      rw [← f.map_mul, inv_mul_selfₓ, f.map_one]⟩
  map_one' := Units.ext f.map_one
  map_mul' := fun _ _ => Units.ext (f.map_mul _ _)

@[simp]
theorem coe_to_hom_units {G M : Type _} [Groupₓ G] [Monoidₓ M] (f : G →* M) (g : G) : (f.toHomUnits g : M) = f g :=
  rfl

end MonoidHom

namespace IsUnit

variable {F α M N : Type _}

section Monoidₓ

variable [Monoidₓ M] [Monoidₓ N]

@[to_additive]
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩ <;> exact (Units.map (f : M →* N) y).IsUnit

/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* Nˣ`. See also `units.lift_right` for a computable version. -/
@[to_additive
      "If a homomorphism `f : M →+ N` sends each element to an `is_add_unit`, then it can be\nlifted to `f : M →+ add_units N`. See also `add_units.lift_right` for a computable version."]
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).Unit) fun x => rfl

@[to_additive]
theorem coe_lift_right (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) : (IsUnit.liftRight f hf x : N) = f x :=
  rfl

@[simp, to_additive]
theorem mul_lift_right_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) : f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 :=
  Units.mul_lift_right_inv (fun y => rfl) x

@[simp, to_additive]
theorem lift_right_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) : ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 :=
  Units.lift_right_inv_mul (fun y => rfl) x

end Monoidₓ

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

@[simp, to_additive]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.coe_inv, Units.inv_mul]

@[simp, to_additive]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.coe_inv, Units.mul_inv]

/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `is_unit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `units α` to `α`. See also `to_units`. -/
@[to_additive
      "The element of the additive group of additive units, corresponding to an element of\nan additive monoid which is an additive unit. As opposed to `is_add_unit.add_unit`, the negation is\ncomputable and comes from the negation on `α`. This is useful to transfer properties of negation in\n`add_units α` to `α`. See also `to_add_units`.",
  simps]
def unit' (h : IsUnit a) : αˣ :=
  ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩

@[simp, to_additive]
protected theorem mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left

@[simp, to_additive]
protected theorem inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left

@[simp, to_additive]
protected theorem mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _

@[simp, to_additive]
protected theorem inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _

@[to_additive]
protected theorem div_self (h : IsUnit a) : a / a = 1 := by
  rw [div_eq_mul_inv, h.mul_inv_cancel]

@[to_additive]
protected theorem eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq

@[to_additive]
protected theorem eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq

@[to_additive]
protected theorem inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul

@[to_additive]
protected theorem mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul

@[to_additive]
protected theorem mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _

@[to_additive]
protected theorem inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _

@[to_additive]
protected theorem mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _

@[to_additive]
protected theorem mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _

@[simp, to_additive]
protected theorem div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]

@[simp, to_additive]
protected theorem mul_div_cancel (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]

@[to_additive]
protected theorem mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by
  simp [← h]

@[to_additive]
protected theorem one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by
  simp [← h]

@[to_additive]
theorem inv : IsUnit a → IsUnit a⁻¹ := by
  rintro ⟨u, rfl⟩
  rw [← Units.coe_inv]
  exact Units.is_unit _

@[to_additive]
theorem div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]
  exact ha.mul hb.inv

@[to_additive]
protected theorem div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp_rw [div_eq_mul_inv]
  exact Units.mul_left_inj h.inv.unit'

@[to_additive]
protected theorem div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]

@[to_additive]
protected theorem eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]

@[to_additive]
protected theorem div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2

@[to_additive]
protected theorem eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2

@[to_additive]
protected theorem div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩

@[to_additive]
protected theorem div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left, one_div]

@[to_additive]
protected theorem mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [← div_eq_mul_inv, ← mul_inv_rev, ← mul_assoc, ← h.mul_inv_cancel_left]

@[to_additive]
protected theorem mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by
  simp [← h]

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b c d : α}

@[to_additive]
protected theorem div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]

@[to_additive]
protected theorem mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel]

@[to_additive]
protected theorem mul_div_cancel' (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]

@[to_additive]
protected theorem mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]

@[to_additive]
protected theorem mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d) (a c : α) (h : a / b = c / d) :
    a * d = c * b := by
  rw [← mul_oneₓ a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]

@[to_additive]
protected theorem div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) : a / b = c / d ↔ a * d = c * b := by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_commₓ, hd.div_mul_cancel]

@[to_additive]
protected theorem div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]

end DivisionCommMonoid

end IsUnit

