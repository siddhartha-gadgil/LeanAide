/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Chris Hughes, Michael Howes
-/
import Mathbin.Algebra.Group.Semiconj
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Hom.Aut
import Mathbin.Algebra.Hom.Group
import Mathbin.Data.Fintype.Basic

/-!
# Conjugacy of group elements

See also `mul_aut.conj` and `quandle.conj`.
-/


universe u v

variable {α : Type u} {β : Type v}

section Monoidₓ

variable [Monoidₓ α] [Monoidₓ β]

/-- We say that `a` is conjugate to `b` if for some unit `c` we have `c * a * c⁻¹ = b`. -/
def IsConj (a b : α) :=
  ∃ c : αˣ, SemiconjBy (↑c) a b

@[refl]
theorem IsConj.refl (a : α) : IsConj a a :=
  ⟨1, SemiconjBy.one_left a⟩

@[symm]
theorem IsConj.symm {a b : α} : IsConj a b → IsConj b a
  | ⟨c, hc⟩ => ⟨c⁻¹, hc.units_inv_symm_left⟩

theorem is_conj_comm {g h : α} : IsConj g h ↔ IsConj h g :=
  ⟨IsConj.symm, IsConj.symm⟩

@[trans]
theorem IsConj.trans {a b c : α} : IsConj a b → IsConj b c → IsConj a c
  | ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩ => ⟨c₂ * c₁, hc₂.mul_left hc₁⟩

@[simp]
theorem is_conj_iff_eq {α : Type _} [CommMonoidₓ α] {a b : α} : IsConj a b ↔ a = b :=
  ⟨fun ⟨c, hc⟩ => by
    rw [SemiconjBy, mul_comm, ← Units.mul_inv_eq_iff_eq_mul, mul_assoc, c.mul_inv, mul_oneₓ] at hc
    exact hc, fun h => by
    rw [h]⟩

protected theorem MonoidHom.map_is_conj (f : α →* β) {a b : α} : IsConj a b → IsConj (f a) (f b)
  | ⟨c, hc⟩ =>
    ⟨Units.map f c, by
      rw [Units.coe_map, SemiconjBy, ← f.map_mul, hc.eq, f.map_mul]⟩

end Monoidₓ

section CancelMonoid

variable [CancelMonoid α]

-- These lemmas hold for `right_cancel_monoid` with the current proofs, but for the sake of
-- not duplicating code (these lemmas also hold for `left_cancel_monoids`) we leave these
-- not generalised.
@[simp]
theorem is_conj_one_right {a : α} : IsConj 1 a ↔ a = 1 :=
  ⟨fun ⟨c, hc⟩ => mul_right_cancelₓ (hc.symm.trans ((mul_oneₓ _).trans (one_mulₓ _).symm)), fun h => by
    rw [h]⟩

@[simp]
theorem is_conj_one_left {a : α} : IsConj a 1 ↔ a = 1 :=
  calc
    IsConj a 1 ↔ IsConj 1 a := ⟨IsConj.symm, IsConj.symm⟩
    _ ↔ a = 1 := is_conj_one_right
    

end CancelMonoid

section Groupₓ

variable [Groupₓ α]

@[simp]
theorem is_conj_iff {a b : α} : IsConj a b ↔ ∃ c : α, c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ => ⟨c, mul_inv_eq_iff_eq_mul.2 hc⟩, fun ⟨c, hc⟩ =>
    ⟨⟨c, c⁻¹, mul_inv_selfₓ c, inv_mul_selfₓ c⟩, mul_inv_eq_iff_eq_mul.1 hc⟩⟩

@[simp]
theorem conj_inv {a b : α} : (b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ :=
  ((MulAut.conj b).map_inv a).symm

@[simp]
theorem conj_mul {a b c : α} : b * a * b⁻¹ * (b * c * b⁻¹) = b * (a * c) * b⁻¹ :=
  ((MulAut.conj b).map_mul a c).symm

@[simp]
theorem conj_pow {i : ℕ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction' i with i hi
  · simp
    
  · simp [← pow_succₓ, ← hi]
    

@[simp]
theorem conj_zpow {i : ℤ} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i * a⁻¹ := by
  induction i
  · simp
    
  · simp [← zpow_neg_succ_of_nat, ← conj_pow]
    

theorem conj_injective {x : α} : Function.Injective fun g : α => x * g * x⁻¹ :=
  (MulAut.conj x).Injective

end Groupₓ

@[simp]
theorem is_conj_iff₀ [GroupWithZeroₓ α] {a b : α} : IsConj a b ↔ ∃ c : α, c ≠ 0 ∧ c * a * c⁻¹ = b :=
  ⟨fun ⟨c, hc⟩ =>
    ⟨c, by
      rw [← Units.coe_inv, Units.mul_inv_eq_iff_eq_mul]
      exact ⟨c.ne_zero, hc⟩⟩,
    fun ⟨c, c0, hc⟩ =>
    ⟨Units.mk0 c c0, by
      rw [SemiconjBy, ← Units.mul_inv_eq_iff_eq_mul, Units.coe_inv, Units.coe_mk0]
      exact hc⟩⟩

namespace IsConj

/-- The setoid of the relation `is_conj` iff there is a unit `u` such that `u * x = y * u` -/
/- This small quotient API is largely copied from the API of `associates`;
where possible, try to keep them in sync -/
protected def setoid (α : Type _) [Monoidₓ α] : Setoidₓ α where
  R := IsConj
  iseqv := ⟨IsConj.refl, fun a b => IsConj.symm, fun a b c => IsConj.trans⟩

end IsConj

attribute [local instance] IsConj.setoid

/-- The quotient type of conjugacy classes of a group. -/
def ConjClasses (α : Type _) [Monoidₓ α] : Type _ :=
  Quotientₓ (IsConj.setoid α)

namespace ConjClasses

section Monoidₓ

variable [Monoidₓ α] [Monoidₓ β]

/-- The canonical quotient map from a monoid `α` into the `conj_classes` of `α` -/
protected def mk {α : Type _} [Monoidₓ α] (a : α) : ConjClasses α :=
  ⟦a⟧

instance : Inhabited (ConjClasses α) :=
  ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_is_conj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b :=
  Iff.intro Quotientₓ.exact Quot.sound

theorem quotient_mk_eq_mk (a : α) : ⟦a⟧ = ConjClasses.mk a :=
  rfl

theorem quot_mk_eq_mk (a : α) : Quot.mk Setoidₓ.R a = ConjClasses.mk a :=
  rfl

theorem forall_is_conj {p : ConjClasses α → Prop} : (∀ a, p a) ↔ ∀ a, p (ConjClasses.mk a) :=
  Iff.intro (fun h a => h _) fun h a => Quotientₓ.induction_on a h

theorem mk_surjective : Function.Surjective (@ConjClasses.mk α _) :=
  forall_is_conj.2 fun a => ⟨a, rfl⟩

instance : One (ConjClasses α) :=
  ⟨⟦1⟧⟩

theorem one_eq_mk_one : (1 : ConjClasses α) = ConjClasses.mk 1 :=
  rfl

theorem exists_rep (a : ConjClasses α) : ∃ a0 : α, ConjClasses.mk a0 = a :=
  Quot.exists_rep a

/-- A `monoid_hom` maps conjugacy classes of one group to conjugacy classes of another. -/
def map (f : α →* β) : ConjClasses α → ConjClasses β :=
  Quotientₓ.lift (ConjClasses.mk ∘ f) fun a b ab => mk_eq_mk_iff_is_conj.2 (f.map_is_conj ab)

theorem map_surjective {f : α →* β} (hf : Function.Surjective f) : Function.Surjective (ConjClasses.map f) := by
  intro b
  obtain ⟨b, rfl⟩ := ConjClasses.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨ConjClasses.mk a, rfl⟩

instance [Fintype α] [DecidableRel (IsConj : α → α → Prop)] : Fintype (ConjClasses α) :=
  Quotientₓ.fintype (IsConj.setoid α)

library_note "slow-failing instance priority"/--
Certain instances trigger further searches when they are considered as candidate instances;
these instances should be assigned a priority lower than the default of 1000 (for example, 900).

The conditions for this rule are as follows:
 * a class `C` has instances `instT : C T` and `instT' : C T'`
 * types `T` and `T'` are both specializations of another type `S`
 * the parameters supplied to `S` to produce `T` are not (fully) determined by `instT`,
   instead they have to be found by instance search
If those conditions hold, the instance `instT` should be assigned lower priority.

For example, suppose the search for an instance of `decidable_eq (multiset α)` tries the
candidate instance `con.quotient.decidable_eq (c : con M) : decidable_eq c.quotient`.
Since `multiset` and `con.quotient` are both quotient types, unification will check
that the relations `list.perm` and `c.to_setoid.r` unify. However, `c.to_setoid` depends on 
a `has_mul M` instance, so this unification triggers a search for `has_mul (list α)`;
this will traverse all subclasses of `has_mul` before failing.
On the other hand, the search for an instance of `decidable_eq (con.quotient c)` for `c : con M`
can quickly reject the candidate instance `multiset.has_decidable_eq` because the type of
`list.perm : list ?m_1 → list ?m_1 → Prop` does not unify with `M → M → Prop`.
Therefore, we should assign `con.quotient.decidable_eq` a lower priority because it fails slowly.
(In terms of the rules above, `C := decidable_eq`, `T := con.quotient`,
`instT := con.quotient.decidable_eq`, `T' := multiset`, `instT' := multiset.has_decidable_eq`,
and `S := quot`.)

If the type involved is a free variable (rather than an instantiation of some type `S`),
the instance priority should be even lower, see Note [lower instance priority].
-/


-- see Note [slow-failing instance priority]
instance (priority := 900) [DecidableRel (IsConj : α → α → Prop)] : DecidableEq (ConjClasses α) :=
  Quotientₓ.decidableEq

instance [DecidableEq α] [Fintype α] : DecidableRel (IsConj : α → α → Prop) := fun a b => by
  delta' IsConj SemiconjBy
  infer_instance

end Monoidₓ

section CommMonoidₓ

variable [CommMonoidₓ α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (mk_eq_mk_iff_is_conj.trans is_conj_iff_eq).1

theorem mk_bijective : Function.Bijective (@ConjClasses.mk α _) :=
  ⟨mk_injective, mk_surjective⟩

/-- The bijection between a `comm_group` and its `conj_classes`. -/
def mkEquiv : α ≃ ConjClasses α :=
  ⟨ConjClasses.mk, Quotientₓ.lift id fun (a : α) b => is_conj_iff_eq.1, Quotientₓ.lift_mk _ _, by
    rw [Function.RightInverse, Function.LeftInverse, forall_is_conj]
    intro x
    rw [← quotient_mk_eq_mk, ← quotient_mk_eq_mk, Quotientₓ.lift_mk, id.def]⟩

end CommMonoidₓ

end ConjClasses

section Monoidₓ

variable [Monoidₓ α]

/-- Given an element `a`, `conjugates a` is the set of conjugates. -/
def ConjugatesOf (a : α) : Set α :=
  { b | IsConj a b }

theorem mem_conjugates_of_self {a : α} : a ∈ ConjugatesOf a :=
  IsConj.refl _

theorem IsConj.conjugates_of_eq {a b : α} (ab : IsConj a b) : ConjugatesOf a = ConjugatesOf b :=
  Set.ext fun g => ⟨fun ag => ab.symm.trans ag, fun bg => ab.trans bg⟩

theorem is_conj_iff_conjugates_of_eq {a b : α} : IsConj a b ↔ ConjugatesOf a = ConjugatesOf b :=
  ⟨IsConj.conjugates_of_eq, fun h => by
    have ha := mem_conjugates_of_self
    rwa [← h] at ha⟩

instance [Fintype α] [DecidableRel (IsConj : α → α → Prop)] {a : α} : Fintype (ConjugatesOf a) :=
  @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

end Monoidₓ

namespace ConjClasses

variable [Monoidₓ α]

attribute [local instance] IsConj.setoid

/-- Given a conjugacy class `a`, `carrier a` is the set it represents. -/
def Carrier : ConjClasses α → Set α :=
  Quotientₓ.lift ConjugatesOf fun (a : α) b ab => IsConj.conjugates_of_eq ab

theorem mem_carrier_mk {a : α} : a ∈ Carrier (ConjClasses.mk a) :=
  IsConj.refl _

theorem mem_carrier_iff_mk_eq {a : α} {b : ConjClasses α} : a ∈ Carrier b ↔ ConjClasses.mk a = b := by
  revert b
  rw [forall_is_conj]
  intro b
  rw [carrier, eq_comm, mk_eq_mk_iff_is_conj, ← quotient_mk_eq_mk, Quotientₓ.lift_mk]
  rfl

theorem carrier_eq_preimage_mk {a : ConjClasses α} : a.Carrier = ConjClasses.mk ⁻¹' {a} :=
  Set.ext fun x => mem_carrier_iff_mk_eq

section Fintype

variable [Fintype α] [DecidableRel (IsConj : α → α → Prop)]

instance {x : ConjClasses α} : Fintype (Carrier x) :=
  (Quotientₓ.recOnSubsingleton x) fun a => ConjugatesOf.fintype

end Fintype

end ConjClasses

