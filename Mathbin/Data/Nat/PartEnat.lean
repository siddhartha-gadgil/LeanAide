/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Algebra.Hom.Equiv
import Mathbin.Data.Part
import Mathbin.Tactic.NormNum

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`. This implementation uses `part ℕ` as an
implementation. Use `with_top ℕ` instead unless you care about computability.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid part_enat`
* `canonically_ordered_add_monoid part_enat`

There is no additive analogue of `monoid_with_zero`; if there were then `part_enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `part_enat` to `with_top ℕ`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : part_enat ≃+ with_top ℕ`
* `with_top_order_iso : part_enat ≃o with_top ℕ`

## Implementation details

`part_enat` is defined to be `part ℕ`.

`+` and `≤` are defined on `part_enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `part_enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

part_enat, with_top ℕ
-/


open Part hiding some

/-- Type of natural numbers with infinity (`⊤`) -/
def PartEnat : Type :=
  Part ℕ

namespace PartEnat

/-- The computable embedding `ℕ → part_enat`.

This coincides with the coercion `coe : ℕ → part_enat`, see `part_enat.some_eq_coe`.
However, `coe` is noncomputable so `some` is preferable when computability is a concern. -/
def some : ℕ → PartEnat :=
  Part.some

instance : Zero PartEnat :=
  ⟨some 0⟩

instance : Inhabited PartEnat :=
  ⟨0⟩

instance : One PartEnat :=
  ⟨some 1⟩

instance : Add PartEnat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => get x h.1 + get y h.2⟩⟩

instance (n : ℕ) : Decidable (some n).Dom :=
  isTrue trivialₓ

@[simp]
theorem dom_some (x : ℕ) : (some x).Dom :=
  trivialₓ

instance : AddCommMonoidₓ PartEnat where
  add := (· + ·)
  zero := 0
  add_comm := fun x y => Part.ext' And.comm fun _ _ => add_commₓ _ _
  zero_add := fun x => Part.ext' (true_andₓ _) fun _ _ => zero_addₓ _
  add_zero := fun x => Part.ext' (and_trueₓ _) fun _ _ => add_zeroₓ _
  add_assoc := fun x y z => Part.ext' And.assoc fun _ _ => add_assocₓ _ _ _

instance : AddMonoidWithOneₓ PartEnat :=
  { PartEnat.addCommMonoid with one := 1, natCast := some, nat_cast_zero := rfl,
    nat_cast_succ := fun _ => Part.ext' (true_andₓ _).symm fun _ _ => rfl }

theorem some_eq_coe (n : ℕ) : some n = n :=
  rfl

@[simp]
theorem coe_inj {x y : ℕ} : (x : PartEnat) = y ↔ x = y :=
  Part.some_inj

@[simp]
theorem dom_coe (x : ℕ) : (x : PartEnat).Dom :=
  trivialₓ

instance : LE PartEnat :=
  ⟨fun x y => ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy⟩

instance : HasTop PartEnat :=
  ⟨none⟩

instance : HasBot PartEnat :=
  ⟨0⟩

instance : HasSup PartEnat :=
  ⟨fun x y => ⟨x.Dom ∧ y.Dom, fun h => x.get h.1⊔y.get h.2⟩⟩

theorem le_def (x y : PartEnat) : x ≤ y ↔ ∃ h : y.Dom → x.Dom, ∀ hy : y.Dom, x.get (h hy) ≤ y.get hy :=
  Iff.rfl

@[elab_as_eliminator]
protected theorem cases_on' {P : PartEnat → Prop} : ∀ a : PartEnat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
  Part.induction_on

@[elab_as_eliminator]
protected theorem cases_on {P : PartEnat → Prop} : ∀ a : PartEnat, P ⊤ → (∀ n : ℕ, P n) → P a := by
  simp only [some_eq_coe]
  exact PartEnat.cases_on'

@[simp]
theorem top_add (x : PartEnat) : ⊤ + x = ⊤ :=
  Part.ext' (false_andₓ _) fun h => h.left.elim

@[simp]
theorem add_top (x : PartEnat) : x + ⊤ = ⊤ := by
  rw [add_commₓ, top_add]

@[simp]
theorem coe_get {x : PartEnat} (h : x.Dom) : (x.get h : PartEnat) = x := by
  rw [← some_eq_coe]
  exact Part.ext' (iff_of_true trivialₓ h) fun _ _ => rfl

@[simp, norm_cast]
theorem get_coe' (x : ℕ) (h : (x : PartEnat).Dom) : get (x : PartEnat) h = x := by
  rw [← coe_inj, coe_get]

theorem get_coe {x : ℕ} : get (x : PartEnat) (dom_coe x) = x :=
  get_coe' _ _

theorem coe_add_get {x : ℕ} {y : PartEnat} (h : ((x : PartEnat) + y).Dom) :
    get ((x : PartEnat) + y) h = x + get y h.2 := by
  simp only [some_eq_coe] at h⊢
  rfl

@[simp]
theorem get_add {x y : PartEnat} (h : (x + y).Dom) : get (x + y) h = x.get h.1 + y.get h.2 :=
  rfl

@[simp]
theorem get_zero (h : (0 : PartEnat).Dom) : (0 : PartEnat).get h = 0 :=
  rfl

@[simp]
theorem get_one (h : (1 : PartEnat).Dom) : (1 : PartEnat).get h = 1 :=
  rfl

theorem get_eq_iff_eq_some {a : PartEnat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = some b :=
  get_eq_iff_eq_some

theorem get_eq_iff_eq_coe {a : PartEnat} {ha : a.Dom} {b : ℕ} : a.get ha = b ↔ a = b := by
  rw [get_eq_iff_eq_some, some_eq_coe]

theorem dom_of_le_of_dom {x y : PartEnat} : x ≤ y → y.Dom → x.Dom := fun ⟨h, _⟩ => h

theorem dom_of_le_some {x : PartEnat} {y : ℕ} (h : x ≤ some y) : x.Dom :=
  dom_of_le_of_dom h trivialₓ

theorem dom_of_le_coe {x : PartEnat} {y : ℕ} (h : x ≤ y) : x.Dom := by
  rw [← some_eq_coe] at h
  exact dom_of_le_some h

instance decidableLe (x y : PartEnat) [Decidable x.Dom] [Decidable y.Dom] : Decidable (x ≤ y) :=
  if hx : x.Dom then
    decidableOfDecidableOfIff
        (show Decidable (∀ hy : (y : PartEnat).Dom, x.get hx ≤ (y : PartEnat).get hy) from forallPropDecidable _) <|
      by
      dsimp' [← (· ≤ ·)]
      simp only [← hx, ← exists_prop_of_true, ← forall_true_iff]
  else
    if hy : y.Dom then is_false fun h => hx <| dom_of_le_of_dom h hy
    else isTrue ⟨fun h => (hy h).elim, fun h => (hy h).elim⟩

/-- The coercion `ℕ → part_enat` preserves `0` and addition. -/
def coeHom : ℕ →+ PartEnat :=
  ⟨coe, Nat.cast_zeroₓ, Nat.cast_addₓ⟩

@[simp]
theorem coe_coe_hom : ⇑coe_hom = coe :=
  rfl

instance : PartialOrderₓ PartEnat where
  le := (· ≤ ·)
  le_refl := fun x => ⟨id, fun _ => le_rfl⟩
  le_trans := fun x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩ => ⟨hxy₁ ∘ hyz₁, fun _ => le_transₓ (hxy₂ _) (hyz₂ _)⟩
  le_antisymm := fun x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩ => Part.ext' ⟨hyx₁, hxy₁⟩ fun _ _ => le_antisymmₓ (hxy₂ _) (hyx₂ _)

theorem lt_def (x y : PartEnat) : x < y ↔ ∃ hx : x.Dom, ∀ hy : y.Dom, x.get hx < y.get hy := by
  rw [lt_iff_le_not_leₓ, le_def, le_def, not_exists]
  constructor
  · rintro ⟨⟨hyx, H⟩, h⟩
    by_cases' hx : x.dom
    · use hx
      intro hy
      specialize H hy
      specialize h fun _ => hy
      rw [not_forall] at h
      cases' h with hx' h
      rw [not_leₓ] at h
      exact h
      
    · specialize h fun hx' => (hx hx').elim
      rw [not_forall] at h
      cases' h with hx' h
      exact (hx hx').elim
      
    
  · rintro ⟨hx, H⟩
    exact ⟨⟨fun _ => hx, fun hy => (H hy).le⟩, fun hxy h => not_lt_of_le (h _) (H _)⟩
    

@[simp, norm_cast]
theorem coe_le_coe {x y : ℕ} : (x : PartEnat) ≤ y ↔ x ≤ y := by
  rw [← some_eq_coe, ← some_eq_coe]
  exact ⟨fun ⟨_, h⟩ => h trivialₓ, fun h => ⟨fun _ => trivialₓ, fun _ => h⟩⟩

@[simp, norm_cast]
theorem coe_lt_coe {x y : ℕ} : (x : PartEnat) < y ↔ x < y := by
  rw [lt_iff_le_not_leₓ, lt_iff_le_not_leₓ, coe_le_coe, coe_le_coe]

@[simp]
theorem get_le_get {x y : PartEnat} {hx : x.Dom} {hy : y.Dom} : x.get hx ≤ y.get hy ↔ x ≤ y := by
  conv => lhs rw [← coe_le_coe, coe_get, coe_get]

theorem le_coe_iff (x : PartEnat) (n : ℕ) : x ≤ n ↔ ∃ h : x.Dom, x.get h ≤ n := by
  rw [← some_eq_coe]
  show (∃ h : True → x.dom, _) ↔ ∃ h : x.dom, x.get h ≤ n
  simp only [← forall_prop_of_true, ← some_eq_coe, ← dom_coe, ← get_coe']

theorem lt_coe_iff (x : PartEnat) (n : ℕ) : x < n ↔ ∃ h : x.Dom, x.get h < n := by
  simp only [← lt_def, ← forall_prop_of_true, ← get_coe', ← dom_coe]

theorem coe_le_iff (n : ℕ) (x : PartEnat) : (n : PartEnat) ≤ x ↔ ∀ h : x.Dom, n ≤ x.get h := by
  rw [← some_eq_coe]
  simp only [← le_def, ← exists_prop_of_true, ← dom_some, ← forall_true_iff]
  rfl

theorem coe_lt_iff (n : ℕ) (x : PartEnat) : (n : PartEnat) < x ↔ ∀ h : x.Dom, n < x.get h := by
  rw [← some_eq_coe]
  simp only [← lt_def, ← exists_prop_of_true, ← dom_some, ← forall_true_iff]
  rfl

protected theorem zero_lt_one : (0 : PartEnat) < 1 := by
  norm_cast
  norm_num

instance semilatticeSup : SemilatticeSup PartEnat :=
  { PartEnat.partialOrder with sup := (·⊔·), le_sup_left := fun _ _ => ⟨And.left, fun _ => le_sup_left⟩,
    le_sup_right := fun _ _ => ⟨And.right, fun _ => le_sup_right⟩,
    sup_le := fun x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ => ⟨fun hz => ⟨hx₁ hz, hy₁ hz⟩, fun _ => sup_le (hx₂ _) (hy₂ _)⟩ }

instance orderBot : OrderBot PartEnat where
  bot := ⊥
  bot_le := fun _ => ⟨fun _ => trivialₓ, fun _ => Nat.zero_leₓ _⟩

instance orderTop : OrderTop PartEnat where
  top := ⊤
  le_top := fun x => ⟨fun h => False.elim h, fun hy => False.elim hy⟩

theorem eq_zero_iff {x : PartEnat} : x = 0 ↔ x ≤ 0 :=
  eq_bot_iff

theorem ne_zero_iff {x : PartEnat} : x ≠ 0 ↔ ⊥ < x :=
  bot_lt_iff_ne_bot.symm

theorem dom_of_lt {x y : PartEnat} : x < y → x.Dom :=
  (PartEnat.cases_on x not_top_lt) fun _ _ => dom_coe _

theorem top_eq_none : (⊤ : PartEnat) = none :=
  rfl

@[simp]
theorem coe_lt_top (x : ℕ) : (x : PartEnat) < ⊤ :=
  Ne.lt_top fun h =>
    absurd (congr_arg Dom h) <| by
      simpa only [← dom_coe] using true_ne_false

@[simp]
theorem coe_ne_top (x : ℕ) : (x : PartEnat) ≠ ⊤ :=
  ne_of_ltₓ (coe_lt_top x)

theorem not_is_max_coe (x : ℕ) : ¬IsMax (x : PartEnat) :=
  not_is_max_of_lt (coe_lt_top x)

theorem ne_top_iff {x : PartEnat} : x ≠ ⊤ ↔ ∃ n : ℕ, x = n := by
  simpa only [some_eq_coe] using Part.ne_none_iff

theorem ne_top_iff_dom {x : PartEnat} : x ≠ ⊤ ↔ x.Dom := by
  classical <;> exact not_iff_comm.1 part.eq_none_iff'.symm

theorem not_dom_iff_eq_top {x : PartEnat} : ¬x.Dom ↔ x = ⊤ :=
  Iff.not_left ne_top_iff_dom.symm

theorem ne_top_of_lt {x y : PartEnat} (h : x < y) : x ≠ ⊤ :=
  ne_of_ltₓ <| lt_of_lt_of_leₓ h le_top

theorem eq_top_iff_forall_lt (x : PartEnat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartEnat) < x := by
  constructor
  · rintro rfl n
    exact coe_lt_top _
    
  · contrapose!
    rw [ne_top_iff]
    rintro ⟨n, rfl⟩
    exact ⟨n, irrefl _⟩
    

theorem eq_top_iff_forall_le (x : PartEnat) : x = ⊤ ↔ ∀ n : ℕ, (n : PartEnat) ≤ x :=
  (eq_top_iff_forall_lt x).trans
    ⟨fun h n => (h n).le, fun h n => lt_of_lt_of_leₓ (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩

theorem pos_iff_one_le {x : PartEnat} : 0 < x ↔ 1 ≤ x :=
  (PartEnat.cases_on x
      (by
        simp only [← iff_trueₓ, ← le_top, ← coe_lt_top, @Nat.cast_zeroₓ PartEnat]))
    fun n => by
    rw [← Nat.cast_zeroₓ, ← Nat.cast_oneₓ, PartEnat.coe_lt_coe, PartEnat.coe_le_coe]
    rfl

instance :
    IsTotal PartEnat
      (· ≤
        ·) where Total := fun x y =>
    PartEnat.cases_on x (Or.inr le_top)
      (PartEnat.cases_on y (fun _ => Or.inl le_top) fun x y =>
        (le_totalₓ x y).elim (Or.inr ∘ coe_le_coe.2) (Or.inl ∘ coe_le_coe.2))

noncomputable instance : LinearOrderₓ PartEnat :=
  { PartEnat.partialOrder with le_total := IsTotal.total, decidableLe := Classical.decRel _, max := (·⊔·),
    max_def := @sup_eq_max_default _ _ (id _) _ }

instance : BoundedOrder PartEnat :=
  { PartEnat.orderTop, PartEnat.orderBot with }

noncomputable instance : Lattice PartEnat :=
  { PartEnat.semilatticeSup with inf := min, inf_le_left := min_le_leftₓ, inf_le_right := min_le_rightₓ,
    le_inf := fun _ _ _ => le_minₓ }

instance : OrderedAddCommMonoid PartEnat :=
  { PartEnat.linearOrder, PartEnat.addCommMonoid with
    add_le_add_left := fun a b ⟨h₁, h₂⟩ c =>
      PartEnat.cases_on c
        (by
          simp )
        fun c =>
        ⟨fun h => And.intro (dom_coe _) (h₁ h.2), fun h => by
          simpa only [← coe_add_get] using add_le_add_left (h₂ _) c⟩ }

instance : CanonicallyOrderedAddMonoid PartEnat :=
  { PartEnat.semilatticeSup, PartEnat.orderBot, PartEnat.orderedAddCommMonoid with
    le_self_add := fun a b =>
      (PartEnat.cases_on b (le_top.trans_eq (add_top _).symm)) fun b =>
        (PartEnat.cases_on a (top_add _).Ge) fun a => (coe_le_coe.2 le_self_add).trans_eq (Nat.cast_addₓ _ _),
    exists_add_of_le := fun a b =>
      (PartEnat.cases_on b fun _ => ⟨⊤, (add_top _).symm⟩) fun b =>
        (PartEnat.cases_on a fun h => ((coe_lt_top _).not_le h).elim) fun a h =>
          ⟨(b - a : ℕ), by
            rw [← Nat.cast_addₓ, coe_inj, add_commₓ, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩ }

protected theorem add_lt_add_right {x y z : PartEnat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z := by
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩
  induction' y using PartEnat.cases_on with n
  · rw [top_add]
    apply_mod_cast coe_lt_top
    
  norm_cast  at h
  apply_mod_cast add_lt_add_right h

protected theorem add_lt_add_iff_right {x y z : PartEnat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
  ⟨lt_of_add_lt_add_right, fun h => PartEnat.add_lt_add_right h hz⟩

protected theorem add_lt_add_iff_left {x y z : PartEnat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y := by
  rw [add_commₓ z, add_commₓ z, PartEnat.add_lt_add_iff_right hz]

protected theorem lt_add_iff_pos_right {x y : PartEnat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y := by
  conv_rhs => rw [← PartEnat.add_lt_add_iff_left hx]
  rw [add_zeroₓ]

theorem lt_add_one {x : PartEnat} (hx : x ≠ ⊤) : x < x + 1 := by
  rw [PartEnat.lt_add_iff_pos_right hx]
  norm_cast
  norm_num

theorem le_of_lt_add_one {x y : PartEnat} (h : x < y + 1) : x ≤ y := by
  induction' y using PartEnat.cases_on with n
  apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.le_of_lt_succₓ
  apply_mod_cast h

theorem add_one_le_of_lt {x y : PartEnat} (h : x < y) : x + 1 ≤ y := by
  induction' y using PartEnat.cases_on with n
  apply le_top
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩
  apply_mod_cast Nat.succ_le_of_ltₓ
  apply_mod_cast h

theorem add_one_le_iff_lt {x y : PartEnat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y := by
  constructor
  swap
  exact add_one_le_of_lt
  intro h
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using PartEnat.cases_on with n
  apply coe_lt_top
  apply_mod_cast Nat.lt_of_succ_leₓ
  apply_mod_cast h

theorem lt_add_one_iff_lt {x y : PartEnat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y := by
  constructor
  exact le_of_lt_add_one
  intro h
  rcases ne_top_iff.mp hx with ⟨m, rfl⟩
  induction' y using PartEnat.cases_on with n
  · rw [top_add]
    apply coe_lt_top
    
  apply_mod_cast Nat.lt_succ_of_leₓ
  apply_mod_cast h

theorem add_eq_top_iff {a b : PartEnat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  apply PartEnat.cases_on a <;>
    apply PartEnat.cases_on b <;> simp <;> simp only [← (Nat.cast_addₓ _ _).symm, ← PartEnat.coe_ne_top] <;> simp

protected theorem add_right_cancel_iff {a b c : PartEnat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b := by
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩
  apply PartEnat.cases_on a <;>
    apply PartEnat.cases_on b <;>
      simp [← add_eq_top_iff, ← coe_ne_top, ← @eq_comm _ (⊤ : PartEnat)] <;>
        simp only [← (Nat.cast_addₓ _ _).symm, ← add_left_cancel_iffₓ, ← PartEnat.coe_inj, ← add_commₓ] <;> tauto

protected theorem add_left_cancel_iff {a b c : PartEnat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c := by
  rw [add_commₓ a, add_commₓ a, PartEnat.add_right_cancel_iff ha]

section WithTop

/-- Computably converts an `part_enat` to a `with_top ℕ`. -/
def toWithTop (x : PartEnat) [Decidable x.Dom] : WithTop ℕ :=
  x.toOption

theorem to_with_top_top : toWithTop ⊤ = ⊤ :=
  rfl

@[simp]
theorem to_with_top_top' {h : Decidable (⊤ : PartEnat).Dom} : toWithTop ⊤ = ⊤ := by
  convert to_with_top_top

theorem to_with_top_zero : toWithTop 0 = 0 :=
  rfl

@[simp]
theorem to_with_top_zero' {h : Decidable (0 : PartEnat).Dom} : toWithTop 0 = 0 := by
  convert to_with_top_zero

theorem to_with_top_some (n : ℕ) : toWithTop (some n) = n :=
  rfl

theorem to_with_top_coe (n : ℕ) {_ : Decidable (n : PartEnat).Dom} : toWithTop n = n := by
  simp only [some_eq_coe, to_with_top_some]

@[simp]
theorem to_with_top_coe' (n : ℕ) {h : Decidable (n : PartEnat).Dom} : toWithTop (n : PartEnat) = n := by
  convert to_with_top_coe n

@[simp]
theorem to_with_top_le {x y : PartEnat} :
    ∀ [Decidable x.Dom] [Decidable y.Dom], to_with_top x ≤ to_with_top y ↔ x ≤ y :=
  PartEnat.cases_on y
    (by
      simp )
    (PartEnat.cases_on x
      (by
        simp )
      (by
        intros <;> simp ))

@[simp]
theorem to_with_top_lt {x y : PartEnat} [Decidable x.Dom] [Decidable y.Dom] : toWithTop x < toWithTop y ↔ x < y :=
  lt_iff_lt_of_le_iff_le to_with_top_le

end WithTop

section WithTopEquiv

open Classical

@[simp]
theorem to_with_top_add {x y : PartEnat} : toWithTop (x + y) = toWithTop x + toWithTop y := by
  apply PartEnat.cases_on y <;> apply PartEnat.cases_on x <;> simp [Nat.cast_addₓ, WithTop.coe_add]

/-- `equiv` between `part_enat` and `with_top ℕ` (for the order isomorphism see
`with_top_order_iso`). -/
noncomputable def withTopEquiv : PartEnat ≃ WithTop ℕ where
  toFun := fun x => toWithTop x
  invFun := fun x =>
    match x with
    | Option.some n => coe n
    | none => ⊤
  left_inv := fun x => by
    apply PartEnat.cases_on x <;> intros <;> simp <;> rfl
  right_inv := fun x => by
    cases x <;> simp [← with_top_equiv._match_1] <;> rfl

@[simp]
theorem with_top_equiv_top : withTopEquiv ⊤ = ⊤ :=
  to_with_top_top'

@[simp]
theorem with_top_equiv_coe (n : Nat) : withTopEquiv n = n :=
  to_with_top_coe' _

@[simp]
theorem with_top_equiv_zero : withTopEquiv 0 = 0 := by
  simpa only [← Nat.cast_zeroₓ] using with_top_equiv_coe 0

@[simp]
theorem with_top_equiv_le {x y : PartEnat} : withTopEquiv x ≤ withTopEquiv y ↔ x ≤ y :=
  to_with_top_le

@[simp]
theorem with_top_equiv_lt {x y : PartEnat} : withTopEquiv x < withTopEquiv y ↔ x < y :=
  to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `part_enat` and `with_top ℕ`. -/
noncomputable def withTopOrderIso : PartEnat ≃o WithTop ℕ :=
  { withTopEquiv with map_rel_iff' := fun _ _ => with_top_equiv_le }

@[simp]
theorem with_top_equiv_symm_top : withTopEquiv.symm ⊤ = ⊤ :=
  rfl

@[simp]
theorem with_top_equiv_symm_coe (n : Nat) : withTopEquiv.symm n = n :=
  rfl

@[simp]
theorem with_top_equiv_symm_zero : withTopEquiv.symm 0 = 0 :=
  rfl

@[simp]
theorem with_top_equiv_symm_le {x y : WithTop ℕ} : withTopEquiv.symm x ≤ withTopEquiv.symm y ↔ x ≤ y := by
  rw [← with_top_equiv_le] <;> simp

@[simp]
theorem with_top_equiv_symm_lt {x y : WithTop ℕ} : withTopEquiv.symm x < withTopEquiv.symm y ↔ x < y := by
  rw [← with_top_equiv_lt] <;> simp

/-- `to_with_top` induces an additive monoid isomorphism between `part_enat` and `with_top ℕ`. -/
noncomputable def withTopAddEquiv : PartEnat ≃+ WithTop ℕ :=
  { withTopEquiv with
    map_add' := fun x y => by
      simp only [← with_top_equiv] <;> convert to_with_top_add }

end WithTopEquiv

theorem lt_wf : @WellFounded PartEnat (· < ·) := by
  classical
  change WellFounded fun a b : PartEnat => a < b
  simp_rw [← to_with_top_lt]
  exact InvImage.wfₓ _ (WithTop.well_founded_lt Nat.lt_wf)

instance : IsWellOrder PartEnat (· < ·) :=
  ⟨lt_wf⟩

instance : HasWellFounded PartEnat :=
  ⟨(· < ·), lt_wf⟩

section Find

variable (P : ℕ → Prop) [DecidablePred P]

/-- The smallest `part_enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : PartEnat :=
  ⟨∃ n, P n, Nat.findₓ⟩

@[simp]
theorem find_get (h : (find P).Dom) : (find P).get h = Nat.findₓ h :=
  rfl

theorem find_dom (h : ∃ n, P n) : (find P).Dom :=
  h

theorem lt_find (n : ℕ) (h : ∀, ∀ m ≤ n, ∀, ¬P m) : (n : PartEnat) < find P := by
  rw [coe_lt_iff]
  intro h'
  rw [find_get]
  have := @Nat.find_specₓ P _ h'
  contrapose! this
  exact h _ this

theorem lt_find_iff (n : ℕ) : (n : PartEnat) < find P ↔ ∀, ∀ m ≤ n, ∀, ¬P m := by
  refine' ⟨_, lt_find P n⟩
  intro h m hm
  by_cases' H : (find P).Dom
  · apply Nat.find_minₓ H
    rw [coe_lt_iff] at h
    specialize h H
    exact lt_of_le_of_ltₓ hm h
    
  · exact not_exists.mp H m
    

theorem find_le (n : ℕ) (h : P n) : find P ≤ n := by
  rw [le_coe_iff]
  refine' ⟨⟨_, h⟩, @Nat.find_min'ₓ P _ _ _ h⟩

theorem find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
  (eq_top_iff_forall_lt _).trans
    ⟨fun h n => (lt_find_iff P n).mp (h n) _ le_rfl, fun h n => (lt_find P n) fun _ _ => h _⟩

end Find

noncomputable instance : LinearOrderedAddCommMonoidWithTop PartEnat :=
  { PartEnat.linearOrder, PartEnat.orderedAddCommMonoid, PartEnat.orderTop with top_add' := top_add }

end PartEnat

