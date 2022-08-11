/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.Hom.Basic

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `antisymm_rel`: The antisymmetrization relation. `antisymm_rel r a b` means that `a` and `b` are
  related both ways by `r`.
* `antisymmetrization α r`: The quotient of `α` by `antisymm_rel r`. Even when `r` is just a
  preorder, `antisymmetrization α` is a partial order.
-/


open Function OrderDual

variable {α β : Type _}

section Relation

variable (r : α → α → Prop)

/-- The antisymmetrization relation. -/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a

theorem antisymm_rel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext fun _ => funext fun _ => propext And.comm

@[refl]
theorem antisymm_rel_refl [IsRefl α r] (a : α) : AntisymmRel r a a :=
  ⟨refl _, refl _⟩

variable {r}

@[symm]
theorem AntisymmRel.symm {a b : α} : AntisymmRel r a b → AntisymmRel r b a :=
  And.symm

@[trans]
theorem AntisymmRel.trans [IsTrans α r] {a b c : α} (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c) :
    AntisymmRel r a c :=
  ⟨trans hab.1 hbc.1, trans hbc.2 hab.2⟩

instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) := fun _ _ => And.decidable

@[simp]
theorem antisymm_rel_iff_eq [IsRefl α r] [IsAntisymm α r] {a b : α} : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias antisymm_rel_iff_eq ↔ AntisymmRel.eq _

end Relation

section IsPreorder

variable (α) (r : α → α → Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps]
def AntisymmRel.setoid : Setoidₓ α :=
  ⟨AntisymmRel r, antisymm_rel_refl _, fun _ _ => AntisymmRel.symm, fun _ _ _ => AntisymmRel.trans⟩

/-- The partial order derived from a preorder by making pairwise comparable elements equal. This is
the quotient by `λ a b, a ≤ b ∧ b ≤ a`. -/
def Antisymmetrization : Type _ :=
  Quotientₓ <| AntisymmRel.setoid α r

variable {α}

/-- Turn an element into its antisymmetrization. -/
def toAntisymmetrization : α → Antisymmetrization α r :=
  Quotientₓ.mk'

/-- Get a representative from the antisymmetrization. -/
noncomputable def ofAntisymmetrization : Antisymmetrization α r → α :=
  Quotientₓ.out'

instance [Inhabited α] : Inhabited (Antisymmetrization α r) :=
  Quotientₓ.inhabited _

@[elab_as_eliminator]
protected theorem Antisymmetrization.ind {p : Antisymmetrization α r → Prop} :
    (∀ a, p <| toAntisymmetrization r a) → ∀ q, p q :=
  Quot.ind

@[elab_as_eliminator]
protected theorem Antisymmetrization.induction_on {p : Antisymmetrization α r → Prop} (a : Antisymmetrization α r)
    (h : ∀ a, p <| toAntisymmetrization r a) : p a :=
  Quotientₓ.induction_on' a h

@[simp]
theorem to_antisymmetrization_of_antisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotientₓ.out_eq' _

end IsPreorder

section Preorderₓ

variable {α} [Preorderₓ α] [Preorderₓ β] {a b : α}

theorem AntisymmRel.image {a b : α} (h : AntisymmRel (· ≤ ·) a b) {f : α → β} (hf : Monotone f) :
    AntisymmRel (· ≤ ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩

instance : PartialOrderₓ (Antisymmetrization α (· ≤ ·)) where
  le := fun a b =>
    (Quotientₓ.liftOn₂' a b (· ≤ ·)) fun (a₁ a₂ b₁ b₂ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans <| h.trans h₂.1, fun h => h₁.1.trans <| h.trans h₂.2⟩
  lt := fun a b =>
    (Quotientₓ.liftOn₂' a b (· < ·)) fun (a₁ a₂ b₁ b₂ : α) h₁ h₂ =>
      propext ⟨fun h => h₁.2.trans_lt <| h.trans_le h₂.1, fun h => h₁.1.trans_lt <| h.trans_le h₂.2⟩
  le_refl := fun a => Quotientₓ.induction_on' a <| le_reflₓ
  le_trans := fun a b c => (Quotientₓ.induction_on₃' a b c) fun a b c => le_transₓ
  lt_iff_le_not_le := fun a b => (Quotientₓ.induction_on₂' a b) fun a b => lt_iff_le_not_leₓ
  le_antisymm := fun a b => (Quotientₓ.induction_on₂' a b) fun a b hab hba => Quotientₓ.sound' ⟨hab, hba⟩

instance [@DecidableRel α (· ≤ ·)] [@DecidableRel α (· < ·)] [IsTotal α (· ≤ ·)] :
    LinearOrderₓ (Antisymmetrization α (· ≤ ·)) :=
  { Antisymmetrization.partialOrder with le_total := fun a b => Quotientₓ.induction_on₂' a b <| total_of (· ≤ ·),
    DecidableEq := @Quotientₓ.decidableEq _ (AntisymmRel.setoid _ (· ≤ ·)) AntisymmRel.decidableRel,
    decidableLe := fun _ _ => Quotientₓ.liftOn₂'.decidable _ _ _ _,
    decidableLt := fun _ _ => Quotientₓ.liftOn₂'.decidable _ _ _ _ }

@[simp]
theorem to_antisymmetrization_le_to_antisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) a ≤ toAntisymmetrization (· ≤ ·) b ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem to_antisymmetrization_lt_to_antisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) a < toAntisymmetrization (· ≤ ·) b ↔ a < b :=
  Iff.rfl

@[simp]
theorem of_antisymmetrization_le_of_antisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a ≤ ofAntisymmetrization (· ≤ ·) b ↔ a ≤ b := by
  convert to_antisymmetrization_le_to_antisymmetrization_iff.symm <;>
    exact (to_antisymmetrization_of_antisymmetrization _ _).symm

@[simp]
theorem of_antisymmetrization_lt_of_antisymmetrization_iff {a b : Antisymmetrization α (· ≤ ·)} :
    ofAntisymmetrization (· ≤ ·) a < ofAntisymmetrization (· ≤ ·) b ↔ a < b := by
  convert to_antisymmetrization_lt_to_antisymmetrization_iff.symm <;>
    exact (to_antisymmetrization_of_antisymmetrization _ _).symm

@[mono]
theorem to_antisymmetrization_mono : Monotone (@toAntisymmetrization α (· ≤ ·) _) := fun a b => id

/-- `to_antisymmetrization` as an order homomorphism. -/
@[simps]
def OrderHom.toAntisymmetrization : α →o Antisymmetrization α (· ≤ ·) :=
  ⟨toAntisymmetrization (· ≤ ·), fun a b => id⟩

private theorem lift_fun_antisymm_rel (f : α →o β) :
    ((AntisymmRel.setoid α (· ≤ ·)).R⇒(AntisymmRel.setoid β (· ≤ ·)).R) f f := fun a b h => ⟨f.mono h.1, f.mono h.2⟩

/-- Turns an order homomorphism from `α` to `β` into one from `antisymmetrization α` to
`antisymmetrization β`. `antisymmetrization` is actually a functor. See `Preorder_to_PartialOrder`.
-/
protected def OrderHom.antisymmetrization (f : α →o β) : Antisymmetrization α (· ≤ ·) →o Antisymmetrization β (· ≤ ·) :=
  ⟨Quotientₓ.map' f <| lift_fun_antisymm_rel f, fun a b => Quotientₓ.induction_on₂' a b <| f.mono⟩

@[simp]
theorem OrderHom.coe_antisymmetrization (f : α →o β) :
    ⇑f.Antisymmetrization = Quotientₓ.map' f (lift_fun_antisymm_rel f) :=
  rfl

@[simp]
theorem OrderHom.antisymmetrization_apply (f : α →o β) (a : Antisymmetrization α (· ≤ ·)) :
    f.Antisymmetrization a = Quotientₓ.map' f (lift_fun_antisymm_rel f) a :=
  rfl

@[simp]
theorem OrderHom.antisymmetrization_apply_mk (f : α →o β) (a : α) :
    f.Antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  Quotientₓ.map'_mk' f (lift_fun_antisymm_rel f) _

variable (α)

/-- `of_antisymmetrization` as an order embedding. -/
@[simps]
noncomputable def OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· ≤ ·) ↪o α where
  toFun := ofAntisymmetrization _
  inj' := fun _ _ => Quotientₓ.out_inj.1
  map_rel_iff' := fun a b => of_antisymmetrization_le_of_antisymmetrization_iff

/-- `antisymmetrization` and `order_dual` commute. -/
def OrderIso.dualAntisymmetrization : (Antisymmetrization α (· ≤ ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· ≤ ·) where
  toFun := (Quotientₓ.map' id) fun _ _ => And.symm
  invFun := (Quotientₓ.map' id) fun _ _ => And.symm
  left_inv := fun a =>
    (Quotientₓ.induction_on' a) fun a => by
      simp_rw [Quotientₓ.map'_mk', id]
  right_inv := fun a =>
    (Quotientₓ.induction_on' a) fun a => by
      simp_rw [Quotientₓ.map'_mk', id]
  map_rel_iff' := fun a b => (Quotientₓ.induction_on₂' a b) fun a b => Iff.rfl

@[simp]
theorem OrderIso.dual_antisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (to_dual <| toAntisymmetrization _ a) = toAntisymmetrization _ (toDual a) :=
  rfl

@[simp]
theorem OrderIso.dual_antisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) = toDual (toAntisymmetrization _ a) :=
  rfl

end Preorderₓ

