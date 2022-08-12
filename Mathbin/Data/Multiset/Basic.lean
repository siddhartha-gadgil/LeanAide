/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Bool.AllAny
import Mathbin.Data.List.Perm

/-!
# Multisets
These are implemented as the quotient of a list by permutations.
## Notation
We define the global infix notation `::ₘ` for `multiset.cons`.
-/


open List Subtype Nat

variable {α : Type _} {β : Type _} {γ : Type _}

/-- `multiset α` is the quotient of `list α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def Multiset.{u} (α : Type u) : Type u :=
  Quotientₓ (List.isSetoid α)

namespace Multiset

instance : Coe (List α) (Multiset α) :=
  ⟨Quot.mk _⟩

@[simp]
theorem quot_mk_to_coe (l : List α) : @Eq (Multiset α) ⟦l⟧ l :=
  rfl

@[simp]
theorem quot_mk_to_coe' (l : List α) : @Eq (Multiset α) (Quot.mk (· ≈ ·) l) l :=
  rfl

@[simp]
theorem quot_mk_to_coe'' (l : List α) : @Eq (Multiset α) (Quot.mk Setoidₓ.R l) l :=
  rfl

@[simp]
theorem coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l₂ ↔ l₁ ~ l₂ :=
  Quotientₓ.eq

instance hasDecidableEq [DecidableEq α] : DecidableEq (Multiset α)
  | s₁, s₂ => (Quotientₓ.recOnSubsingleton₂ s₁ s₂) fun l₁ l₂ => decidableOfIff' _ Quotientₓ.eq

/-- defines a size for a multiset by referring to the size of the underlying list -/
protected def sizeof [SizeOf α] (s : Multiset α) : ℕ :=
  (Quot.liftOn s sizeof) fun l₁ l₂ => Perm.sizeof_eq_sizeof

instance hasSizeof [SizeOf α] : SizeOf (Multiset α) :=
  ⟨Multiset.sizeof⟩

/-! ### Empty multiset -/


/-- `0 : multiset α` is the empty set -/
protected def zero : Multiset α :=
  @nil α

instance : Zero (Multiset α) :=
  ⟨Multiset.zero⟩

instance : HasEmptyc (Multiset α) :=
  ⟨0⟩

instance inhabitedMultiset : Inhabited (Multiset α) :=
  ⟨0⟩

@[simp]
theorem coe_nil_eq_zero : (@nil α : Multiset α) = 0 :=
  rfl

@[simp]
theorem empty_eq_zero : (∅ : Multiset α) = 0 :=
  rfl

@[simp]
theorem coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ l = [] :=
  Iff.trans coe_eq_coe perm_nil

/-! ### `multiset.cons` -/


/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (a :: l : Multiset α)) fun l₁ l₂ p => Quot.sound (p.cons a)

-- mathport name: «expr ::ₘ »
infixr:67 " ::ₘ " => Multiset.cons

instance : HasInsert α (Multiset α) :=
  ⟨cons⟩

@[simp]
theorem insert_eq_cons (a : α) (s : Multiset α) : insert a s = a ::ₘ s :=
  rfl

@[simp]
theorem cons_coe (a : α) (l : List α) : (a ::ₘ l : Multiset α) = (a :: l : List α) :=
  rfl

theorem singleton_coe (a : α) : (a ::ₘ 0 : Multiset α) = ([a] : List α) :=
  rfl

@[simp]
theorem cons_inj_left {a b : α} (s : Multiset α) : a ::ₘ s = b ::ₘ s ↔ a = b :=
  ⟨(Quot.induction_on s) fun l e =>
      have : [a] ++ l ~ [b] ++ l := Quotientₓ.exact e
      singleton_perm_singleton.1 <| (perm_append_right_iff _).1 this,
    congr_arg _⟩

@[simp]
theorem cons_inj_right (a : α) : ∀ {s t : Multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t := by
  rintro ⟨l₁⟩ ⟨l₂⟩ <;> simp

@[recursor 5]
protected theorem induction {p : Multiset α → Prop} (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : Multiset α}, p s → p (a ::ₘ s)) :
    ∀ s, p s := by
  rintro ⟨l⟩ <;> induction' l with _ _ ih <;> [exact h₁, exact h₂ ih]

@[elab_as_eliminator]
protected theorem induction_on {p : Multiset α → Prop} (s : Multiset α) (h₁ : p 0)
    (h₂ : ∀ ⦃a : α⦄ {s : Multiset α}, p s → p (a ::ₘ s)) : p s :=
  Multiset.induction h₁ h₂ s

theorem cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
  (Quot.induction_on s) fun l => Quotientₓ.sound <| Perm.swap _ _ _

section Rec

variable {C : Multiset α → Sort _}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq : ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b)))
    (m : Multiset α) : C m :=
  (Quotientₓ.hrecOn m (@List.rec α (fun l => C ⟦l⟧) C_0 fun a l b => C_cons a ⟦l⟧ b)) fun l l' h =>
    h.rec_heq
      (fun a l l' b b' hl => by
        have : ⟦l⟧ = ⟦l'⟧ := Quot.sound hl
        cc)
      fun a a' l => C_cons_heq a a' ⟦l⟧

/-- Companion to `multiset.rec` with more convenient argument order. -/
@[elab_as_eliminator]
protected def recOn (m : Multiset α) (C_0 : C 0) (C_cons : ∀ a m, C m → C (a ::ₘ m))
    (C_cons_heq : ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))) : C m :=
  Multiset.rec C_0 C_cons C_cons_heq m

variable {C_0 : C 0} {C_cons : ∀ a m, C m → C (a ::ₘ m)}
  {C_cons_heq : ∀ a a' m b, HEq (C_cons a (a' ::ₘ m) (C_cons a' m b)) (C_cons a' (a ::ₘ m) (C_cons a m b))}

@[simp]
theorem rec_on_0 : @Multiset.recOn α C (0 : Multiset α) C_0 C_cons C_cons_heq = C_0 :=
  rfl

@[simp]
theorem rec_on_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).recOn C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq) :=
  (Quotientₓ.induction_on m) fun l => rfl

end Rec

section Mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def Mem (a : α) (s : Multiset α) : Prop :=
  Quot.liftOn s (fun l => a ∈ l) fun l₁ l₂ (e : l₁ ~ l₂) => propext <| e.mem_iff

instance : HasMem α (Multiset α) :=
  ⟨Mem⟩

@[simp]
theorem mem_coe {a : α} {l : List α} : a ∈ (l : Multiset α) ↔ a ∈ l :=
  Iff.rfl

instance decidableMem [DecidableEq α] (a : α) (s : Multiset α) : Decidable (a ∈ s) :=
  Quot.recOnSubsingleton s <| List.decidableMem a

@[simp]
theorem mem_cons {a b : α} {s : Multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
  (Quot.induction_on s) fun l => Iff.rfl

theorem mem_cons_of_mem {a b : α} {s : Multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
  mem_cons.2 <| Or.inr h

@[simp]
theorem mem_cons_self (a : α) (s : Multiset α) : a ∈ a ::ₘ s :=
  mem_cons.2 (Or.inl rfl)

theorem forall_mem_cons {p : α → Prop} {a : α} {s : Multiset α} :
    (∀, ∀ x ∈ a ::ₘ s, ∀, p x) ↔ p a ∧ ∀, ∀ x ∈ s, ∀, p x :=
  (Quotientₓ.induction_on' s) fun L => List.forall_mem_consₓ

theorem exists_cons_of_mem {s : Multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
  (Quot.induction_on s) fun l (h : a ∈ l) =>
    let ⟨l₁, l₂, e⟩ := mem_split h
    e.symm ▸ ⟨(l₁ ++ l₂ : List α), Quot.sound perm_middle⟩

@[simp]
theorem not_mem_zero (a : α) : a ∉ (0 : Multiset α) :=
  id

theorem eq_zero_of_forall_not_mem {s : Multiset α} : (∀ x, x ∉ s) → s = 0 :=
  (Quot.induction_on s) fun l H => by
    rw [eq_nil_iff_forall_not_mem.mpr H] <;> rfl

theorem eq_zero_iff_forall_not_mem {s : Multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
  ⟨fun h => h.symm ▸ fun _ => not_false, eq_zero_of_forall_not_mem⟩

theorem exists_mem_of_ne_zero {s : Multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
  (Quot.induction_on s) fun l hl =>
    match l, hl with
    | [] => fun h => False.elim <| h rfl
    | a :: l => fun _ =>
      ⟨a, by
        simp ⟩

theorem empty_or_exists_mem (s : Multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
  or_iff_not_imp_left.mpr Multiset.exists_mem_of_ne_zero

@[simp]
theorem zero_ne_cons {a : α} {m : Multiset α} : 0 ≠ a ::ₘ m := fun h =>
  have : a ∈ (0 : Multiset α) := h.symm ▸ mem_cons_self _ _
  not_mem_zero _ this

@[simp]
theorem cons_ne_zero {a : α} {m : Multiset α} : a ::ₘ m ≠ 0 :=
  zero_ne_cons.symm

theorem cons_eq_cons {a b : α} {as bs : Multiset α} :
    a ::ₘ as = b ::ₘ bs ↔ a = b ∧ as = bs ∨ a ≠ b ∧ ∃ cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs := by
  have : DecidableEq α := Classical.decEq α
  constructor
  · intro eq
    by_cases' a = b
    · subst h
      simp_all
      
    · have : a ∈ b ::ₘ bs := Eq ▸ mem_cons_self _ _
      have : a ∈ bs := by
        simpa [← h]
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩
      simp [← h, ← hcs]
      have : a ::ₘ as = b ::ₘ a ::ₘ cs := by
        simp [← Eq, ← hcs]
      have : a ::ₘ as = a ::ₘ b ::ₘ cs := by
        rwa [cons_swap]
      simpa using this
      
    
  · intro h
    rcases h with (⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩)
    · simp [*]
      
    · simp [*, ← cons_swap a b]
      
    

end Mem

/-! ### `multiset.subset` -/


section Subset

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def Subset (s t : Multiset α) : Prop :=
  ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : HasSubset (Multiset α) :=
  ⟨Multiset.Subset⟩

instance : HasSsubset (Multiset α) :=
  ⟨fun s t => s ⊆ t ∧ ¬t ⊆ s⟩

@[simp]
theorem coe_subset {l₁ l₂ : List α} : (l₁ : Multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ :=
  Iff.rfl

@[simp]
theorem Subset.refl (s : Multiset α) : s ⊆ s := fun a h => h

theorem Subset.trans {s t u : Multiset α} : s ⊆ t → t ⊆ u → s ⊆ u := fun h₁ h₂ a m => h₂ (h₁ m)

theorem subset_iff {s t : Multiset α} : s ⊆ t ↔ ∀ ⦃x⦄, x ∈ s → x ∈ t :=
  Iff.rfl

theorem mem_of_subset {s t : Multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t :=
  @h _

@[simp]
theorem zero_subset (s : Multiset α) : 0 ⊆ s := fun a => (not_mem_nilₓ a).elim

theorem subset_cons (s : Multiset α) (a : α) : s ⊆ a ::ₘ s := fun _ => mem_cons_of_mem

theorem ssubset_cons {s : Multiset α} {a : α} (ha : a ∉ s) : s ⊂ a ::ₘ s :=
  ⟨subset_cons _ _, fun h => ha <| h <| mem_cons_self _ _⟩

@[simp]
theorem cons_subset {a : α} {s t : Multiset α} : a ::ₘ s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp [← subset_iff, ← or_imp_distrib, ← forall_and_distrib]

theorem cons_subset_cons {a : α} {s t : Multiset α} : s ⊆ t → a ::ₘ s ⊆ a ::ₘ t :=
  (Quotientₓ.induction_on₂ s t) fun _ _ => cons_subset_consₓ _

theorem eq_zero_of_subset_zero {s : Multiset α} (h : s ⊆ 0) : s = 0 :=
  eq_zero_of_forall_not_mem h

theorem subset_zero {s : Multiset α} : s ⊆ 0 ↔ s = 0 :=
  ⟨eq_zero_of_subset_zero, fun xeq => xeq.symm ▸ Subset.refl 0⟩

theorem induction_on' {p : Multiset α → Prop} (S : Multiset α) (h₁ : p 0)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
  @Multiset.induction_on α (fun T => T ⊆ S → p T) S (fun _ => h₁)
    (fun a s hps hs =>
      let ⟨hS, sS⟩ := cons_subset.1 hs
      h₂ hS sS (hps sS))
    (Subset.refl S)

end Subset

section ToList

/-- Produces a list of the elements in the multiset using choice. -/
@[reducible]
noncomputable def toList {α : Type _} (s : Multiset α) :=
  Classical.some (Quotientₓ.exists_rep s)

@[simp]
theorem to_list_zero {α : Type _} : (Multiset.toList 0 : List α) = [] :=
  (Multiset.coe_eq_zero _).1 (Classical.some_spec (Quotientₓ.exists_rep Multiset.zero))

@[simp, norm_cast]
theorem coe_to_list {α : Type _} (s : Multiset α) : (s.toList : Multiset α) = s :=
  Classical.some_spec (Quotientₓ.exists_rep _)

@[simp]
theorem mem_to_list {α : Type _} (a : α) (s : Multiset α) : a ∈ s.toList ↔ a ∈ s := by
  rw [← Multiset.mem_coe, Multiset.coe_to_list]

end ToList

/-! ### Partial order on `multiset`s -/


/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def Le (s t : Multiset α) : Prop :=
  (Quotientₓ.liftOn₂ s t (· <+~ ·)) fun v₁ v₂ w₁ w₂ p₁ p₂ => propext (p₂.subperm_left.trans p₁.subperm_right)

instance : PartialOrderₓ (Multiset α) where
  le := Multiset.Le
  le_refl := by
    rintro ⟨l⟩ <;> exact subperm.refl _
  le_trans := by
    rintro ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩ <;> exact @subperm.trans _ _ _ _
  le_antisymm := by
    rintro ⟨l₁⟩ ⟨l₂⟩ h₁ h₂ <;> exact Quot.sound (subperm.antisymm h₁ h₂)

section

variable {s t : Multiset α} {a : α}

theorem subset_of_le : s ≤ t → s ⊆ t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => Subperm.subset

alias subset_of_le ← le.subset

theorem mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t :=
  mem_of_subset (subset_of_le h)

theorem not_mem_mono (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| @h _

@[simp]
theorem coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) ≤ l₂ ↔ l₁ <+~ l₂ :=
  Iff.rfl

@[elab_as_eliminator]
theorem le_induction_on {C : Multiset α → Multiset α → Prop} {s t : Multiset α} (h : s ≤ t)
    (H : ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
  Quotientₓ.induction_on₂ s t (fun l₁ l₂ ⟨l, p, s⟩ => (show ⟦l⟧ = ⟦l₁⟧ from Quot.sound p) ▸ H s) h

theorem zero_le (s : Multiset α) : 0 ≤ s :=
  (Quot.induction_on s) fun l => (nil_sublist l).Subperm

theorem le_zero : s ≤ 0 ↔ s = 0 :=
  ⟨fun h => le_antisymmₓ h (zero_le _), le_of_eqₓ⟩

theorem lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ s :=
  (Quot.induction_on s) fun l =>
    suffices l <+~ a :: l ∧ ¬l ~ a :: l by
      simpa [← lt_iff_le_and_ne]
    ⟨(sublist_cons _ _).Subperm, fun p => ne_of_ltₓ (lt_succ_selfₓ (length l)) p.length_eq⟩

theorem le_cons_self (s : Multiset α) (a : α) : s ≤ a ::ₘ s :=
  le_of_ltₓ <| lt_cons_self _ _

theorem cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => subperm_cons a

theorem cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t :=
  (cons_le_cons_iff a).2

theorem le_cons_of_not_mem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t := by
  refine' ⟨_, fun h => le_transₓ h <| le_cons_self _ _⟩
  suffices ∀ {t'} (_ : s ≤ t') (_ : a ∈ t'), a ::ₘ s ≤ t' by
    exact fun h => (cons_le_cons_iff a).1 (this h (mem_cons_self _ _))
  introv h
  revert m
  refine' le_induction_on h _
  introv s m₁ m₂
  rcases mem_split m₂ with ⟨r₁, r₂, rfl⟩
  exact perm_middle.subperm_left.2 ((subperm_cons _).2 <| ((sublist_or_mem_of_sublist s).resolve_right m₁).Subperm)

end

/-! ### Singleton -/


instance : HasSingleton α (Multiset α) :=
  ⟨fun a => a ::ₘ 0⟩

instance : IsLawfulSingleton α (Multiset α) :=
  ⟨fun a => rfl⟩

theorem singleton_eq_cons (a : α) : singleton a = a ::ₘ 0 :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Multiset α) ↔ b = a := by
  simp only [← singleton_eq_cons, ← mem_cons, ← iff_selfₓ, ← or_falseₓ, ← not_mem_zero]

theorem mem_singleton_self (a : α) : a ∈ ({a} : Multiset α) := by
  rw [singleton_eq_cons]
  exact mem_cons_self _ _

theorem singleton_inj {a b : α} : ({a} : Multiset α) = {b} ↔ a = b := by
  simp_rw [singleton_eq_cons]
  exact cons_inj_left _

@[simp]
theorem singleton_ne_zero (a : α) : ({a} : Multiset α) ≠ 0 :=
  ne_of_gtₓ (lt_cons_self _ _)

@[simp]
theorem singleton_le {a : α} {s : Multiset α} : {a} ≤ s ↔ a ∈ s :=
  ⟨fun h => mem_of_le h (mem_singleton_self _), fun h =>
    let ⟨t, e⟩ := exists_cons_of_mem h
    e.symm ▸ cons_le_cons _ (zero_le _)⟩

theorem pair_comm (x y : α) : ({x, y} : Multiset α) = {y, x} :=
  cons_swap x y 0

/-! ### Additive monoid -/


/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : Multiset α) : Multiset α :=
  (Quotientₓ.liftOn₂ s₁ s₂ fun l₁ l₂ => ((l₁ ++ l₂ : List α) : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.append p₂

instance : Add (Multiset α) :=
  ⟨Multiset.add⟩

@[simp]
theorem coe_add (s t : List α) : (s + t : Multiset α) = (s ++ t : List α) :=
  rfl

theorem singleton_add (a : α) (s : Multiset α) : {a} + s = a ::ₘ s :=
  rfl

private theorem add_le_add_iff_left' {s t u : Multiset α} : s + t ≤ s + u ↔ t ≤ u :=
  (Quotientₓ.induction_on₃ s t u) fun l₁ l₂ l₃ => subperm_append_left _

instance : CovariantClass (Multiset α) (Multiset α) (· + ·) (· ≤ ·) :=
  ⟨fun s t u => add_le_add_iff_left'.2⟩

instance : ContravariantClass (Multiset α) (Multiset α) (· + ·) (· ≤ ·) :=
  ⟨fun s t u => add_le_add_iff_left'.1⟩

instance : OrderedCancelAddCommMonoid (Multiset α) :=
  { @Multiset.partialOrder α with zero := 0, add := (· + ·),
    add_comm := fun s t => (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => Quot.sound perm_append_comm,
    add_assoc := fun s₁ s₂ s₃ =>
      (Quotientₓ.induction_on₃ s₁ s₂ s₃) fun l₁ l₂ l₃ => congr_arg coe <| append_assoc l₁ l₂ l₃,
    zero_add := fun s => (Quot.induction_on s) fun l => rfl,
    add_zero := fun s => (Quotientₓ.induction_on s) fun l => congr_arg coe <| append_nil l,
    add_left_cancel := fun a b c => add_left_cancel'', add_le_add_left := fun s₁ s₂ => add_le_add_left,
    le_of_add_le_add_left := fun s₁ s₂ s₃ => le_of_add_le_add_left }

theorem le_add_right (s t : Multiset α) : s ≤ s + t := by
  simpa using add_le_add_left (zero_le t) s

theorem le_add_left (s t : Multiset α) : s ≤ t + s := by
  simpa using add_le_add_right (zero_le t) s

theorem le_iff_exists_add {s t : Multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
  ⟨fun h =>
    (le_induction_on h) fun l₁ l₂ s =>
      let ⟨l, p⟩ := s.exists_perm_append
      ⟨l, Quot.sound p⟩,
    fun ⟨u, e⟩ => e.symm ▸ le_add_right _ _⟩

instance : OrderBot (Multiset α) where
  bot := 0
  bot_le := Multiset.zero_le

instance : CanonicallyOrderedAddMonoid (Multiset α) :=
  { Multiset.orderBot, Multiset.orderedCancelAddCommMonoid with le_self_add := le_add_right,
    exists_add_of_le := fun a b h =>
      (le_induction_on h) fun l₁ l₂ s =>
        let ⟨l, p⟩ := s.exists_perm_append
        ⟨l, Quot.sound p⟩ }

/-- This is a `rfl` and `simp` version of `bot_eq_zero`. -/
@[simp]
theorem bot_eq_zero : (⊥ : Multiset α) = 0 :=
  rfl

@[simp]
theorem cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a ::ₘ (s + t) := by
  rw [← singleton_add, ← singleton_add, add_assocₓ]

@[simp]
theorem add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a ::ₘ (s + t) := by
  rw [add_commₓ, cons_add, add_commₓ]

@[simp]
theorem mem_add {a : α} {s t : Multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => mem_appendₓ

theorem mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s := by
  induction' n with n ih
  · rw [zero_nsmul] at h
    exact absurd h (not_mem_zero _)
    
  · rw [succ_nsmul, mem_add] at h
    exact h.elim id ih
    

@[simp]
theorem mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s := by
  refine' ⟨mem_of_mem_nsmul, fun h => _⟩
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h0
  rw [succ_nsmul, mem_add]
  exact Or.inl h

theorem nsmul_cons {s : Multiset α} (n : ℕ) (a : α) : n • (a ::ₘ s) = n • {a} + n • s := by
  rw [← singleton_add, nsmul_add]

/-! ### Cardinality -/


/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : Multiset α →+ ℕ where
  toFun := fun s => (Quot.liftOn s length) fun l₁ l₂ => Perm.length_eq
  map_zero' := rfl
  map_add' := fun s t => Quotientₓ.induction_on₂ s t length_append

@[simp]
theorem coe_card (l : List α) : card (l : Multiset α) = length l :=
  rfl

@[simp]
theorem card_zero : @card α 0 = 0 :=
  rfl

theorem card_add (s t : Multiset α) : card (s + t) = card s + card t :=
  card.map_add s t

theorem card_nsmul (s : Multiset α) (n : ℕ) : (n • s).card = n * s.card := by
  rw [card.map_nsmul s n, Nat.nsmul_eq_mul]

@[simp]
theorem card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) = card s + 1 :=
  (Quot.induction_on s) fun l => rfl

@[simp]
theorem card_singleton (a : α) : card ({a} : Multiset α) = 1 := by
  simp only [← singleton_eq_cons, ← card_zero, ← eq_self_iff_true, ← zero_addₓ, ← card_cons]

theorem card_pair (a b : α) : ({a, b} : Multiset α).card = 2 := by
  rw [insert_eq_cons, card_cons, card_singleton]

theorem card_eq_one {s : Multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
  ⟨(Quot.induction_on s) fun l h => (List.length_eq_one.1 h).imp fun a => congr_arg coe, fun ⟨a, e⟩ => e.symm ▸ rfl⟩

theorem card_le_of_le {s t : Multiset α} (h : s ≤ t) : card s ≤ card t :=
  (le_induction_on h) fun l₁ l₂ => length_le_of_sublistₓ

@[mono]
theorem card_mono : Monotone (@card α) := fun a b => card_le_of_le

theorem eq_of_le_of_card_le {s t : Multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
  (le_induction_on h) fun l₁ l₂ s h₂ => congr_arg coe <| eq_of_sublist_of_length_le s h₂

theorem card_lt_of_lt {s t : Multiset α} (h : s < t) : card s < card t :=
  lt_of_not_geₓ fun h₂ => ne_of_ltₓ h <| eq_of_le_of_card_le (le_of_ltₓ h) h₂

theorem lt_iff_cons_le {s t : Multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
  ⟨(Quotientₓ.induction_on₂ s t) fun l₁ l₂ h => Subperm.exists_of_length_lt (le_of_ltₓ h) (card_lt_of_lt h),
    fun ⟨a, h⟩ => lt_of_lt_of_leₓ (lt_cons_self _ _) h⟩

@[simp]
theorem card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 0 :=
  ⟨fun h => (eq_of_le_of_card_le (zero_le _) (le_of_eqₓ h)).symm, fun e => by
    simp [← e]⟩

theorem card_pos {s : Multiset α} : 0 < card s ↔ s ≠ 0 :=
  pos_iff_ne_zero.trans <| not_congr card_eq_zero

theorem card_pos_iff_exists_mem {s : Multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
  (Quot.induction_on s) fun l => length_pos_iff_exists_memₓ

theorem card_eq_two {s : Multiset α} : s.card = 2 ↔ ∃ x y, s = {x, y} :=
  ⟨Quot.induction_on s fun l h => (List.length_eq_two.mp h).imp fun a => Exists.imp fun b => congr_arg coe,
    fun ⟨a, b, e⟩ => e.symm ▸ rfl⟩

theorem card_eq_three {s : Multiset α} : s.card = 3 ↔ ∃ x y z, s = {x, y, z} :=
  ⟨Quot.induction_on s fun l h =>
      (List.length_eq_three.mp h).imp fun a => Exists.imp fun b => Exists.imp fun c => congr_arg coe,
    fun ⟨a, b, c, e⟩ => e.symm ▸ rfl⟩

/-! ### Induction principles -/


/-- A strong induction principle for multisets:
If you construct a value for a particular multiset given values for all strictly smaller multisets,
you can construct a value for any multiset.
-/
@[elab_as_eliminator]
def strongInductionOnₓ {p : Multiset α → Sort _} : ∀ s : Multiset α, (∀ s, (∀, ∀ t < s, ∀, p t) → p s) → p s
  | s => fun ih =>
    (ih s) fun t h =>
      have : card t < card s := card_lt_of_lt h
      strong_induction_on t ih

theorem strong_induction_eq {p : Multiset α → Sort _} (s : Multiset α) (H) :
    @strongInductionOnₓ _ p s H = H s fun t h => @strongInductionOnₓ _ p t H := by
  rw [strong_induction_on]

@[elab_as_eliminator]
theorem case_strong_induction_on {p : Multiset α → Prop} (s : Multiset α) (h₀ : p 0)
    (h₁ : ∀ a s, (∀, ∀ t ≤ s, ∀, p t) → p (a ::ₘ s)) : p s :=
  (Multiset.strongInductionOnₓ s) fun s =>
    (Multiset.induction_on s fun _ => h₀) fun a s _ ih =>
      (h₁ _ _) fun t h => ih _ <| lt_of_le_of_ltₓ h <| lt_cons_self _ _

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strongDownwardInductionₓ {p : Multiset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    ∀ s : Multiset α, s.card ≤ n → p s
  | s =>
    H s fun t ht h =>
      have : n - card t < n - card s := (tsub_lt_tsub_iff_left_of_le ht).2 (card_lt_of_lt h)
      strong_downward_induction t ht

theorem strong_downward_induction_eq {p : Multiset α → Sort _} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) (s : Multiset α) :
    strongDownwardInductionₓ H s = H s fun t ht hst => strongDownwardInductionₓ H t ht := by
  rw [strong_downward_induction]

/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_eliminator]
def strongDownwardInductionOn {p : Multiset α → Sort _} {n : ℕ} :
    ∀ s : Multiset α,
      (∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) → s.card ≤ n → p s :=
  fun s H => strongDownwardInductionₓ H s

theorem strong_downward_induction_on_eq {p : Multiset α → Sort _} (s : Multiset α) {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun t ht h => t.strongDownwardInductionOn H ht := by
  dunfold strong_downward_induction_on
  rw [strong_downward_induction]

/-- Another way of expressing `strong_induction_on`: the `(<)` relation is well-founded. -/
theorem well_founded_lt : WellFounded ((· < ·) : Multiset α → Multiset α → Prop) :=
  Subrelation.wfₓ (fun _ _ => Multiset.card_lt_of_lt) (measure_wf Multiset.card)

/-! ### `multiset.repeat` -/


/-- `repeat a n` is the multiset containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : Multiset α :=
  repeatₓ a n

@[simp]
theorem repeat_zero (a : α) : repeat a 0 = 0 :=
  rfl

@[simp]
theorem repeat_succ (a : α) (n) : repeat a (n + 1) = a ::ₘ repeat a n := by
  simp [← repeat]

@[simp]
theorem repeat_one (a : α) : repeat a 1 = {a} := by
  simp only [← repeat_succ, ← singleton_eq_cons, ← eq_self_iff_true, ← repeat_zero, ← cons_inj_right]

@[simp]
theorem card_repeat : ∀ (a : α) (n), card (repeat a n) = n :=
  length_repeat

theorem mem_repeat {a b : α} {n : ℕ} : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a :=
  mem_repeat

theorem eq_of_mem_repeat {a b : α} {n} : b ∈ repeat a n → b = a :=
  eq_of_mem_repeat

theorem eq_repeat' {a : α} {s : Multiset α} : s = repeat a s.card ↔ ∀, ∀ b ∈ s, ∀, b = a :=
  (Quot.induction_on s) fun l => Iff.trans ⟨fun h => perm_repeat.1 <| Quotientₓ.exact h, congr_arg coe⟩ eq_repeat'

theorem eq_repeat_of_mem {a : α} {s : Multiset α} : (∀, ∀ b ∈ s, ∀, b = a) → s = repeat a s.card :=
  eq_repeat'.2

theorem eq_repeat {a : α} {n} {s : Multiset α} : s = repeat a n ↔ card s = n ∧ ∀, ∀ b ∈ s, ∀, b = a :=
  ⟨fun h => h.symm ▸ ⟨card_repeat _ _, fun b => eq_of_mem_repeat⟩, fun ⟨e, al⟩ => e ▸ eq_repeat_of_mem al⟩

theorem repeat_left_injective {n : ℕ} (hn : n ≠ 0) : Function.Injective fun a : α => repeat a n := fun a b h =>
  (eq_repeat.1 h).2 _ <| mem_repeat.2 ⟨hn, rfl⟩

@[simp]
theorem repeat_left_inj {a b : α} {n : ℕ} (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
  (repeat_left_injective h).eq_iff

theorem repeat_injective (a : α) : Function.Injective (repeat a) := fun m n h => by
  rw [← (eq_repeat.1 h).1, card_repeat]

theorem repeat_subset_singleton : ∀ (a : α) (n), repeat a n ⊆ {a} :=
  repeat_subset_singleton

theorem repeat_le_coe {a : α} {n} {l : List α} : repeat a n ≤ l ↔ List.repeat a n <+ l :=
  ⟨fun ⟨l', p, s⟩ => perm_repeat.1 p ▸ s, Sublist.subperm⟩

theorem nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = repeat a n := by
  refine' eq_repeat.mpr ⟨_, fun b hb => mem_singleton.mp (mem_of_mem_nsmul hb)⟩
  rw [card_nsmul, card_singleton, mul_oneₓ]

theorem nsmul_repeat {a : α} (n m : ℕ) : n • repeat a m = repeat a (n * m) := by
  rw [eq_repeat]
  constructor
  · rw [card_nsmul, card_repeat]
    
  · exact fun b hb => eq_of_mem_repeat (mem_of_mem_nsmul hb)
    

/-! ### Erasing one copy of an element -/


section Erase

variable [DecidableEq α] {s t : Multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the
  multiplicity of `a`. -/
def erase (s : Multiset α) (a : α) : Multiset α :=
  Quot.liftOn s (fun l => (l.erase a : Multiset α)) fun l₁ l₂ p => Quot.sound (p.erase a)

@[simp]
theorem coe_erase (l : List α) (a : α) : erase (l : Multiset α) a = l.erase a :=
  rfl

@[simp]
theorem erase_zero (a : α) : (0 : Multiset α).erase a = 0 :=
  rfl

@[simp]
theorem erase_cons_head (a : α) (s : Multiset α) : (a ::ₘ s).erase a = s :=
  (Quot.induction_on s) fun l => congr_arg coe <| erase_cons_headₓ a l

@[simp]
theorem erase_cons_tail {a b : α} (s : Multiset α) (h : b ≠ a) : (b ::ₘ s).erase a = b ::ₘ s.erase a :=
  (Quot.induction_on s) fun l => congr_arg coe <| erase_cons_tailₓ l h

@[simp]
theorem erase_singleton (a : α) : ({a} : Multiset α).erase a = 0 :=
  erase_cons_head a 0

@[simp]
theorem erase_of_not_mem {a : α} {s : Multiset α} : a ∉ s → s.erase a = s :=
  (Quot.induction_on s) fun l h => congr_arg coe <| erase_of_not_memₓ h

@[simp]
theorem cons_erase {s : Multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
  (Quot.induction_on s) fun l h => Quot.sound (perm_cons_erase h).symm

theorem le_cons_erase (s : Multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
  if h : a ∈ s then le_of_eqₓ (cons_erase h).symm
  else by
    rw [erase_of_not_mem h] <;> apply le_cons_self

theorem add_singleton_eq_iff {s t : Multiset α} {a : α} : s + {a} = t ↔ a ∈ t ∧ s = t.erase a := by
  rw [add_commₓ, singleton_add]
  constructor
  · rintro rfl
    exact ⟨s.mem_cons_self a, (s.erase_cons_head a).symm⟩
    
  · rintro ⟨h, rfl⟩
    exact cons_erase h
    

theorem erase_add_left_pos {a : α} {s : Multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ h => congr_arg coe <| erase_append_leftₓ l₂ h

theorem erase_add_right_pos {a : α} (s) {t : Multiset α} (h : a ∈ t) : (s + t).erase a = s + t.erase a := by
  rw [add_commₓ, erase_add_left_pos s h, add_commₓ]

theorem erase_add_right_neg {a : α} {s : Multiset α} (t) : a ∉ s → (s + t).erase a = s + t.erase a :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ h => congr_arg coe <| erase_append_rightₓ l₂ h

theorem erase_add_left_neg {a : α} (s) {t : Multiset α} (h : a ∉ t) : (s + t).erase a = s.erase a + t := by
  rw [add_commₓ, erase_add_right_neg s h, add_commₓ]

theorem erase_le (a : α) (s : Multiset α) : s.erase a ≤ s :=
  (Quot.induction_on s) fun l => (erase_sublist a l).Subperm

@[simp]
theorem erase_lt {a : α} {s : Multiset α} : s.erase a < s ↔ a ∈ s :=
  ⟨fun h => not_imp_comm.1 erase_of_not_mem (ne_of_ltₓ h), fun h => by
    simpa [← h] using lt_cons_self (s.erase a) a⟩

theorem erase_subset (a : α) (s : Multiset α) : s.erase a ⊆ s :=
  subset_of_le (erase_le a s)

theorem mem_erase_of_ne {a b : α} {s : Multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
  (Quot.induction_on s) fun l => List.mem_erase_of_neₓ ab

theorem mem_of_mem_erase {a b : α} {s : Multiset α} : a ∈ s.erase b → a ∈ s :=
  mem_of_subset (erase_subset _ _)

theorem erase_comm (s : Multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
  (Quot.induction_on s) fun l => congr_arg coe <| l.erase_comm a b

theorem erase_le_erase {s t : Multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
  (le_induction_on h) fun l₁ l₂ h => (h.erase _).Subperm

theorem erase_le_iff_le_cons {s t : Multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
  ⟨fun h => le_transₓ (le_cons_erase _ _) (cons_le_cons _ h), fun h =>
    if m : a ∈ s then by
      rw [← cons_erase m] at h <;> exact (cons_le_cons_iff _).1 h
    else le_transₓ (erase_le _ _) ((le_cons_of_not_mem m).1 h)⟩

@[simp]
theorem card_erase_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) = pred (card s) :=
  (Quot.induction_on s) fun l => length_erase_of_memₓ

@[simp]
theorem card_erase_add_one {a : α} {s : Multiset α} : a ∈ s → (s.erase a).card + 1 = s.card :=
  (Quot.induction_on s) fun l => length_erase_add_one

theorem card_erase_lt_of_mem {a : α} {s : Multiset α} : a ∈ s → card (s.erase a) < card s := fun h =>
  card_lt_of_lt (erase_lt.mpr h)

theorem card_erase_le {a : α} {s : Multiset α} : card (s.erase a) ≤ card s :=
  card_le_of_le (erase_le a s)

theorem card_erase_eq_ite {a : α} {s : Multiset α} : card (s.erase a) = if a ∈ s then pred (card s) else card s := by
  by_cases' h : a ∈ s
  · rwa [card_erase_of_mem h, if_pos]
    
  · rwa [erase_of_not_mem h, if_neg]
    

end Erase

@[simp]
theorem coe_reverse (l : List α) : (reverse l : Multiset α) = l :=
  Quot.sound <| reverse_perm _

/-! ### `multiset.map` -/


/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun l₁ l₂ p => Quot.sound (p.map f)

@[congr]
theorem map_congr {f g : α → β} {s t : Multiset α} : s = t → (∀, ∀ x ∈ t, ∀, f x = g x) → map f s = map g t := by
  rintro rfl h
  induction s using Quot.induction_on
  exact congr_arg coe (map_congr h)

theorem map_hcongr {β' : Type _} {m : Multiset α} {f : α → β} {f' : α → β'} (h : β = β')
    (hf : ∀, ∀ a ∈ m, ∀, HEq (f a) (f' a)) : HEq (map f m) (map f' m) := by
  subst h
  simp at hf
  simp [← map_congr rfl hf]

theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : Multiset α} :
    (∀, ∀ y ∈ s.map f, ∀, p y) ↔ ∀, ∀ x ∈ s, ∀, p (f x) :=
  (Quotientₓ.induction_on' s) fun L => List.forall_mem_map_iffₓ

@[simp]
theorem coe_map (f : α → β) (l : List α) : map f ↑l = l.map f :=
  rfl

@[simp]
theorem map_zero (f : α → β) : map f 0 = 0 :=
  rfl

@[simp]
theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  (Quot.induction_on s) fun l => rfl

theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f := by
  ext
  simp

@[simp]
theorem map_singleton (f : α → β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl

theorem map_repeat (f : α → β) (a : α) (k : ℕ) : (repeat a k).map f = repeat (f a) k := by
  induction k
  simp
  simpa

@[simp]
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => congr_arg coe <| map_append _ _ _

/-- If each element of `s : multiset α` can be lifted to `β`, then `s` can be lifted to
`multiset β`. -/
instance [CanLift α β] : CanLift (Multiset α) (Multiset β) where
  cond := fun s => ∀, ∀ x ∈ s, ∀, CanLift.Cond β x
  coe := map CanLift.coe
  prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, coe_map _ _⟩

/-- `multiset.map` as an `add_monoid_hom`. -/
def mapAddMonoidHom (f : α → β) : Multiset α →+ Multiset β where
  toFun := map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
theorem coe_map_add_monoid_hom (f : α → β) : (mapAddMonoidHom f : Multiset α → Multiset β) = map f :=
  rfl

theorem map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • map f s :=
  (mapAddMonoidHom f).map_nsmul _ _

@[simp]
theorem mem_map {f : α → β} {b : β} {s : Multiset α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
  (Quot.induction_on s) fun l => mem_mapₓ

@[simp]
theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  (Quot.induction_on s) fun l => length_mapₓ _ _

@[simp]
theorem map_eq_zero {s : Multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero, Multiset.card_map, Multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : Multiset α} (h : a ∈ s) : f a ∈ map f s :=
  mem_map.2 ⟨_, h, rfl⟩

theorem map_eq_singleton {f : α → β} {s : Multiset α} {b : β} : map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, s = {a} := by
      rw [← card_eq_one, ← card_map, h, card_singleton]
    refine' ⟨a, ha, _⟩
    rw [← mem_singleton, ← h, ha, map_singleton, mem_singleton]
    
  · rintro ⟨a, rfl, rfl⟩
    simp
    

theorem map_eq_cons [DecidableEq α] (f : α → β) (s : Multiset α) (t : Multiset β) (b : β) :
    (∃ a ∈ s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t := by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons, Multiset.cons_erase ha]
    
  · intro h
    have : b ∈ s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons, cons_inj_right] at h
    refine' ⟨a, mem_cons_self _ _, rfl, _⟩
    rw [Multiset.erase_cons_head, h]
    

theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {s : Multiset α} : f a ∈ map f s ↔ a ∈ s :=
  (Quot.induction_on s) fun l => mem_map_of_injectiveₓ H

@[simp]
theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| List.map_mapₓ _ _ _

theorem map_id (s : Multiset α) : map id s = s :=
  (Quot.induction_on s) fun l => congr_arg coe <| map_id _

@[simp]
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s

@[simp]
theorem map_const (s : Multiset α) (b : β) : map (Function.const α b) s = repeat b s.card :=
  (Quot.induction_on s) fun l => congr_arg coe <| map_const _ _

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) : b₁ = b₂ :=
  eq_of_mem_repeat <| by
    rwa [map_const] at h

@[simp]
theorem map_le_map {f : α → β} {s t : Multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  (le_induction_on h) fun l₁ l₂ h => (h.map f).Subperm

@[simp]
theorem map_lt_map {f : α → β} {s t : Multiset α} (h : s < t) : s.map f < t.map f := by
  refine' (map_le_map h.le).lt_of_not_le fun H => h.ne <| eq_of_le_of_card_le h.le _
  rw [← s.card_map f, ← t.card_map f]
  exact card_le_of_le H

theorem map_mono (f : α → β) : Monotone (map f) := fun _ _ => map_le_map

theorem map_strict_mono (f : α → β) : StrictMono (map f) := fun _ _ => map_lt_map

@[simp]
theorem map_subset_map {f : α → β} {s t : Multiset α} (H : s ⊆ t) : map f s ⊆ map f t := fun b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩

theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α) (s : Multiset α) :
    (s.erase x).map f = (s.map f).erase (f x) := by
  induction' s using Multiset.induction_on with y s ih
  · simp
    
  by_cases' hxy : y = x
  · cases hxy
    simp
    
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]
    

theorem map_surjective_of_surjective {f : α → β} (hf : Function.Surjective f) : Function.Surjective (map f) := by
  intro s
  induction' s using Multiset.induction_on with x s ih
  · exact ⟨0, map_zero _⟩
    
  · obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩
    

/-! ### `multiset.fold` -/


/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) (H : RightCommutative f) (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => foldlₓ f b l) fun l₁ l₂ p => p.foldl_eq H b

@[simp]
theorem foldl_zero (f : β → α → β) (H b) : foldl f H b 0 = b :=
  rfl

@[simp]
theorem foldl_cons (f : β → α → β) (H b a s) : foldl f H b (a ::ₘ s) = foldl f H (f b a) s :=
  (Quot.induction_on s) fun l => rfl

@[simp]
theorem foldl_add (f : β → α → β) (H b s t) : foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => foldl_append _ _ _ _

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : LeftCommutative f) (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => foldr f b l) fun l₁ l₂ p => p.foldr_eq H b

@[simp]
theorem foldr_zero (f : α → β → β) (H b) : foldr f H b 0 = b :=
  rfl

@[simp]
theorem foldr_cons (f : α → β → β) (H b a s) : foldr f H b (a ::ₘ s) = f a (foldr f H b s) :=
  (Quot.induction_on s) fun l => rfl

@[simp]
theorem foldr_singleton (f : α → β → β) (H b a) : foldr f H b ({a} : Multiset α) = f a b :=
  rfl

@[simp]
theorem foldr_add (f : α → β → β) (H b s t) : foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => foldr_append _ _ _ _

@[simp]
theorem coe_foldr (f : α → β → β) (H : LeftCommutative f) (b : β) (l : List α) : foldr f H b l = l.foldr f b :=
  rfl

@[simp]
theorem coe_foldl (f : β → α → β) (H : RightCommutative f) (b : β) (l : List α) : foldl f H b l = l.foldl f b :=
  rfl

theorem coe_foldr_swap (f : α → β → β) (H : LeftCommutative f) (b : β) (l : List α) :
    foldr f H b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f H b) (coe_reverse l)).symm.trans <| foldr_reverse _ _ _

theorem foldr_swap (f : α → β → β) (H : LeftCommutative f) (b : β) (s : Multiset α) :
    foldr f H b s = foldl (fun x y => f y x) (fun x y z => (H _ _ _).symm) b s :=
  (Quot.induction_on s) fun l => coe_foldr_swap _ _ _ _

theorem foldl_swap (f : β → α → β) (H : RightCommutative f) (b : β) (s : Multiset α) :
    foldl f H b s = foldr (fun x y => f y x) (fun x y z => (H _ _ _).symm) b s :=
  (foldr_swap _ _ _ _).symm

theorem foldr_induction' (f : α → β → β) (H : LeftCommutative f) (x : β) (q : α → Prop) (p : β → Prop) (s : Multiset α)
    (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x) (q_s : ∀, ∀ a ∈ s, ∀, q a) : p (foldr f H x s) := by
  revert s
  refine'
    Multiset.induction
      (by
        simp [← px])
      _
  intro a s hs hsa
  rw [foldr_cons]
  have hps : ∀ x : α, x ∈ s → q x := fun x hxs => hsa x (mem_cons_of_mem hxs)
  exact hpqf a (foldr f H x s) (hsa a (mem_cons_self a s)) (hs hps)

theorem foldr_induction (f : α → α → α) (H : LeftCommutative f) (x : α) (p : α → Prop) (s : Multiset α)
    (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀, ∀ a ∈ s, ∀, p a) : p (foldr f H x s) :=
  foldr_induction' f H x p p s p_f px p_s

theorem foldl_induction' (f : β → α → β) (H : RightCommutative f) (x : β) (q : α → Prop) (p : β → Prop) (s : Multiset α)
    (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x) (q_s : ∀, ∀ a ∈ s, ∀, q a) : p (foldl f H x s) := by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) (fun x y z => (H _ _ _).symm) x q p s hpqf px q_s

theorem foldl_induction (f : α → α → α) (H : RightCommutative f) (x : α) (p : α → Prop) (s : Multiset α)
    (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀, ∀ a ∈ s, ∀, p a) : p (foldl f H x s) :=
  foldl_induction' f H x p p s p_f px p_s

/-! ### Map for partial functions -/


/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
def pmap {p : α → Prop} (f : ∀ a, p a → β) (s : Multiset α) : (∀, ∀ a ∈ s, ∀, p a) → Multiset β :=
  (Quot.recOn s fun l H => ↑(pmap f l H)) fun l₁ l₂ (pp : l₁ ~ l₂) =>
    funext fun H₂ : ∀, ∀ a ∈ l₂, ∀, p a =>
      have H₁ : ∀, ∀ a ∈ l₁, ∀, p a := fun a h => H₂ a (pp.Subset h)
      have :
        ∀ {s₂ e H},
          @Eq.ndrec (Multiset α) l₁ (fun s => (∀, ∀ a ∈ s, ∀, p a) → Multiset β) (fun _ => ↑(pmap f l₁ H₁)) s₂ e H =
            ↑(pmap f l₁ H₁) :=
        by
        intro s₂ e _ <;> subst e
      this.trans <| Quot.sound <| pp.pmap f

@[simp]
theorem coe_pmap {p : α → Prop} (f : ∀ a, p a → β) (l : List α) (H : ∀, ∀ a ∈ l, ∀, p a) : pmap f l H = l.pmap f H :=
  rfl

@[simp]
theorem pmap_zero {p : α → Prop} (f : ∀ a, p a → β) (h : ∀, ∀ a ∈ (0 : Multiset α), ∀, p a) : pmap f 0 h = 0 :=
  rfl

@[simp]
theorem pmap_cons {p : α → Prop} (f : ∀ a, p a → β) (a : α) (m : Multiset α) :
    ∀ h : ∀, ∀ b ∈ a ::ₘ m, ∀, p b,
      pmap f (a ::ₘ m) h = f a (h a (mem_cons_self a m)) ::ₘ pmap f m fun a ha => h a <| mem_cons_of_mem ha :=
  (Quotientₓ.induction_on m) fun l h => rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : Multiset α) : Multiset { x // x ∈ s } :=
  pmap Subtype.mk s fun a => id

@[simp]
theorem coe_attach (l : List α) : @Eq (Multiset { x // x ∈ l }) (@attach α l) l.attach :=
  rfl

theorem sizeof_lt_sizeof_of_mem [SizeOf α] {x : α} {s : Multiset α} (hx : x ∈ s) : sizeof x < sizeof s := by
  induction' s with l a b
  exact List.sizeof_lt_sizeof_of_mem hx
  rfl

theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : Multiset α) : ∀ H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
  (Quot.induction_on s) fun l H => congr_arg coe <| pmap_eq_map p f l H

theorem pmap_congr {p q : α → Prop} {f : ∀ a, p a → β} {g : ∀ a, q a → β} (s : Multiset α) {H₁ H₂}
    (h : ∀ a h₁ h₂, f a h₁ = g a h₂) : pmap f s H₁ = pmap g s H₂ :=
  Quot.induction_on s (fun l H₁ H₂ => congr_arg coe <| pmap_congr l h) H₁ H₂

theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (s) :
    ∀ H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
  (Quot.induction_on s) fun l H => congr_arg coe <| map_pmap g f l H

theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (s) :
    ∀ H, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2) :=
  (Quot.induction_on s) fun l H => congr_arg coe <| pmap_eq_map_attach f l H

theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  (Quot.induction_on s) fun l => congr_arg coe <| attach_map_val l

@[simp]
theorem mem_attach (s : Multiset α) : ∀ x, x ∈ s.attach :=
  (Quot.induction_on s) fun l => mem_attach _

@[simp]
theorem mem_pmap {p : α → Prop} {f : ∀ a, p a → β} {s H b} : b ∈ pmap f s H ↔ ∃ (a : _)(h : a ∈ s), f a (H a h) = b :=
  Quot.induction_on s (fun l H => mem_pmap) H

@[simp]
theorem card_pmap {p : α → Prop} (f : ∀ a, p a → β) (s H) : card (pmap f s H) = card s :=
  Quot.induction_on s (fun l H => length_pmap) H

@[simp]
theorem card_attach {m : Multiset α} : card (attach m) = card m :=
  card_pmap _ _ _

@[simp]
theorem attach_zero : (0 : Multiset α).attach = 0 :=
  rfl

theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach = ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  (Quotientₓ.induction_on m) fun l =>
    congr_arg coe <|
      congr_arg (List.cons _) <| by
        rw [List.map_pmap] <;> exact List.pmap_congr _ fun a' h₁ h₂ => Subtype.eq rfl

section DecidablePiExists

variable {m : Multiset α}

/-- If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`. -/
protected def decidableForallMultiset {p : α → Prop} [hp : ∀ a, Decidable (p a)] : Decidable (∀, ∀ a ∈ m, ∀, p a) :=
  Quotientₓ.recOnSubsingleton m fun l =>
    decidableOfIff (∀, ∀ a ∈ l, ∀, p a) <| by
      simp

instance decidableDforallMultiset {p : ∀, ∀ a ∈ m, ∀, Prop} [hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∀ (a) (h : a ∈ m), p a h) :=
  decidableOfDecidableOfIff (@Multiset.decidableForallMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)
    (Iff.intro (fun h a ha => h ⟨a, ha⟩ (mem_attach _ _)) fun h ⟨a, ha⟩ _ => h _ _)

/-- decidable equality for functions whose domain is bounded by multisets -/
instance decidableEqPiMultiset {β : α → Type _} [h : ∀ a, DecidableEq (β a)] : DecidableEq (∀, ∀ a ∈ m, ∀, β a) :=
  fun f g =>
  decidableOfIff (∀ (a) (h : a ∈ m), f a h = g a h)
    (by
      simp [← Function.funext_iffₓ])

/-- If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`. -/
protected def decidableExistsMultiset {p : α → Prop} [DecidablePred p] : Decidable (∃ x ∈ m, p x) :=
  Quotientₓ.recOnSubsingleton m fun l =>
    decidableOfIff (∃ a ∈ l, p a) <| by
      simp

instance decidableDexistsMultiset {p : ∀, ∀ a ∈ m, ∀, Prop} [hp : ∀ (a) (h : a ∈ m), Decidable (p a h)] :
    Decidable (∃ (a : _)(h : a ∈ m), p a h) :=
  decidableOfDecidableOfIff (@Multiset.decidableExistsMultiset { a // a ∈ m } m.attach (fun a => p a.1 a.2) _)
    (Iff.intro (fun ⟨⟨a, ha₁⟩, _, ha₂⟩ => ⟨a, ha₁, ha₂⟩) fun ⟨a, ha₁, ha₂⟩ => ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩)

end DecidablePiExists

/-! ### Subtraction -/


section

variable [DecidableEq α] {s t u : Multiset α} {a b : α}

/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`
  (note that it is truncated subtraction, so it is `0` if `count a t ≥ count a s`). -/
protected def sub (s t : Multiset α) : Multiset α :=
  (Quotientₓ.liftOn₂ s t fun l₁ l₂ => (l₁.diff l₂ : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ => Quot.sound <| p₁.diff p₂

instance : Sub (Multiset α) :=
  ⟨Multiset.sub⟩

@[simp]
theorem coe_sub (s t : List α) : (s - t : Multiset α) = (s.diff t : List α) :=
  rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_zero (s : Multiset α) : s - 0 = s :=
  (Quot.induction_on s) fun l => rfl

@[simp]
theorem sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s.erase a - t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => congr_arg coe <| diff_cons _ _ _

/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t := by
  revert s <;>
    exact
      Multiset.induction_on t
        (by
          simp [← Multiset.sub_zero])
        fun a t IH s => by
        simp [← IH, ← erase_le_iff_le_cons]

instance : HasOrderedSub (Multiset α) :=
  ⟨fun n m k => Multiset.sub_le_iff_le_add⟩

theorem sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase erase_comm s t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ =>
    show ↑(l₁.diff l₂) = foldl erase erase_comm ↑l₁ ↑l₂ by
      rw [diff_eq_foldl l₁ l₂]
      symm
      exact foldl_hom _ _ _ _ _ fun x y => rfl

@[simp]
theorem card_sub {s t : Multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
  (tsub_eq_of_eq_add_rev <| by
      rw [add_commₓ, ← card_add, tsub_add_cancel_of_le h]).symm

/-! ### Union -/


/-- `s ∪ t` is the lattice join operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∪ t` is the maximum
  of the multiplicities in `s` and `t`. -/
def union (s t : Multiset α) : Multiset α :=
  s - t + t

instance : HasUnion (Multiset α) :=
  ⟨union⟩

theorem union_def (s t : Multiset α) : s ∪ t = s - t + t :=
  rfl

theorem le_union_left (s t : Multiset α) : s ≤ s ∪ t :=
  le_tsub_add

theorem le_union_right (s t : Multiset α) : t ≤ s ∪ t :=
  le_add_left _ _

theorem eq_union_left : t ≤ s → s ∪ t = s :=
  tsub_add_cancel_of_le

theorem union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
  add_le_add_right (tsub_le_tsub_right h _) u

theorem union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u := by
  rw [← eq_union_left h₂] <;> exact union_le_union_right h₁ t

@[simp]
theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le tsub_le_self),
    Or.ndrec (mem_of_le <| le_union_left _ _) (mem_of_le <| le_union_right _ _)⟩

@[simp]
theorem map_union [DecidableEq β] {f : α → β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s ∪ t) = map f s ∪ map f t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ =>
    congr_arg coe
      (by
        rw [List.map_append f, List.map_diff finj])

/-! ### Intersection -/


/-- `s ∩ t` is the lattice meet operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∩ t` is the minimum
  of the multiplicities in `s` and `t`. -/
def inter (s t : Multiset α) : Multiset α :=
  (Quotientₓ.liftOn₂ s t fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun v₁ v₂ w₁ w₂ p₁ p₂ =>
    Quot.sound <| p₁.bagInter p₂

instance : HasInter (Multiset α) :=
  ⟨inter⟩

@[simp]
theorem inter_zero (s : Multiset α) : s ∩ 0 = 0 :=
  (Quot.induction_on s) fun l => congr_arg coe l.bag_inter_nil

@[simp]
theorem zero_inter (s : Multiset α) : 0 ∩ s = 0 :=
  (Quot.induction_on s) fun l => congr_arg coe l.nil_bag_inter

@[simp]
theorem cons_inter_of_pos {a} (s : Multiset α) {t} : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ h => congr_arg coe <| cons_bag_inter_of_pos _ h

@[simp]
theorem cons_inter_of_neg {a} (s : Multiset α) {t} : a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ h => congr_arg coe <| cons_bag_inter_of_neg _ h

theorem inter_le_left (s t : Multiset α) : s ∩ t ≤ s :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => (bag_inter_sublist_left _ _).Subperm

theorem inter_le_right (s : Multiset α) : ∀ t, s ∩ t ≤ t :=
  (Multiset.induction_on s fun t => (zero_inter t).symm ▸ zero_le _) fun a s IH t =>
    if h : a ∈ t then by
      simpa [← h] using cons_le_cons a (IH (t.erase a))
    else by
      simp [← h, ← IH]

theorem le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u := by
  revert s u
  refine' Multiset.induction_on t _ fun a t IH => _ <;> intros
  · simp [← h₁]
    
  by_cases' a ∈ u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
    
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_not_mem <| mt (mem_of_le h₂) h).1 h₁) h₂
    

@[simp]
theorem mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  ⟨fun h => ⟨mem_of_le (inter_le_left _ _) h, mem_of_le (inter_le_right _ _) h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁, cons_inter_of_pos _ h₂] <;> apply mem_cons_self⟩

instance : Lattice (Multiset α) :=
  { @Multiset.partialOrder α with sup := (· ∪ ·), sup_le := @union_le _ _, le_sup_left := le_union_left,
    le_sup_right := le_union_right, inf := (· ∩ ·), le_inf := @le_inter _ _, inf_le_left := inter_le_left,
    inf_le_right := inter_le_right }

@[simp]
theorem sup_eq_union (s t : Multiset α) : s⊔t = s ∪ t :=
  rfl

@[simp]
theorem inf_eq_inter (s t : Multiset α) : s⊓t = s ∩ t :=
  rfl

@[simp]
theorem le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u :=
  le_inf_iff

@[simp]
theorem union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u :=
  sup_le_iff

theorem union_comm (s t : Multiset α) : s ∪ t = t ∪ s :=
  sup_comm

theorem inter_comm (s t : Multiset α) : s ∩ t = t ∩ s :=
  inf_comm

theorem eq_union_right (h : s ≤ t) : s ∪ t = t := by
  rw [union_comm, eq_union_left h]

theorem union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t :=
  sup_le_sup_left h _

theorem union_le_add (s t : Multiset α) : s ∪ t ≤ s + t :=
  union_le (le_add_right _ _) (le_add_left _ _)

theorem union_add_distrib (s t u : Multiset α) : s ∪ t + u = s + u ∪ (t + u) := by
  simpa [← (· ∪ ·), ← union, ← eq_comm, ← add_assocₓ] using
    show s + u - (t + u) = s - t by
      rw [add_commₓ t, tsub_add_eq_tsub_tsub, add_tsub_cancel_right]

theorem add_union_distrib (s t u : Multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := by
  rw [add_commₓ, union_add_distrib, add_commₓ s, add_commₓ s]

theorem cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t

theorem inter_add_distrib (s t u : Multiset α) : s ∩ t + u = (s + u) ∩ (t + u) := by
  by_contra h
  cases'
    lt_iff_cons_le.1
      (lt_of_le_of_neₓ (le_inter (add_le_add_right (inter_le_left s t) u) (add_le_add_right (inter_le_right s t) u))
        h) with
    a hl
  rw [← cons_add] at hl
  exact
    not_le_of_lt (lt_cons_self (s ∩ t) a)
      (le_inter (le_of_add_le_add_right (le_transₓ hl (inter_le_left _ _)))
        (le_of_add_le_add_right (le_transₓ hl (inter_le_right _ _))))

theorem add_inter_distrib (s t u : Multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := by
  rw [add_commₓ, inter_add_distrib, add_commₓ s, add_commₓ s]

theorem cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := by
  simp

theorem union_add_inter (s t : Multiset α) : s ∪ t + s ∩ t = s + t := by
  apply le_antisymmₓ
  · rw [union_add_distrib]
    refine' union_le (add_le_add_left (inter_le_right _ _) _) _
    rw [add_commₓ]
    exact add_le_add_right (inter_le_left _ _) _
    
  · rw [add_commₓ, add_inter_distrib]
    refine' le_inter (add_le_add_right (le_union_right _ _) _) _
    rw [add_commₓ]
    exact add_le_add_right (le_union_left _ _) _
    

theorem sub_add_inter (s t : Multiset α) : s - t + s ∩ t = s := by
  rw [inter_comm]
  revert s
  refine'
    Multiset.induction_on t
      (by
        simp )
      fun a t IH s => _
  by_cases' a ∈ s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
    
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_not_mem h, IH]
    

theorem sub_inter (s t : Multiset α) : s - s ∩ t = s - t :=
  add_right_cancelₓ <| by
    rw [sub_add_inter s t, tsub_add_cancel_of_le (inter_le_left s t)]

end

/-! ### `multiset.filter` -/


section

variable (p : α → Prop) [DecidablePred p]

/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (filterₓ p l : Multiset α)) fun l₁ l₂ h => Quot.sound <| h.filter p

@[simp]
theorem coe_filter (l : List α) : filter p ↑l = l.filter p :=
  rfl

@[simp]
theorem filter_zero : filter p 0 = 0 :=
  rfl

theorem filter_congr {p q : α → Prop} [DecidablePred p] [DecidablePred q] {s : Multiset α} :
    (∀, ∀ x ∈ s, ∀, p x ↔ q x) → filter p s = filter q s :=
  (Quot.induction_on s) fun l h => congr_arg coe <| filter_congr' h

@[simp]
theorem filter_add (s t : Multiset α) : filter p (s + t) = filter p s + filter p t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => congr_arg coe <| filter_append _ _

@[simp]
theorem filter_le (s : Multiset α) : filter p s ≤ s :=
  (Quot.induction_on s) fun l => (filter_sublist _).Subperm

@[simp]
theorem filter_subset (s : Multiset α) : filter p s ⊆ s :=
  subset_of_le <| filter_le _ _

theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
  (le_induction_on h) fun l₁ l₂ h => (h.filter p).Subperm

theorem monotone_filter_left : Monotone (filter p) := fun s t => filter_le_filter p

theorem monotone_filter_right (s : Multiset α) ⦃p q : α → Prop⦄ [DecidablePred p] [DecidablePred q] (h : p ≤ q) :
    s.filter p ≤ s.filter q :=
  Quotientₓ.induction_on s fun l => (l.monotone_filter_right h).Subperm

variable {p}

@[simp]
theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
  (Quot.induction_on s) fun l h => congr_arg coe <| filter_cons_of_pos l h

@[simp]
theorem filter_cons_of_neg {a : α} (s) : ¬p a → filter p (a ::ₘ s) = filter p s :=
  (Quot.induction_on s) fun l h => @congr_arg _ _ _ _ coe <| filter_cons_of_neg l h

@[simp]
theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
  (Quot.induction_on s) fun l => mem_filterₓ

theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
  (mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
  (mem_filter.1 h).1

theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨m, h⟩

theorem filter_eq_self {s} : filter p s = s ↔ ∀, ∀ a ∈ s, ∀, p a :=
  (Quot.induction_on s) fun l =>
    Iff.trans ⟨fun h => eq_of_sublist_of_length_eq (filter_sublist _) (@congr_arg _ _ _ _ card h), congr_arg coe⟩
      filter_eq_self

theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀, ∀ a ∈ s, ∀, ¬p a :=
  (Quot.induction_on s) fun l =>
    Iff.trans ⟨fun h => eq_nil_of_length_eq_zero (@congr_arg _ _ _ _ card h), congr_arg coe⟩ filter_eq_nil

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀, ∀ a ∈ s, ∀, p a :=
  ⟨fun h => ⟨le_transₓ h (filter_le _ _), fun a m => of_mem_filter (mem_of_le h m)⟩, fun ⟨h, al⟩ =>
    filter_eq_self.2 al ▸ filter_le_filter p h⟩

theorem filter_cons {a : α} (s : Multiset α) : filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s := by
  split_ifs with h
  · rw [filter_cons_of_pos _ h, singleton_add]
    
  · rw [filter_cons_of_neg _ h, zero_addₓ]
    

theorem filter_singleton {a : α} (p : α → Prop) [DecidablePred p] : filter p {a} = if p a then {a} else ∅ := by
  simp only [← singleton, ← filter_cons, ← filter_zero, ← add_zeroₓ, ← empty_eq_zero]

theorem filter_nsmul (s : Multiset α) (n : ℕ) : filter p (n • s) = n • filter p s := by
  refine' s.induction_on _ _
  · simp only [← filter_zero, ← nsmul_zero]
    
  · intro a ha ih
    rw [nsmul_cons, filter_add, ih, filter_cons, nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [← filter_eq_self, ← nsmul_zero, ← filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (mem_of_mem_nsmul hb)]
        
    

variable (p)

@[simp]
theorem filter_sub [DecidableEq α] (s t : Multiset α) : filter p (s - t) = filter p s - filter p t := by
  revert s
  refine'
    Multiset.induction_on t
      (by
        simp )
      fun a t IH s => _
  rw [sub_cons, IH]
  by_cases' p a
  · rw [filter_cons_of_pos _ h, sub_cons]
    congr
    by_cases' m : a ∈ s
    · rw [← cons_inj_right a, ← filter_cons_of_pos _ h, cons_erase (mem_filter_of_mem m h), cons_erase m]
      
    · rw [erase_of_not_mem m, erase_of_not_mem (mt mem_of_mem_filter m)]
      
    
  · rw [filter_cons_of_neg _ h]
    by_cases' m : a ∈ s
    · rw
        [(by
          rw [filter_cons_of_neg _ h] : filter p (erase s a) = filter p (a ::ₘ erase s a)),
        cons_erase m]
      
    · rw [erase_of_not_mem m]
      
    

@[simp]
theorem filter_union [DecidableEq α] (s t : Multiset α) : filter p (s ∪ t) = filter p s ∪ filter p t := by
  simp [← (· ∪ ·), ← union]

@[simp]
theorem filter_inter [DecidableEq α] (s t : Multiset α) : filter p (s ∩ t) = filter p s ∩ filter p t :=
  le_antisymmₓ (le_inter (filter_le_filter _ <| inter_le_left _ _) (filter_le_filter _ <| inter_le_right _ _)) <|
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun a h => of_mem_filter (mem_of_le (inter_le_left _ _) h)⟩

@[simp]
theorem filter_filter (q) [DecidablePred q] (s : Multiset α) : filter p (filter q s) = filter (fun a => p a ∧ q a) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_filter p q l

theorem filter_add_filter (q) [DecidablePred q] (s : Multiset α) :
    filter p s + filter q s = filter (fun a => p a ∨ q a) s + filter (fun a => p a ∧ q a) s :=
  (Multiset.induction_on s rfl) fun a s IH => by
    by_cases' p a <;> by_cases' q a <;> simp [*]

theorem filter_add_not (s : Multiset α) : filter p s + filter (fun a => ¬p a) s = s := by
  rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2] <;> simp [← Decidable.em]

theorem map_filter (f : β → α) (s : Multiset β) : filter p (map f s) = map f (filter (p ∘ f) s) :=
  Quot.induction_on s fun l => by
    simp [← map_filter]

/-! ### Simultaneously filter and map elements of a multiset -/


/-- `filter_map f s` is a combination filter/map operation on `s`.
  The function `f : α → option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filterMap (f : α → Option β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l => (filterMap f l : Multiset β)) fun l₁ l₂ h => Quot.sound <| h.filterMap f

@[simp]
theorem coe_filter_map (f : α → Option β) (l : List α) : filterMap f l = l.filterMap f :=
  rfl

@[simp]
theorem filter_map_zero (f : α → Option β) : filterMap f 0 = 0 :=
  rfl

@[simp]
theorem filter_map_cons_none {f : α → Option β} (a : α) (s : Multiset α) (h : f a = none) :
    filterMap f (a ::ₘ s) = filterMap f s :=
  (Quot.induction_on s) fun l => @congr_arg _ _ _ _ coe <| filter_map_cons_none a l h

@[simp]
theorem filter_map_cons_some (f : α → Option β) (a : α) (s : Multiset α) {b : β} (h : f a = some b) :
    filterMap f (a ::ₘ s) = b ::ₘ filterMap f s :=
  (Quot.induction_on s) fun l => @congr_arg _ _ _ _ coe <| filter_map_cons_some f a l h

theorem filter_map_eq_map (f : α → β) : filterMap (some ∘ f) = map f :=
  funext fun s => (Quot.induction_on s) fun l => @congr_arg _ _ _ _ coe <| congr_fun (filter_map_eq_map f) l

theorem filter_map_eq_filter : filterMap (Option.guard p) = filter p :=
  funext fun s => (Quot.induction_on s) fun l => @congr_arg _ _ _ _ coe <| congr_fun (filter_map_eq_filter p) l

theorem filter_map_filter_map (f : α → Option β) (g : β → Option γ) (s : Multiset α) :
    filterMap g (filterMap f s) = filterMap (fun x => (f x).bind g) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_map_filter_map f g l

theorem map_filter_map (f : α → Option β) (g : β → γ) (s : Multiset α) :
    map g (filterMap f s) = filterMap (fun x => (f x).map g) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| map_filter_map f g l

theorem filter_map_map (f : α → β) (g : β → Option γ) (s : Multiset α) : filterMap g (map f s) = filterMap (g ∘ f) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_map_map f g l

theorem filter_filter_map (f : α → Option β) (p : β → Prop) [DecidablePred p] (s : Multiset α) :
    filter p (filterMap f s) = filterMap (fun x => (f x).filter p) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_filter_map f p l

theorem filter_map_filter (f : α → Option β) (s : Multiset α) :
    filterMap f (filter p s) = filterMap (fun x => if p x then f x else none) s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_map_filter p f l

@[simp]
theorem filter_map_some (s : Multiset α) : filterMap some s = s :=
  (Quot.induction_on s) fun l => congr_arg coe <| filter_map_some l

@[simp]
theorem mem_filter_map (f : α → Option β) (s : Multiset α) {b : β} : b ∈ filterMap f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
  (Quot.induction_on s) fun l => mem_filter_map f l

theorem map_filter_map_of_inv (f : α → Option β) (g : β → α) (H : ∀ x : α, (f x).map g = some x) (s : Multiset α) :
    map g (filterMap f s) = s :=
  (Quot.induction_on s) fun l => congr_arg coe <| map_filter_map_of_inv f g H l

theorem filter_map_le_filter_map (f : α → Option β) {s t : Multiset α} (h : s ≤ t) : filterMap f s ≤ filterMap f t :=
  (le_induction_on h) fun l₁ l₂ h => (h.filterMap _).Subperm

/-! ### countp -/


/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp (s : Multiset α) : ℕ :=
  Quot.liftOn s (countp p) fun l₁ l₂ => Perm.countp_eq p

@[simp]
theorem coe_countp (l : List α) : countp p l = l.countp p :=
  rfl

@[simp]
theorem countp_zero : countp p 0 = 0 :=
  rfl

variable {p}

@[simp]
theorem countp_cons_of_pos {a : α} (s) : p a → countp p (a ::ₘ s) = countp p s + 1 :=
  Quot.induction_on s <| countp_cons_of_pos p

@[simp]
theorem countp_cons_of_neg {a : α} (s) : ¬p a → countp p (a ::ₘ s) = countp p s :=
  Quot.induction_on s <| countp_cons_of_neg p

variable (p)

theorem countp_cons (b : α) (s) : countp p (b ::ₘ s) = countp p s + if p b then 1 else 0 :=
  Quot.induction_on s <| by
    simp [← List.countp_cons]

theorem countp_eq_card_filter (s) : countp p s = card (filter p s) :=
  (Quot.induction_on s) fun l => l.countp_eq_length_filter p

theorem countp_le_card (s) : countp p s ≤ card s :=
  (Quot.induction_on s) fun l => countp_le_length p

@[simp]
theorem countp_add (s t) : countp p (s + t) = countp p s + countp p t := by
  simp [← countp_eq_card_filter]

@[simp]
theorem countp_nsmul (s) (n : ℕ) : countp p (n • s) = n * countp p s := by
  induction n <;> simp [*, ← succ_nsmul', ← succ_mul, ← zero_nsmul]

theorem card_eq_countp_add_countp (s) : card s = countp p s + countp (fun x => ¬p x) s :=
  (Quot.induction_on s) fun l => by
    simp [← l.length_eq_countp_add_countp p]

/-- `countp p`, the number of elements of a multiset satisfying `p`, promoted to an
`add_monoid_hom`. -/
def countpAddMonoidHom : Multiset α →+ ℕ where
  toFun := countp p
  map_zero' := countp_zero _
  map_add' := countp_add _

@[simp]
theorem coe_countp_add_monoid_hom : (countpAddMonoidHom p : Multiset α → ℕ) = countp p :=
  rfl

@[simp]
theorem countp_sub [DecidableEq α] {s t : Multiset α} (h : t ≤ s) : countp p (s - t) = countp p s - countp p t := by
  simp [← countp_eq_card_filter, ← h, ← filter_le_filter]

theorem countp_le_of_le {s t} (h : s ≤ t) : countp p s ≤ countp p t := by
  simpa [← countp_eq_card_filter] using card_le_of_le (filter_le_filter p h)

@[simp]
theorem countp_filter (q) [DecidablePred q] (s : Multiset α) : countp p (filter q s) = countp (fun a => p a ∧ q a) s :=
  by
  simp [← countp_eq_card_filter]

theorem countp_eq_countp_filter_add (s) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    countp p s = (filter q s).countp p + (filter (fun a => ¬q a) s).countp p :=
  (Quot.induction_on s) fun l => l.countp_eq_countp_filter_add _ _

@[simp]
theorem countp_true {s : Multiset α} : countp (fun _ => True) s = card s :=
  (Quot.induction_on s) fun l => List.countp_true

@[simp]
theorem countp_false {s : Multiset α} : countp (fun _ => False) s = 0 :=
  (Quot.induction_on s) fun l => List.countp_false

theorem countp_map (f : α → β) (s : Multiset α) (p : β → Prop) [DecidablePred p] :
    countp p (map f s) = (s.filter fun a => p (f a)).card := by
  refine' Multiset.induction_on s _ fun a t IH => _
  · rw [map_zero, countp_zero, filter_zero, card_zero]
    
  · rw [map_cons, countp_cons, IH, filter_cons, card_add, apply_ite card, card_zero, card_singleton, add_commₓ]
    

variable {p}

theorem countp_pos {s} : 0 < countp p s ↔ ∃ a ∈ s, p a :=
  (Quot.induction_on s) fun l => List.countp_pos p

theorem countp_eq_zero {s} : countp p s = 0 ↔ ∀, ∀ a ∈ s, ∀, ¬p a :=
  (Quot.induction_on s) fun l => List.countp_eq_zero p

theorem countp_eq_card {s} : countp p s = card s ↔ ∀, ∀ a ∈ s, ∀, p a :=
  (Quot.induction_on s) fun l => List.countp_eq_length p

theorem countp_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
  countp_pos.2 ⟨_, h, pa⟩

theorem countp_congr {s s' : Multiset α} (hs : s = s') {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀, ∀ x ∈ s, ∀, p x = p' x) : s.countp p = s'.countp p' :=
  Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [← quot_mk_to_coe'', ← coe_eq_coe] at hs
      exact hs.countp_congr hp)
    hs hp

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α]

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : Multiset α → ℕ :=
  countp (Eq a)

@[simp]
theorem coe_count (a : α) (l : List α) : count a ↑l = l.count a :=
  coe_countp _ _

@[simp]
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl

@[simp]
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = succ (count a s) :=
  countp_cons_of_pos _ rfl

@[simp]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
  countp_cons_of_neg _ h

theorem count_le_card (a : α) (s) : count a s ≤ card s :=
  countp_le_card _ _

theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
  countp_le_of_le _

theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)

theorem count_cons (a b : α) (s : Multiset α) : count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countp_cons _ _ _

@[simp]
theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 := by
  simp only [← count_cons_self, ← singleton_eq_cons, ← eq_self_iff_true, ← count_zero]

theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [← count_cons, ← singleton_eq_cons, ← count_zero, ← zero_addₓ]

@[simp]
theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
  countp_add _

/-- `count a`, the multiplicity of `a` in a multiset, promoted to an `add_monoid_hom`. -/
def countAddMonoidHom (a : α) : Multiset α →+ ℕ :=
  countpAddMonoidHom (Eq a)

@[simp]
theorem coe_count_add_monoid_hom {a : α} : (countAddMonoidHom a : Multiset α → ℕ) = count a :=
  rfl

@[simp]
theorem count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, ← succ_nsmul', ← succ_mul, ← zero_nsmul]

theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a ∈ s := by
  simp [← count, ← countp_pos]

theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 ≤ count a s ↔ a ∈ s := by
  rw [succ_le_iff, count_pos]

@[simp]
theorem count_eq_zero_of_not_mem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
  by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zeroₓ h')

@[simp]
theorem count_eq_zero {a : α} {s : Multiset α} : count a s = 0 ↔ a ∉ s :=
  iff_not_comm.1 <| count_pos.symm.trans pos_iff_ne_zero

theorem count_ne_zero {a : α} {s : Multiset α} : count a s ≠ 0 ↔ a ∈ s := by
  simp [← Ne.def, ← count_eq_zero]

theorem count_eq_card {a : α} {s} : count a s = card s ↔ ∀, ∀ x ∈ s, ∀, a = x :=
  countp_eq_card

@[simp]
theorem count_repeat_self (a : α) (n : ℕ) : count a (repeat a n) = n := by
  simp [← repeat]

theorem count_repeat (a b : α) (n : ℕ) : count a (repeat b n) = if a = b then n else 0 := by
  split_ifs with h₁
  · rw [h₁, count_repeat_self]
    
  · rw [count_eq_zero]
    apply mt eq_of_mem_repeat h₁
    

@[simp]
theorem count_erase_self (a : α) (s : Multiset α) : count a (erase s a) = pred (count a s) := by
  by_cases' a ∈ s
  · rw
        [(by
          rw [cons_erase h] : count a s = count a (a ::ₘ erase s a)),
        count_cons_self] <;>
      rfl
    
  · rw [erase_of_not_mem h, count_eq_zero.2 h] <;> rfl
    

@[simp]
theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : Multiset α) : count a (erase s b) = count a s := by
  by_cases' b ∈ s
  · rw [← count_cons_of_ne ab, cons_erase h]
    
  · rw [erase_of_not_mem h]
    

@[simp]
theorem count_sub (a : α) (s t : Multiset α) : count a (s - t) = count a s - count a t := by
  revert s
  refine'
    Multiset.induction_on t
      (by
        simp )
      fun b t IH s => _
  rw [sub_cons, IH]
  by_cases' ab : a = b
  · subst b
    rw [count_erase_self, count_cons_self, sub_succ, pred_sub]
    
  · rw [count_erase_of_ne ab, count_cons_of_ne ab]
    

@[simp]
theorem count_union (a : α) (s t : Multiset α) : count a (s ∪ t) = max (count a s) (count a t) := by
  simp [← (· ∪ ·), ← union, ← tsub_add_eq_max, -add_commₓ]

@[simp]
theorem count_inter (a : α) (s t : Multiset α) : count a (s ∩ t) = min (count a s) (count a t) := by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add, sub_add_inter, count_sub, tsub_add_min]

theorem le_count_iff_repeat_le {a : α} {s : Multiset α} {n : ℕ} : n ≤ count a s ↔ repeat a n ≤ s :=
  (Quot.induction_on s) fun l => le_count_iff_repeat_sublist.trans repeat_le_coe.symm

@[simp]
theorem count_filter_of_pos {p} [DecidablePred p] {a} {s : Multiset α} (h : p a) : count a (filter p s) = count a s :=
  (Quot.induction_on s) fun l => count_filter h

@[simp]
theorem count_filter_of_neg {p} [DecidablePred p] {a} {s : Multiset α} (h : ¬p a) : count a (filter p s) = 0 :=
  Multiset.count_eq_zero_of_not_mem fun t => h (of_mem_filter t)

theorem count_filter {p} [DecidablePred p] {a} {s : Multiset α} : count a (filter p s) = if p a then count a s else 0 :=
  by
  split_ifs with h
  · exact count_filter_of_pos h
    
  · exact count_filter_of_neg h
    

theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
  (Quotientₓ.induction_on₂ s t) fun l₁ l₂ => Quotientₓ.eq.trans perm_iff_count

@[ext]
theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
  ext.2

@[simp]
theorem coe_inter (s t : List α) : (s ∩ t : Multiset α) = (s.bagInter t : List α) := by
  ext <;> simp

theorem le_iff_count {s t : Multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
  ⟨fun h a => count_le_of_le a h, fun al => by
    rw [←
        (ext.2 fun a => by
          simp [← max_eq_rightₓ (al a)] :
          s ∪ t = t)] <;>
      apply le_union_left⟩

instance : DistribLattice (Multiset α) :=
  { Multiset.lattice with
    le_sup_inf := fun s t u =>
      le_of_eqₓ <|
        Eq.symm <|
          ext.2 fun a => by
            simp only [← max_min_distrib_left, ← Multiset.count_inter, ← Multiset.sup_eq_union, ← Multiset.count_union,
              ← Multiset.inf_eq_inter] }

theorem repeat_inf (s : Multiset α) (a : α) (n : ℕ) : repeat a n⊓s = repeat a (min (s.count a) n) := by
  ext x
  rw [inf_eq_inter, count_inter, count_repeat, count_repeat]
  by_cases' x = a
  simp only [← min_commₓ, ← h, ← if_true, ← eq_self_iff_true]
  simp only [← h, ← if_false, ← zero_min]

theorem count_map {α β : Type _} (f : α → β) (s : Multiset α) [DecidableEq β] (b : β) :
    count b (map f s) = (s.filter fun a => b = f a).card :=
  countp_map _ _ _

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∈ » s)
/-- `multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
theorem count_map_eq_count [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Set.InjOn f { x : α | x ∈ s }) (x)
    (_ : x ∈ s) : (s.map f).count (f x) = s.count x := by
  suffices (filter (fun a : α => f x = f a) s).count x = card (filter (fun a : α => f x = f a) s) by
    rw [count, countp_map, ← this]
    exact count_filter_of_pos rfl
  · rw [eq_repeat.2 ⟨rfl, fun b hb => eq_comm.1 ((hf H (mem_filter.1 hb).left) (mem_filter.1 hb).right)⟩]
    simp only [← count_repeat, ← eq_self_iff_true, ← if_true, ← card_repeat]
    

/-- `multiset.map f` preserves `count` if `f` is injective -/
theorem count_map_eq_count' [DecidableEq β] (f : α → β) (s : Multiset α) (hf : Function.Injective f) (x : α) :
    (s.map f).count (f x) = s.count x := by
  by_cases' H : x ∈ s
  · exact count_map_eq_count f _ (Set.inj_on_of_injective hf _) _ H
    
  · rw [count_eq_zero_of_not_mem H, count_eq_zero, mem_map]
    rintro ⟨k, hks, hkx⟩
    rw [hf hkx] at *
    contradiction
    

theorem filter_eq' (s : Multiset α) (b : α) : s.filter (· = b) = repeat b (count b s) := by
  ext a
  rw [count_repeat, count_filter]
  exact if_ctx_congr Iff.rfl (fun h => congr_arg _ h) fun h => rfl

theorem filter_eq (s : Multiset α) (b : α) : s.filter (Eq b) = repeat b (count b s) := by
  simp_rw [← filter_eq', eq_comm]

@[simp]
theorem repeat_inter (x : α) (n : ℕ) (s : Multiset α) : repeat x n ∩ s = repeat x (min n (s.count x)) := by
  refine' le_antisymmₓ _ _
  · simp only [← le_iff_count, ← count_inter, ← count_repeat]
    intro a
    split_ifs with h
    · rw [h]
      
    · rw [Nat.zero_minₓ]
      
    
  simp only [← le_inter_iff, le_count_iff_repeat_le, ← count_inter, ← count_repeat_self]

@[simp]
theorem inter_repeat (s : Multiset α) (x : α) (n : ℕ) : s ∩ repeat x n = repeat x (min (s.count x) n) := by
  rw [inter_comm, repeat_inter, min_commₓ]

end

section Embedding

@[simp]
theorem map_le_map_iff {f : α → β} (hf : Function.Injective f) {s t : Multiset α} : s.map f ≤ t.map f ↔ s ≤ t := by
  classical
  refine' ⟨fun h => le_iff_count.mpr fun a => _, map_le_map⟩
  simpa [← count_map_eq_count' f _ hf] using le_iff_count.mp h (f a)

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a multiset to its
image under `f`. -/
@[simps]
def mapEmbedding (f : α ↪ β) : Multiset α ↪o Multiset β :=
  OrderEmbedding.ofMapLeIff (map f) fun _ _ => map_le_map_iff f.inj'

end Embedding

theorem count_eq_card_filter_eq [DecidableEq α] (s : Multiset α) (a : α) : s.count a = (s.filter (Eq a)).card := by
  rw [count, countp_eq_card_filter]

/-- Mapping a multiset through a predicate and counting the `true`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `classical.dec_eq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp]
theorem map_count_true_eq_filter_card (s : Multiset α) (p : α → Prop) [DecidablePred p] :
    (s.map p).count True = (s.filter p).card := by
  simp only [← count_eq_card_filter_eq, ← map_filter, ← card_map, ← Function.comp.left_id, ← eq_true_eq_id]

/-! ### Lift a relation to `multiset`s -/


section Rel

/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
@[mk_iff]
inductive Rel (r : α → β → Prop) : Multiset α → Multiset β → Prop
  | zero : rel 0 0
  | cons {a b as bs} : r a b → rel as bs → rel (a ::ₘ as) (b ::ₘ bs)

variable {δ : Type _} {r : α → β → Prop} {p : γ → δ → Prop}

private theorem rel_flip_aux {s t} (h : Rel r s t) : Rel (flip r) t s :=
  Rel.rec_on h Rel.zero fun _ _ _ _ h₀ h₁ ih => Rel.cons h₀ ih

theorem rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s :=
  ⟨rel_flip_aux, rel_flip_aux⟩

theorem rel_refl_of_refl_on {m : Multiset α} {r : α → α → Prop} : (∀, ∀ x ∈ m, ∀, r x x) → Rel r m m := by
  apply m.induction_on
  · intros
    apply rel.zero
    
  · intro a m ih h
    exact rel.cons (h _ (mem_cons_self _ _)) (ih fun _ ha => h _ (mem_cons_of_mem ha))
    

theorem rel_eq_refl {s : Multiset α} : Rel (· = ·) s s :=
  rel_refl_of_refl_on fun x hx => rfl

theorem rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t := by
  constructor
  · intro h
    induction h <;> simp [*]
    
  · intro h
    subst h
    exact rel_eq_refl
    

theorem Rel.mono {r p : α → β → Prop} {s t} (hst : Rel r s t) (h : ∀, ∀ a ∈ s, ∀, ∀ b ∈ t, ∀, r a b → p a b) :
    Rel p s t := by
  induction hst
  case rel.zero =>
    exact rel.zero
  case rel.cons a b s t hab hst ih =>
    apply rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab)
    exact ih fun a' ha' b' hb' h' => h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h'

theorem Rel.add {s t u v} (hst : Rel r s t) (huv : Rel r u v) : Rel r (s + u) (t + v) := by
  induction hst
  case rel.zero =>
    simpa using huv
  case rel.cons a b s t hab hst ih =>
    simpa using ih.cons hab

theorem rel_flip_eq {s t : Multiset α} : Rel (fun a b => b = a) s t ↔ s = t :=
  show Rel (flip (· = ·)) s t ↔ s = t by
    rw [rel_flip, rel_eq, eq_comm]

@[simp]
theorem rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b = 0 := by
  rw [rel_iff] <;> simp

@[simp]
theorem rel_zero_right {a : Multiset α} : Rel r a 0 ↔ a = 0 := by
  rw [rel_iff] <;> simp

theorem rel_cons_left {a as bs} : Rel r (a ::ₘ as) bs ↔ ∃ b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs' := by
  constructor
  · generalize hm : a ::ₘ as = m
    intro h
    induction h generalizing as
    case rel.zero =>
      simp at hm
      contradiction
    case rel.cons a' b as' bs ha'b h ih =>
      rcases cons_eq_cons.1 hm with (⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩)
      · subst eq₁
        subst eq₂
        exact ⟨b, bs, ha'b, h, rfl⟩
        
      · rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ rel.cons ha'b h₂, Eq.symm ▸ cons_swap _ _ _⟩
        
    
  · exact fun ⟨b, bs', hab, h, Eq⟩ => Eq.symm ▸ rel.cons hab h
    

theorem rel_cons_right {as b bs} : Rel r as (b ::ₘ bs) ↔ ∃ a as', r a b ∧ Rel r as' bs ∧ as = a ::ₘ as' := by
  rw [← rel_flip, rel_cons_left]
  refine' exists₂_congrₓ fun a as' => _
  rw [rel_flip, flip]

theorem rel_add_left {as₀ as₁} :
    ∀ {bs}, Rel r (as₀ + as₁) bs ↔ ∃ bs₀ bs₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ bs = bs₀ + bs₁ :=
  Multiset.induction_on as₀
    (by
      simp )
    (by
      intro a s ih bs
      simp only [← ih, ← cons_add, ← rel_cons_left]
      constructor
      · intro h
        rcases h with ⟨b, bs', hab, h, rfl⟩
        rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩
        exact
          ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by
            simp ⟩
        
      · intro h
        rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩
        rcases h with ⟨b, bs, hab, h₀, rfl⟩
        exact
          ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by
            simp ⟩
        )

theorem rel_add_right {as bs₀ bs₁} : Rel r as (bs₀ + bs₁) ↔ ∃ as₀ as₁, Rel r as₀ bs₀ ∧ Rel r as₁ bs₁ ∧ as = as₀ + as₁ :=
  by
  rw [← rel_flip, rel_add_left] <;> simp [← rel_flip]

theorem rel_map_left {s : Multiset γ} {f : γ → α} : ∀ {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  Multiset.induction_on s
    (by
      simp )
    (by
      simp (config := { contextual := true })[← rel_cons_left])

theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ → β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip, rel_map_left, ← rel_flip] <;> rfl

theorem rel_map {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right

theorem card_eq_card_of_rel {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) : card s = card t := by
  induction h <;> simp [*]

theorem exists_mem_of_rel_of_mem {r : α → β → Prop} {s : Multiset α} {t : Multiset β} (h : Rel r s t) :
    ∀ {a : α} (ha : a ∈ s), ∃ b ∈ t, r a b := by
  induction' h with x y s t hxy hst ih
  · simp
    
  · intro a ha
    cases' mem_cons.1 ha with ha ha
    · exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩
      
    · rcases ih ha with ⟨b, hbt, hab⟩
      exact ⟨b, mem_cons.2 (Or.inr hbt), hab⟩
      
    

theorem rel_of_forall {m1 m2 : Multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
    (hc : card m1 = card m2) : m1.Rel r m2 := by
  revert m1
  apply m2.induction_on
  · intro m h hc
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero]
    
  · intro a t ih m h hc
    rw [card_cons] at hc
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m from hc.symm ▸ Nat.succ_posₓ _)
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb
    refine' rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih _ _, rfl⟩
    · exact fun _ _ ha hb => h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb)
      
    · simpa using hc
      
    

theorem rel_repeat_left {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    (repeat a n).Rel r m ↔ m.card = n ∧ ∀ x, x ∈ m → r a x :=
  ⟨fun h =>
    ⟨(card_eq_card_of_rel h).symm.trans (card_repeat _ _), fun x hx => by
      obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx
      rwa [eq_of_mem_repeat hb1] at hb2⟩,
    fun h =>
    rel_of_forall (fun x y hx hy => (eq_of_mem_repeat hx).symm ▸ h.2 _ hy) (Eq.trans (card_repeat _ _) h.1.symm)⟩

theorem rel_repeat_right {m : Multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
    m.Rel r (repeat a n) ↔ m.card = n ∧ ∀ x, x ∈ m → r x a := by
  rw [← rel_flip]
  exact rel_repeat_left

theorem Rel.trans (r : α → α → Prop) [IsTrans α r] {s t u : Multiset α} (r1 : Rel r s t) (r2 : Rel r t u) : Rel r s u :=
  by
  induction' t using Multiset.induction_on with x t ih generalizing s u
  · rw [rel_zero_right.mp r1, rel_zero_left.mp r2, rel_zero_left]
    
  · obtain ⟨a, as, ha1, ha2, rfl⟩ := rel_cons_right.mp r1
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp r2
    exact Multiset.Rel.cons (trans ha1 hb1) (ih ha2 hb2)
    

theorem Rel.countp_eq (r : α → α → Prop) [IsTrans α r] [IsSymm α r] {s t : Multiset α} (x : α) [DecidablePred (r x)]
    (h : Rel r s t) : countp (r x) s = countp (r x) t := by
  induction' s using Multiset.induction_on with y s ih generalizing t
  · rw [rel_zero_left.mp h]
    
  · obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countp_cons, countp_cons, ih hb2]
    exact congr_arg _ (if_congr ⟨fun h => trans h hb1, fun h => trans h (symm hb1)⟩ rfl rfl)
    

end Rel

section Map

theorem map_eq_map {f : α → β} (hf : Function.Injective f) {s t : Multiset α} : s.map f = t.map f ↔ s = t := by
  rw [← rel_eq, ← rel_eq, rel_map]
  simp only [← hf.eq_iff]

theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (Multiset.map f) := fun x y =>
  (map_eq_map hf).1

end Map

section Quot

theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  (Rel.rec_on hst rfl) fun a b s t hab hst ih => by
    simp [← ih, ← Quot.sound hab]

theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : Multiset (Quot r)) :
    ∃ t : Multiset α, s = t.map (Quot.mk r) :=
  (Multiset.induction_on s ⟨0, rfl⟩) fun a s ⟨t, ht⟩ =>
    (Quot.induction_on a) fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot {r : α → α → Prop} {p : Multiset (Quot r) → Prop} (s : Multiset (Quot r)) :
    (∀ s : Multiset α, p (s.map (Quot.mk r))) → p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨t, rfl⟩ => fun h => h _

end Quot

/-! ### Disjoint multisets -/


/-- `disjoint s t` means that `s` and `t` have no elements in common. -/
def Disjoint (s t : Multiset α) : Prop :=
  ∀ ⦃a⦄, a ∈ s → a ∈ t → False

@[simp]
theorem coe_disjoint (l₁ l₂ : List α) : @Disjoint α l₁ l₂ ↔ l₁.Disjoint l₂ :=
  Iff.rfl

theorem Disjoint.symm {s t : Multiset α} (d : Disjoint s t) : Disjoint t s
  | a, i₂, i₁ => d i₁ i₂

theorem disjoint_comm {s t : Multiset α} : Disjoint s t ↔ Disjoint t s :=
  ⟨Disjoint.symm, Disjoint.symm⟩

theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
  Iff.rfl

theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  disjoint_comm

theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ ∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ t, ∀, a ≠ b := by
  simp [← disjoint_left, ← imp_not_comm]

theorem disjoint_of_subset_left {s t u : Multiset α} (h : s ⊆ u) (d : Disjoint u t) : Disjoint s t
  | x, m₁ => d (h m₁)

theorem disjoint_of_subset_right {s t u : Multiset α} (h : t ⊆ u) (d : Disjoint s u) : Disjoint s t
  | x, m, m₁ => d m (h m₁)

theorem disjoint_of_le_left {s t u : Multiset α} (h : s ≤ u) : Disjoint u t → Disjoint s t :=
  disjoint_of_subset_left (subset_of_le h)

theorem disjoint_of_le_right {s t u : Multiset α} (h : t ≤ u) : Disjoint s u → Disjoint s t :=
  disjoint_of_subset_right (subset_of_le h)

@[simp]
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l
  | a => (not_mem_nilₓ a).elim

@[simp]
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [← Disjoint] <;> rfl

@[simp]
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [disjoint_comm, singleton_disjoint]

@[simp]
theorem disjoint_add_left {s t u : Multiset α} : Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u := by
  simp [← Disjoint, ← or_imp_distrib, ← forall_and_distrib]

@[simp]
theorem disjoint_add_right {s t u : Multiset α} : Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [disjoint_comm, disjoint_add_left] <;> tauto

@[simp]
theorem disjoint_cons_left {a : α} {s t : Multiset α} : Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
  (@disjoint_add_left _ {a} s t).trans <| by
    rw [singleton_disjoint]

@[simp]
theorem disjoint_cons_right {a : α} {s t : Multiset α} : Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [disjoint_comm, disjoint_cons_left] <;> tauto

theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} : s ∩ t = 0 ↔ Disjoint s t := by
  rw [← subset_zero] <;> simp [← subset_iff, ← Disjoint]

@[simp]
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=
  by
  simp [← Disjoint, ← or_imp_distrib, ← forall_and_distrib]

@[simp]
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u :=
  by
  simp [← Disjoint, ← or_imp_distrib, ← forall_and_distrib]

theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} : s + t = s ∪ t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero, Nat.min_eq_zero_iff,
    Nat.add_eq_max_iff]

theorem disjoint_map_map {f : α → γ} {g : β → γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ ∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ t, ∀, f a ≠ g b := by
  simp [← Disjoint, ← @eq_comm _ (f _) (g _)]
  rfl

/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def Pairwise (r : α → α → Prop) (m : Multiset α) : Prop :=
  ∃ l : List α, m = l ∧ l.Pairwise r

theorem pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : Symmetric r) {l : List α} :
    Multiset.Pairwise r l ↔ l.Pairwise r :=
  Iff.intro (fun ⟨l', Eq, h⟩ => ((Quotientₓ.exact Eq).pairwise_iff hr).2 h) fun h => ⟨l, rfl, h⟩

end Multiset

namespace Multiset

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose_x p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def chooseX : ∀ hp : ∃! a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a } :=
  Quotientₓ.recOn l (fun l' ex_unique => List.chooseX p l' (exists_of_exists_unique ex_unique))
    (by
      intros
      funext hp
      suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y
      · apply all_equal
        
      · rintro ⟨x, px⟩ ⟨y, py⟩
        rcases hp with ⟨z, ⟨z_mem_l, pz⟩, z_unique⟩
        congr
        calc x = z := z_unique x px _ = y := (z_unique y py).symm
        )

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

variable (α)

/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α where
  toFun := coe
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) => (List.ext_le h.length_eq) fun n h₁ h₂ => Subsingleton.elimₓ _ _
  left_inv := fun l => rfl
  right_inv := fun m => (Quot.induction_on m) fun l => rfl

variable {α}

@[simp]
theorem coe_subsingleton_equiv [Subsingleton α] : (subsingletonEquiv α : List α → Multiset α) = coe :=
  rfl

end Multiset

